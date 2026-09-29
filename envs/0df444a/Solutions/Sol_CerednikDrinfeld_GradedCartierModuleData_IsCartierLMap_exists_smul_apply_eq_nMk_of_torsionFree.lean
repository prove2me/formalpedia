-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.IsCartierLMap.exists_smul_apply_eq_nMk_of_torsionFree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/229fe4d9-fb18-55f3-887e-6838bc46af5a

import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_lambda_injective_of_isHomogeneousVBasis_of_torsionFree
import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_exists_smul_apply_eq_nMk_of_torsionFree

set_option autoImplicit false

open CerednikDrinfeld

namespace E0Up

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData WittVector

section Witt

variable (p : ℕ) [hp : Fact p.Prime]

private theorem frobenius_teichmuller_aux₁ {R : Type} (x : MvPolynomial R ℚ) :
    frobenius (teichmuller p x) = teichmuller p (x ^ p) := by
  apply (ghostMap.bijective_of_invertible p (MvPolynomial R ℚ)).1
  funext n
  rw [ghostMap_apply, ghostMap_apply, ghostComponent_frobenius, ghostComponent_teichmuller,
    ghostComponent_teichmuller, ← pow_mul, ← pow_succ']

private theorem frobenius_teichmuller_aux₂ {R : Type} (x : MvPolynomial R ℤ) :
    frobenius (teichmuller p x) = teichmuller p (x ^ p) := by
  refine map_injective (MvPolynomial.map (Int.castRingHom ℚ))
    (MvPolynomial.map_injective _ Int.cast_injective) ?_
  rw [WittVector.IsPoly.map (WittVector.frobenius_isPoly p), map_teichmuller, map_teichmuller, map_pow,
    frobenius_teichmuller_aux₁]

theorem frobenius_teichmuller {S : Type} [CommRing S] (a : S) :
    frobenius (teichmuller p a) = teichmuller p (a ^ p) := by
  obtain ⟨x, rfl⟩ := MvPolynomial.counit_surjective S a
  rw [← map_teichmuller, ← WittVector.IsPoly.map (WittVector.frobenius_isPoly p), frobenius_teichmuller_aux₂,
    map_teichmuller, map_pow]

theorem exists_natCast_eq_teichmuller_add_verschiebung {S : Type} [CommRing S] :
    ∃ ε : WittVector p S, ((p : ℕ) : WittVector p S) = teichmuller p (p : S) + verschiebung ε := by
  have h0 : (((p : ℕ) : WittVector p S) - teichmuller p (p : S)).coeff 0 = 0 := by
    have := add_coeff_zero (teichmuller p (p : S)) (((p : ℕ) : WittVector p S) - teichmuller p (p : S))
    rw [add_sub_cancel, teichmuller_coeff_zero, ← constantCoeff_apply, map_natCast] at this
    exact left_eq_add.mp this
  refine ⟨(((p : ℕ) : WittVector p S) - teichmuller p (p : S)).shift 1, ?_⟩
  have := eq_iterate_verschiebung (x := ((p : ℕ) : WittVector p S) - teichmuller p (p : S)) (n := 1)
    (by intro i hi; interval_cases i; exact h0)
  rw [Function.iterate_one] at this
  rw [← this, add_sub_cancel]

end Witt

section Datum

variable {p : ℕ} [Fact p.Prime] {S : Type} [CommRing S] {jS : Zp2 p →+* S}

theorem fin2_add_one_add_one : ∀ i : Fin 2, i + 1 + 1 = i := by decide

theorem fin2_add_one_ne : ∀ i : Fin 2, i + 1 ≠ i := by decide

theorem sum_univ_fin2 {M : Type} [AddCommMonoid M] (l : Fin 2) (f : Fin 2 → M) :
    ∑ i : Fin 2, f i = f l + f (l + 1) := by
  fin_cases l
  · simp [Fin.sum_univ_two]
  · simp [Fin.sum_univ_two, add_comm]

theorem isCompl_piece_succ (D : GradedCartierModuleData p S jS) (i : Fin 2) :
    IsCompl (D.piece i) (D.piece (i + 1)) := by
  fin_cases i
  · exact D.isCompl_piece
  · exact D.isCompl_piece.symm

theorem exists_piece_decomp (D : GradedCartierModuleData p S jS) (i : Fin 2) (m : D.M) :
    ∃ m₀ m₁ : D.M, m₀ ∈ D.piece i ∧ m₁ ∈ D.piece (i + 1) ∧ m = m₀ + m₁ := by
  have hm : m ∈ D.piece i ⊔ D.piece (i + 1) := by
    rw [(isCompl_piece_succ D i).sup_eq_top]; exact Submodule.mem_top
  obtain ⟨m₀, h₀, m₁, h₁, h⟩ := Submodule.mem_sup.mp hm
  exact ⟨m₀, m₁, h₀, h₁, h.symm⟩

theorem eq_zero_of_mem_piece_of_mem_piece_succ (D : GradedCartierModuleData p S jS) (i : Fin 2) (m : D.M)
    (h₀ : m ∈ D.piece i) (h₁ : m ∈ D.piece (i + 1)) : m = 0 :=
  (Submodule.disjoint_def.mp (isCompl_piece_succ D i).disjoint) m h₀ h₁

theorem exists_eq_teichmuller_smul_add_verschiebung (D : GradedCartierModuleData p S jS) {γ : Fin 2 → D.M}
    (hγ : D.IsHomogeneousVBasis γ) (l : Fin 2) (m : D.M) (hm : m ∈ D.piece l) :
    ∃ (c : S) (y : D.M), y ∈ D.piece (l + 1) ∧ m = teichmuller p c • γ l + D.verschiebung y := by
  obtain ⟨⟨c, y⟩, hcy, -⟩ := hγ.2 m
  obtain ⟨y₀, y₁, hy₀, hy₁, rfl⟩ := exists_piece_decomp D l y
  simp only at hcy
  rw [sum_univ_fin2 l, map_add] at hcy

  have hA : teichmuller p (c (l + 1)) • γ (l + 1) + D.verschiebung y₀ ∈ D.piece (l + 1) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 (l + 1))) (D.verschiebung_mem l y₀ hy₀)
  have hB : teichmuller p (c l) • γ l + D.verschiebung y₁ ∈ D.piece l := by
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 l)) ?_
    have := D.verschiebung_mem (l + 1) y₁ hy₁
    rwa [fin2_add_one_add_one] at this
  have hA' : teichmuller p (c (l + 1)) • γ (l + 1) + D.verschiebung y₀ ∈ D.piece l := by
    have : teichmuller p (c (l + 1)) • γ (l + 1) + D.verschiebung y₀ =
        m - (teichmuller p (c l) • γ l + D.verschiebung y₁) := by rw [hcy]; abel
    rw [this]
    exact Submodule.sub_mem _ hm hB
  have hA0 := eq_zero_of_mem_piece_of_mem_piece_succ D l _ hA' hA
  refine ⟨c l, y₁, hy₁, ?_⟩
  calc m = (teichmuller p (c l) • γ l + D.verschiebung y₁) +
        (teichmuller p (c (l + 1)) • γ (l + 1) + D.verschiebung y₀) := by rw [hcy]; abel
    _ = teichmuller p (c l) • γ l + D.verschiebung y₁ := by rw [hA0, add_zero]

theorem teichmuller_smul_add_verschiebung_inj (D : GradedCartierModuleData p S jS) {γ : Fin 2 → D.M}
    (hγ : D.IsHomogeneousVBasis γ) (l : Fin 2) {c c' : S} {y y' : D.M}
    (h : teichmuller p c • γ l + D.verschiebung y = teichmuller p c' • γ l + D.verschiebung y') :
    c = c' ∧ y = y' := by
  obtain ⟨cy, -, huniq⟩ := hγ.2 (teichmuller p c • γ l + D.verschiebung y)
  have e : ∀ (c₀ : S) (y₀ : D.M), teichmuller p c₀ • γ l + D.verschiebung y₀ =
      (∑ i : Fin 2, teichmuller p (Function.update (fun _ : Fin 2 => (0 : S)) l c₀ i) • γ i) + D.verschiebung y₀ := by
    intro c₀ y₀
    rw [sum_univ_fin2 l, Function.update_self, Function.update_of_ne (fin2_add_one_ne l)]
    simp [map_zero]
  have h1 := huniq (Function.update (fun _ : Fin 2 => (0 : S)) l c, y) (e c y)
  have h2 := huniq (Function.update (fun _ : Fin 2 => (0 : S)) l c', y') (h.trans (e c' y'))
  have h12 := h1.trans h2.symm
  refine ⟨?_, congrArg Prod.snd h12⟩
  have := congrArg (fun q => q.1 l) h12
  simpa using this

end Datum

end E0Up

theorem solution
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] (jS : Zp2 p →+* S)
    (hS : ∀ s : S, (p : S) * s = 0 → s = 0)
    (D : GradedCartierModuleData p S jS) (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L) (i : Fin 2) :
    ∃ (a d : S) (x u v u' m : D.M) (ε : WittVector p S),
      D.varpi (γ i) = WittVector.teichmuller p a • γ (i + 1) + D.verschiebung x ∧
      ((p : ℕ) : WittVector p S) = WittVector.teichmuller p (p : S) + WittVector.verschiebung ε ∧
      ε • L (γ i) = D.nMk (x + u, v) ∧
      u = WittVector.teichmuller p (a ^ (p - 1) * d) • γ i + D.verschiebung u' ∧
      D.varpi u + D.verschiebung v = WittVector.teichmuller p a • m := by
  have h11 := E0Up.fin2_add_one_add_one i

  obtain ⟨a, x, hx, hPiI⟩ :=
    E0Up.exists_eq_teichmuller_smul_add_verschiebung D hγ (i + 1) (D.varpi (γ i)) (D.varpi_mem i _ (hγ.1 i))
  rw [h11] at hx
  obtain ⟨a', x', hx', hPiS⟩ :=
    E0Up.exists_eq_teichmuller_smul_add_verschiebung D hγ (i + 1 + 1) (D.varpi (γ (i + 1)))
      (D.varpi_mem (i + 1) _ (hγ.1 (i + 1)))
  rw [h11] at hPiS hx'

  obtain ⟨ε, hε⟩ := E0Up.exists_natCast_eq_teichmuller_add_verschiebung p (S := S)

  have exp1 : D.varpi (D.varpi (γ i)) =
      WittVector.teichmuller p (a * a') • γ i +
        D.verschiebung (WittVector.frobenius (WittVector.teichmuller p a) • x' + D.varpi x) := by
    rw [hPiI, map_add, map_smul, hPiS, D.varpi_verschiebung, smul_add, D.smul_verschiebung, smul_smul,
      ← map_mul, map_add, add_assoc]
  have exp2 : D.varpi (D.varpi (γ i)) =
      WittVector.teichmuller p (p : S) • γ i + D.verschiebung (ε • D.frobenius (γ i)) := by
    rw [D.varpi_varpi, ← Nat.cast_smul_eq_nsmul (WittVector p S), hε, add_smul,
      D.verschiebung_smul_frobenius]
  obtain ⟨haa', hV⟩ := E0Up.teichmuller_smul_add_verschiebung_inj D hγ i (exp1.symm.trans exp2)

  have hreg : ∀ s : S, a * s = 0 → s = 0 := fun s hs => hS s (by
    rw [← haa', mul_comm a a', mul_assoc, hs, mul_zero])
  have hlam : D.lambda (ε • L (γ i) - D.nMk (x, 0)) = WittVector.frobenius (WittVector.teichmuller p a) • x' := by
    rw [map_sub, map_smul, hL.lambda_comp, CerednikDrinfeld.GradedCartierModuleData.lambda_nMk, map_zero, add_zero, ← hV, add_sub_cancel_right]
  obtain ⟨⟨n, n'⟩, hnn⟩ := D.nMk_surjective (ε • L (γ i) - D.nMk (x, 0))
  obtain ⟨u, n₁, hu, hn₁, rfl⟩ := E0Up.exists_piece_decomp D i n
  obtain ⟨v, n₁', hv, hn₁', rfl⟩ := E0Up.exists_piece_decomp D i n'
  have hsplit : WittVector.frobenius (WittVector.teichmuller p a) • x' =
      (D.varpi u + D.verschiebung v) + (D.varpi n₁ + D.verschiebung n₁') := by
    rw [← hlam, ← hnn, CerednikDrinfeld.GradedCartierModuleData.lambda_nMk, map_add, map_add]; abel
  have hmem1 : D.varpi u + D.verschiebung v ∈ D.piece (i + 1) :=
    Submodule.add_mem _ (D.varpi_mem i u hu) (D.verschiebung_mem i v hv)
  have hmem2 : D.varpi n₁ + D.verschiebung n₁' ∈ D.piece i := by
    have h1 := D.varpi_mem (i + 1) n₁ hn₁
    have h2 := D.verschiebung_mem (i + 1) n₁' hn₁'
    rw [h11] at h1 h2
    exact Submodule.add_mem _ h1 h2
  have hmemx' : WittVector.frobenius (WittVector.teichmuller p a) • x' ∈ D.piece (i + 1) :=
    Submodule.smul_mem _ _ hx'
  have hzero : D.varpi n₁ + D.verschiebung n₁' = 0 := by
    refine E0Up.eq_zero_of_mem_piece_of_mem_piece_succ D i _ hmem2 ?_
    have : D.varpi n₁ + D.verschiebung n₁' =
        WittVector.frobenius (WittVector.teichmuller p a) • x' - (D.varpi u + D.verschiebung v) := by
      rw [hsplit]; abel
    rw [this]
    exact Submodule.sub_mem _ hmemx' hmem1
  have hstar : WittVector.frobenius (WittVector.teichmuller p a) • x' = D.varpi u + D.verschiebung v := by
    rw [hsplit, hzero, add_zero]

  obtain ⟨c, u', hu', hu_eq⟩ := E0Up.exists_eq_teichmuller_smul_add_verschiebung D hγ i u hu
  obtain ⟨d, x'', hx'', hx'_eq⟩ := E0Up.exists_eq_teichmuller_smul_add_verschiebung D hγ (i + 1) x' hx'
  have lhs : WittVector.frobenius (WittVector.teichmuller p a) • x' =
      WittVector.teichmuller p (a ^ p * d) • γ (i + 1) +
        D.verschiebung (WittVector.frobenius (WittVector.frobenius (WittVector.teichmuller p a)) • x'') := by
    rw [hx'_eq, smul_add, smul_smul, D.smul_verschiebung, E0Up.frobenius_teichmuller, ← map_mul]
  have rhs : D.varpi u + D.verschiebung v =
      WittVector.teichmuller p (c * a) • γ (i + 1) +
        D.verschiebung (WittVector.frobenius (WittVector.teichmuller p c) • x + D.varpi u' + v) := by
    rw [hu_eq, map_add, map_smul, hPiI, D.varpi_verschiebung, smul_add, D.smul_verschiebung, smul_smul, ← map_mul,
      map_add, map_add]
    abel
  obtain ⟨hcd, -⟩ := E0Up.teichmuller_smul_add_verschiebung_inj D hγ (i + 1) (lhs.symm.trans (hstar.trans rhs))

  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  have hc : c = a ^ (p - 1) * d := by
    have : a * (c - a ^ (p - 1) * d) = 0 := by
      rw [mul_sub, mul_comm a c, ← hcd, ← mul_assoc, ← pow_succ', hp1, sub_self]
    exact sub_eq_zero.mp (hreg _ this)

  refine ⟨a, d, x, u, v, u', WittVector.teichmuller p (a ^ (p - 1)) • x', ε, hPiI, hε, ?_, ?_, ?_⟩
  · apply CerednikDrinfeld.GradedCartierModuleData.lambda_injective_of_isHomogeneousVBasis_of_torsionFree p jS hS D γ hγ
    rw [map_smul, hL.lambda_comp, CerednikDrinfeld.GradedCartierModuleData.lambda_nMk, ← hV, hstar, map_add]
    abel
  · rw [← hc]; exact hu_eq
  · rw [← hstar, smul_smul, ← map_mul, ← pow_succ', hp1, E0Up.frobenius_teichmuller]

end S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_exists_smul_apply_eq_nMk_of_torsionFree
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_exists_smul_apply_eq_nMk_of_torsionFree (solution)
