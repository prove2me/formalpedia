-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.exists_digits_mem_sq_of_varpi_eq_verschiebung
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/3e1579c4-92fd-56ec-b5e2-2cb890efc53a

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_digits_mem_sq_of_varpi_eq_verschiebung

set_option autoImplicit false

open CerednikDrinfeld

namespace DigitKit

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

section More

variable {p : ℕ} [Fact p.Prime] {S : Type} [CommRing S] {jS : Zp2 p →+* S}

open WittVector

theorem mem_piece_succ_of_verschiebung_mem (D : GradedCartierModuleData p S jS) {γ : Fin 2 → D.M}
    (hγ : D.IsHomogeneousVBasis γ) (l : Fin 2) (y : D.M) (hy : D.verschiebung y ∈ D.piece l) :
    y ∈ D.piece (l + 1) := by
  obtain ⟨y₀, y₁, hy₀, hy₁, rfl⟩ := exists_piece_decomp D (l + 1) y

  rw [fin2_add_one_add_one] at hy₁
  have hV1 : D.verschiebung y₁ ∈ D.piece (l + 1) := D.verschiebung_mem l y₁ hy₁
  have hV0 : D.verschiebung y₀ ∈ D.piece l := by
    have := D.verschiebung_mem (l + 1) y₀ hy₀
    rwa [fin2_add_one_add_one] at this
  have hV1' : D.verschiebung y₁ ∈ D.piece l := by
    have : D.verschiebung y₁ = D.verschiebung (y₀ + y₁) - D.verschiebung y₀ := by rw [map_add]; abel
    rw [this]
    exact Submodule.sub_mem _ hy hV0
  have h0 : D.verschiebung y₁ = 0 := eq_zero_of_mem_piece_of_mem_piece_succ D l _ hV1' hV1
  have hy1 : y₁ = 0 := hγ.verschiebung_injective (by rw [h0, map_zero])
  rw [hy1, add_zero]
  exact hy₀

theorem exists_eq_teichmuller_add_verschiebung' (w : WittVector p S) :
    ∃ w₁ : WittVector p S, w = teichmuller p (w.coeff 0) + verschiebung w₁ := by
  have h0 : (w - teichmuller p (w.coeff 0)).coeff 0 = 0 := by
    have h := add_coeff_zero (teichmuller p (w.coeff 0)) (w - teichmuller p (w.coeff 0))
    rw [add_sub_cancel, teichmuller_coeff_zero] at h
    exact left_eq_add.mp h
  refine ⟨(w - teichmuller p (w.coeff 0)).shift 1, ?_⟩
  have := eq_iterate_verschiebung (x := w - teichmuller p (w.coeff 0)) (n := 1)
    (by intro i hi; interval_cases i; exact h0)
  rw [Function.iterate_one] at this
  rw [← this, add_sub_cancel]

theorem eq_verschiebung_shift_of_coeff_zero (w : WittVector p S) (h : w.coeff 0 = 0) :
    w = verschiebung (w.shift 1) ∧ (w.shift 1).coeff 0 = w.coeff 1 := by
  refine ⟨?_, by rw [shift_coeff, add_zero]⟩
  have := eq_iterate_verschiebung (x := w) (n := 1) (by intro i hi; interval_cases i; exact h)
  rwa [Function.iterate_one] at this

theorem smul_teichmuller_smul_add_verschiebung (D : GradedCartierModuleData p S jS) (w w₁ : WittVector p S)
    (hw : w = teichmuller p (w.coeff 0) + verschiebung w₁) (k : S) (g y : D.M) :
    w • (teichmuller p k • g + D.verschiebung y) =
      teichmuller p (w.coeff 0 * k) • g +
        D.verschiebung (WittVector.frobenius (teichmuller p (w.coeff 0)) • y +
          w₁ • D.frobenius (teichmuller p k • g + D.verschiebung y)) := by
  conv_lhs => rw [hw]
  rw [add_smul, ← D.verschiebung_smul_frobenius, smul_add, smul_smul, ← map_mul, D.smul_verschiebung, map_add, map_add]
  abel

theorem coeff_one_teichmuller_add_mem_span (α β : S) :
    (teichmuller p α + teichmuller p β - teichmuller p (α + β)).coeff 1 ∈ Ideal.span {α} := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← WittVector.map_coeff (Ideal.Quotient.mk (Ideal.span {α}))]
  have hα : Ideal.Quotient.mk (Ideal.span {α}) α = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self α)
  rw [map_sub, map_add, map_teichmuller, map_teichmuller, map_teichmuller, map_add, hα, teichmuller_zero, zero_add, zero_add,
    sub_self, WittVector.zero_coeff]

end More

end DigitKit

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : Zp2 p →+* B)
    (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (i : Fin 2) (xi xnext : D.M) (a : B)
    (hcrit : D.varpi (γ i) = D.verschiebung xi)
    (hnext : D.varpi (γ (i + 1)) = WittVector.teichmuller p a • γ i + D.verschiebung xnext)
    (m : D.M) (hm : m ∈ D.piece i) (hinv : D.varpi m = D.verschiebung m) :
    ∃ (c d : B) (m₂ : D.M),
      m = WittVector.teichmuller p c • γ i +
        D.verschiebung (WittVector.teichmuller p d • γ (i + 1) + D.verschiebung m₂) ∧
      c - a * d ∈ (Ideal.span {c, d}) ^ 2 ∧ d ∈ (Ideal.span {c, d}) ^ 2 := by
  classical
  have h11 := DigitKit.fin2_add_one_add_one i
  have two_le : 2 ≤ p := (Fact.out : p.Prime).two_le

  have hxi : xi ∈ D.piece i := by
    have := DigitKit.mem_piece_succ_of_verschiebung_mem D hγ (i + 1) xi
      (by rw [← hcrit]; exact D.varpi_mem i _ (hγ.1 i))
    rwa [h11] at this
  have hxn : xnext ∈ D.piece (i + 1) := by
    refine DigitKit.mem_piece_succ_of_verschiebung_mem D hγ i xnext ?_
    have e : D.verschiebung xnext = D.varpi (γ (i + 1)) - WittVector.teichmuller p a • γ i := by
      rw [hnext]; abel
    rw [e]
    refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ (hγ.1 i))
    have := D.varpi_mem (i + 1) _ (hγ.1 (i + 1))
    rwa [h11] at this

  obtain ⟨c, m1, hm1p, hmE⟩ := DigitKit.exists_eq_teichmuller_smul_add_verschiebung D hγ i m hm
  obtain ⟨d, m2, hm2p, hm1E⟩ := DigitKit.exists_eq_teichmuller_smul_add_verschiebung D hγ (i + 1) m1 hm1p
  rw [h11] at hm2p
  obtain ⟨e, xi', hxi'p, hxiE⟩ := DigitKit.exists_eq_teichmuller_smul_add_verschiebung D hγ i xi hxi
  obtain ⟨h, xi'', -, hxi'E⟩ := DigitKit.exists_eq_teichmuller_smul_add_verschiebung D hγ (i + 1) xi' hxi'p
  obtain ⟨g, xn', -, hxnE⟩ := DigitKit.exists_eq_teichmuller_smul_add_verschiebung D hγ (i + 1) xnext hxn
  obtain ⟨f, m3, -, hm2E⟩ := DigitKit.exists_eq_teichmuller_smul_add_verschiebung D hγ i m2 hm2p
  obtain ⟨k, fr', -, hFE⟩ := DigitKit.exists_eq_teichmuller_smul_add_verschiebung D hγ (i + 1) (D.frobenius (γ i))
    (D.frobenius_mem i _ (hγ.1 i))

  have hPm : D.varpi m = D.verschiebung (WittVector.teichmuller p (c ^ p) • xi + D.varpi m1) := by
    rw [hmE, map_add, map_smul, hcrit, D.smul_verschiebung, DigitKit.frobenius_teichmuller, D.varpi_verschiebung, map_add]
  have hstar : m = WittVector.teichmuller p (c ^ p) • xi + D.varpi m1 :=
    hγ.verschiebung_injective (by rw [← hPm, hinv])
  have hPm1 : D.varpi m1 = WittVector.teichmuller p (d * a) • γ i +
      D.verschiebung (WittVector.teichmuller p (d ^ p) • xnext + D.varpi m2) := by
    rw [hm1E, map_add, map_smul, hnext, smul_add, smul_smul, ← map_mul, D.smul_verschiebung,
      DigitKit.frobenius_teichmuller, D.varpi_verschiebung, map_add, add_assoc]

  set R := WittVector.teichmuller p (c ^ (p * p)) • xi' + (WittVector.teichmuller p (d ^ p) • xnext + D.varpi m2) with hR
  have hstar2 : m = (WittVector.teichmuller p (c ^ p * e) + WittVector.teichmuller p (d * a)) • γ i + D.verschiebung R := by
    rw [hstar, hPm1, hxiE, smul_add, smul_smul, ← map_mul, D.smul_verschiebung, DigitKit.frobenius_teichmuller,
      ← pow_mul, add_smul, hR]
    simp only [map_add]
    abel
  set ω := WittVector.teichmuller p (c ^ p * e) + WittVector.teichmuller p (d * a) - WittVector.teichmuller p c with hω
  have hωγ : ω • γ i = D.verschiebung (m1 - R) := by
    rw [hω, sub_smul, map_sub, sub_eq_sub_iff_add_eq_add, add_comm (D.verschiebung m1), ← hmE, ← hstar2]
  have hω0 : ω.coeff 0 = c ^ p * e + d * a - c := by
    rw [← WittVector.constantCoeff_apply, hω, map_sub, map_add, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
      WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]

  obtain ⟨ω₁, hω₁⟩ := DigitKit.exists_eq_teichmuller_add_verschiebung' ω
  have hωγ2 : ω • γ i = WittVector.teichmuller p (ω.coeff 0) • γ i + D.verschiebung (ω₁ • D.frobenius (γ i)) := by
    conv_lhs => rw [hω₁]
    rw [add_smul, ← D.verschiebung_smul_frobenius]
  have hcmp := DigitKit.teichmuller_smul_add_verschiebung_inj D hγ i
    (c := ω.coeff 0) (c' := 0) (y := ω₁ • D.frobenius (γ i)) (y' := m1 - R)
    (by rw [← hωγ2, hωγ, WittVector.teichmuller_zero, zero_smul, zero_add])
  have hc_eq : c = c ^ p * e + d * a := by
    have := hcmp.1
    rw [hω0] at this
    linear_combination (-1 : B) * this
  have hcI : c ∈ Ideal.span {c, d} := Ideal.subset_span (by simp)
  have hdI : d ∈ Ideal.span {c, d} := Ideal.subset_span (by simp)
  have hcp : ∀ (n : ℕ) (r : B), 2 ≤ n → c ^ n * r ∈ Ideal.span {c, d} ^ 2 := by
    intro n r hn
    rw [← Nat.add_sub_cancel' hn, pow_add, pow_two, mul_assoc, pow_two]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hcI hcI)
  have hdp : ∀ (n : ℕ) (r : B), 2 ≤ n → d ^ n * r ∈ Ideal.span {c, d} ^ 2 := by
    intro n r hn
    rw [← Nat.add_sub_cancel' hn, pow_add, pow_two, mul_assoc, pow_two]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hdI hdI)
  refine ⟨c, d, m2, by rw [hmE, hm1E], ?_, ?_⟩
  · have : c - a * d = c ^ p * e := by linear_combination hc_eq
    rw [this]
    exact hcp p e two_le
  ·
    have hω00 : ω.coeff 0 = 0 := hcmp.1
    obtain ⟨hωV, hω1⟩ := DigitKit.eq_verschiebung_shift_of_coeff_zero ω hω00
    have hωγ3 : ω • γ i = WittVector.teichmuller p (0 : B) • γ i + D.verschiebung (ω.shift 1 • D.frobenius (γ i)) := by
      conv_lhs => rw [hωV]
      rw [← D.verschiebung_smul_frobenius, WittVector.teichmuller_zero, zero_smul, zero_add]
    have hcmp2 := DigitKit.teichmuller_smul_add_verschiebung_inj D hγ i
      (c := 0) (c' := 0) (y := ω.shift 1 • D.frobenius (γ i)) (y' := m1 - R)
      (by rw [← hωγ3, hωγ, WittVector.teichmuller_zero, zero_smul, zero_add])
    have hm1R : m1 = R + ω.shift 1 • D.frobenius (γ i) := by rw [hcmp2.2, add_sub_cancel]

    obtain ⟨ω₃, hω₃⟩ := DigitKit.exists_eq_teichmuller_add_verschiebung' (ω.shift 1)
    have hT := DigitKit.smul_teichmuller_smul_add_verschiebung D (ω.shift 1) ω₃ hω₃ k (γ (i + 1)) fr'
    rw [← hFE] at hT

    have hPm2 : D.varpi m2 = D.verschiebung (WittVector.teichmuller p (f ^ p) • xi + D.varpi m3) := by
      rw [hm2E, map_add, map_smul, hcrit, D.smul_verschiebung, DigitKit.frobenius_teichmuller, D.varpi_verschiebung, map_add]
    have hRexp : R = (WittVector.teichmuller p (c ^ (p * p) * h) + WittVector.teichmuller p (d ^ p * g)) • γ (i + 1) +
        D.verschiebung (WittVector.frobenius (WittVector.teichmuller p (c ^ (p * p))) • xi'' + WittVector.frobenius (WittVector.teichmuller p (d ^ p)) • xn' +
          (WittVector.teichmuller p (f ^ p) • xi + D.varpi m3)) := by
      rw [hR, hxi'E, hxnE, hPm2, smul_add, smul_smul, ← map_mul, D.smul_verschiebung, smul_add, smul_smul, ← map_mul,
        D.smul_verschiebung, add_smul]
      simp only [map_add]
      abel

    set W := WittVector.teichmuller p (c ^ (p * p) * h) + WittVector.teichmuller p (d ^ p * g) + WittVector.teichmuller p ((ω.shift 1).coeff 0 * k) with hW
    set Y := (WittVector.frobenius (WittVector.teichmuller p (c ^ (p * p))) • xi'' + WittVector.frobenius (WittVector.teichmuller p (d ^ p)) • xn' +
          (WittVector.teichmuller p (f ^ p) • xi + D.varpi m3)) +
        (WittVector.frobenius (WittVector.teichmuller p ((ω.shift 1).coeff 0)) • fr' +
          ω₃ • D.frobenius (D.frobenius (γ i))) with hY
    have hm1W : m1 = W • γ (i + 1) + D.verschiebung Y := by
      rw [hm1R, hRexp, hT, hW, hY, add_smul, add_smul, add_smul]
      simp only [map_add]
      abel
    obtain ⟨W₁, hW₁⟩ := DigitKit.exists_eq_teichmuller_add_verschiebung' W
    have hW0 : W.coeff 0 = c ^ (p * p) * h + d ^ p * g + (ω.shift 1).coeff 0 * k := by
      rw [← WittVector.constantCoeff_apply, hW, map_add, map_add, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
        WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
    have hm1fin : m1 = WittVector.teichmuller p (W.coeff 0) • γ (i + 1) + D.verschiebung (W₁ • D.frobenius (γ (i + 1)) + Y) := by
      rw [hm1W]
      conv_lhs => rw [hW₁]
      rw [add_smul, ← D.verschiebung_smul_frobenius, hY]
      simp only [map_add]
      abel
    have hcmp3 := DigitKit.teichmuller_smul_add_verschiebung_inj D hγ (i + 1) (hm1E.symm.trans hm1fin)
    have hd_eq : d = c ^ (p * p) * h + d ^ p * g + ω.coeff 1 * k := hcmp3.1.trans (by rw [hW0, hω1])

    have hω' : ω = WittVector.teichmuller p (c ^ p * e) + WittVector.teichmuller p (d * a) - WittVector.teichmuller p (c ^ p * e + d * a) := by rw [hω, ← hc_eq]
    have hmem : ω.coeff 1 ∈ Ideal.span {c ^ p * e} := by
      rw [hω']
      exact DigitKit.coeff_one_teichmuller_add_mem_span _ _
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
    have hX : c ^ (p * p) * h + d ^ p * g + ω.coeff 1 * k ∈ Ideal.span {c, d} ^ 2 := by
      refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
      · exact hcp (p * p) h (le_trans two_le (Nat.le_mul_self p))
      · exact hdp p g two_le
      · rw [← hr, show r * (c ^ p * e) * k = c ^ p * (r * e * k) by ring]
        exact hcp p _ two_le
    convert hX using 2

end S_CerednikDrinfeld_GradedCartierModuleData_exists_digits_mem_sq_of_varpi_eq_verschiebung
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_digits_mem_sq_of_varpi_eq_verschiebung (solution)
