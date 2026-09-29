-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4911fc1a-d3b2-5446-b071-f96b2b212223

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis

set_option autoImplicit false

noncomputable section

namespace B29AC

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData WittVector

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
  (D : GradedCartierModuleData p B j) {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)

theorem iterate_add (n : ℕ) (x y : D.M) :
    (⇑D.verschiebung)^[n] (x + y) = (⇑D.verschiebung)^[n] x + (⇑D.verschiebung)^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      map_add]

def expd (x : D.M) : (Fin 2 → B) × D.M := Classical.choose (hγ.2 x).exists

theorem expd_spec (x : D.M) :
    x = (∑ i : Fin 2, teichmuller p ((expd D hγ x).1 i) • γ i) + D.verschiebung (expd D hγ x).2 :=
  Classical.choose_spec (hγ.2 x).exists

theorem expd_unique (x : D.M) (c : Fin 2 → B) (y : D.M)
    (h : x = (∑ i : Fin 2, teichmuller p (c i) • γ i) + D.verschiebung y) : (c, y) = expd D hγ x :=
  (hγ.2 x).unique h (expd_spec D hγ x)

include hγ in
theorem expd_zero_of_eq (c : Fin 2 → B) (y : D.M)
    (h : (0 : D.M) = (∑ i : Fin 2, teichmuller p (c i) • γ i) + D.verschiebung y) : c = 0 ∧ y = 0 := by
  have h0 : (0 : D.M) = (∑ i : Fin 2, teichmuller p ((0 : Fin 2 → B) i) • γ i) + D.verschiebung 0 := by
    simp [teichmuller_zero]
  have h1 := expd_unique D hγ 0 c y h
  have h2 := expd_unique D hγ 0 0 0 h0
  have := h1.trans h2.symm
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

theorem sum_two_of_eq_zero (π : Fin 2) (c : Fin 2 → B) (h : c (π + 1) = 0) :
    (∑ i : Fin 2, teichmuller p (c i) • γ i) = teichmuller p (c π) • γ π := by
  fin_cases π
  · have h' : c 1 = 0 := h
    simp [Fin.sum_univ_two, h', teichmuller_zero]
  · have h' : c 0 = 0 := h
    simp [Fin.sum_univ_two, h', teichmuller_zero]

theorem add_one_add_one (k : Fin 2) : k + 1 + 1 = k := by
  fin_cases k <;> rfl

theorem decomp (k : Fin 2) (y : D.M) : ∃ u ∈ D.piece k, ∃ v ∈ D.piece (k + 1), y = u + v := by
  have htop : D.piece 0 ⊔ D.piece 1 = ⊤ := D.isCompl_piece.sup_eq_top
  have hy : y ∈ D.piece 0 ⊔ D.piece 1 := by rw [htop]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hy
  fin_cases k
  · exact ⟨u, hu, v, hv, huv.symm⟩
  · exact ⟨v, hv, u, hu, by rw [← huv, add_comm]⟩

theorem eq_zero_of_mem_mem (k : Fin 2) (z : D.M) (h1 : z ∈ D.piece k) (h2 : z ∈ D.piece (k + 1)) : z = 0 := by
  have hd := Submodule.disjoint_def.1 D.isCompl_piece.disjoint
  fin_cases k
  · exact hd z h1 h2
  · exact hd z h2 h1

theorem expd_graded (k : Fin 2) (x : D.M) (hx : x ∈ D.piece k) :
    (expd D hγ x).1 (k + 1) = 0 ∧ (expd D hγ x).2 ∈ D.piece (k + 1) := by
  set c := (expd D hγ x).1 with hc
  set y := (expd D hγ x).2 with hy
  have hxe : x = (∑ i : Fin 2, teichmuller p (c i) • γ i) + D.verschiebung y := expd_spec D hγ x
  obtain ⟨u, hu, v, hv, hyuv⟩ := decomp D k y

  set c' : Fin 2 → B := Pi.single (k + 1) (c (k + 1)) with hc'
  have hc'k : c' (k + 1 + 1) = 0 := by
    rw [hc', add_one_add_one, Pi.single_eq_of_ne]
    intro h; fin_cases k <;> exact absurd h (by decide)
  have hsum' : (∑ i : Fin 2, teichmuller p (c' i) • γ i) = teichmuller p (c (k + 1)) • γ (k + 1) := by
    rw [sum_two_of_eq_zero D (k + 1) c' hc'k, hc', Pi.single_eq_same]
  have hsum : (∑ i : Fin 2, teichmuller p (c i) • γ i) =
      teichmuller p (c k) • γ k + teichmuller p (c (k + 1)) • γ (k + 1) := by
    fin_cases k <;> simp [Fin.sum_univ_two, add_comm]

  have hv'1 : teichmuller p (c (k + 1)) • γ (k + 1) + D.verschiebung u ∈ D.piece (k + 1) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 (k + 1))) (D.verschiebung_mem k u hu)
  have hv'0 : teichmuller p (c (k + 1)) • γ (k + 1) + D.verschiebung u ∈ D.piece k := by
    have heq : teichmuller p (c (k + 1)) • γ (k + 1) + D.verschiebung u =
        x - (teichmuller p (c k) • γ k + D.verschiebung v) := by
      rw [hxe, hsum, hyuv, map_add]; abel
    rw [heq]
    refine Submodule.sub_mem _ hx (Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 k)) ?_)
    have := D.verschiebung_mem (k + 1) v hv
    rwa [add_one_add_one] at this
  have hzero : teichmuller p (c (k + 1)) • γ (k + 1) + D.verschiebung u = 0 :=
    eq_zero_of_mem_mem D k _ hv'0 hv'1
  have h0 : (0 : D.M) = (∑ i : Fin 2, teichmuller p (c' i) • γ i) + D.verschiebung u := by
    rw [hsum', hzero]
  obtain ⟨hc'0, hu0⟩ := expd_zero_of_eq D hγ c' u h0
  refine ⟨?_, ?_⟩
  · have := congrFun hc'0 (k + 1)
    rwa [hc', Pi.single_eq_same] at this
  · rw [hyuv, hu0, zero_add]; exact hv

omit D hγ in
theorem natCast_p_eq : ∃ t : WittVector p B, (p : WittVector p B) = teichmuller p (p : B) + verschiebung t := by
  set x : WittVector p B := (p : WittVector p B) - teichmuller p (p : B) with hxdef
  have hx : ∀ i < 1, x.coeff i = 0 := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [← constantCoeff_apply, hxdef, map_sub, map_natCast, constantCoeff_apply, teichmuller_coeff_zero, sub_self]
  refine ⟨x.shift 1, ?_⟩
  have h := eq_iterate_verschiebung hx
  rw [Function.iterate_one] at h
  rw [← h, hxdef]
  abel

def sq (i : Fin 2) : ℕ → D.M
  | 0 => D.varpi (γ i)
  | m + 1 => (expd D hγ (sq i m)).2

def cst : ℕ → Fin 2 → B := fun m i => (expd D hγ (sq D hγ i m)).1 (piIndex m i)

omit D hγ in
theorem piIndex_zero (i : Fin 2) : piIndex 0 i = i + 1 := by
  fin_cases i <;> rfl

omit D hγ in
theorem piIndex_succ (m : ℕ) (i : Fin 2) : piIndex (m + 1) i = piIndex m i + 1 := by
  apply Fin.ext
  simp only [piIndex, Fin.val_add]
  fin_cases i <;> simp

theorem sq_mem (i : Fin 2) (m : ℕ) : sq D hγ i m ∈ D.piece (piIndex m i) := by
  induction m with
  | zero => rw [piIndex_zero]; exact D.varpi_mem i _ (hγ.1 i)
  | succ m ih => rw [piIndex_succ]; exact (expd_graded D hγ _ _ ih).2

theorem sq_step (i : Fin 2) (m : ℕ) :
    sq D hγ i m = teichmuller p (cst D hγ m i) • γ (piIndex m i) + D.verschiebung (sq D hγ i (m + 1)) := by
  have h := expd_spec D hγ (sq D hγ i m)
  have hz := (expd_graded D hγ _ _ (sq_mem D hγ i m)).1
  rw [sum_two_of_eq_zero D (piIndex m i) _ hz] at h
  exact h

theorem main (i : Fin 2) (N : ℕ) :
    D.varpi (γ i) =
      (∑ m : Fin N, (⇑D.verschiebung)^[(m : ℕ)]
        (WittVector.teichmuller p (cst D hγ m i) • γ (piIndex m i))) + (⇑D.verschiebung)^[N] (sq D hγ i N) := by
  induction N with
  | zero => simp [sq]
  | succ N ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    conv_lhs => rw [ih, sq_step D hγ i N, iterate_add, ← Function.iterate_succ_apply]
    rw [add_assoc]

omit D hγ in
theorem one_add_one : (1 : Fin 2) + 1 = 0 := rfl

theorem prod_eq : cst D hγ 0 0 * cst D hγ 0 1 = (p : B) := by
  have h0 := sq_step D hγ 0 0
  have h1 := sq_step D hγ 1 0
  rw [piIndex_zero] at h0 h1
  change D.varpi (γ 0) = _ at h0
  change D.varpi (γ 1) = _ at h1
  rw [zero_add] at h0
  rw [one_add_one] at h1
  obtain ⟨t, ht⟩ := natCast_p_eq (p := p) (B := B)

  have lhs : D.varpi (D.varpi (γ 0)) =
      (∑ i : Fin 2, teichmuller p ((Pi.single (0 : Fin 2) (cst D hγ 0 0 * cst D hγ 0 1) : Fin 2 → B) i) • γ i) +
        D.verschiebung (WittVector.frobenius (teichmuller p (cst D hγ 0 0)) • sq D hγ 1 1 + D.varpi (sq D hγ 0 1)) := by
    rw [sum_two_of_eq_zero D 0 _ (by simp), Pi.single_eq_same]
    conv_lhs => rw [h0]
    rw [map_add, map_smul, h1, D.varpi_verschiebung, smul_add, smul_smul, ← map_mul, D.smul_verschiebung,
      map_add, add_assoc]
  have rhs : D.varpi (D.varpi (γ 0)) =
      (∑ i : Fin 2, teichmuller p ((Pi.single (0 : Fin 2) (p : B) : Fin 2 → B) i) • γ i) +
        D.verschiebung (t • D.frobenius (γ 0)) := by
    rw [sum_two_of_eq_zero D 0 _ (by simp), Pi.single_eq_same, D.varpi_varpi,
      ← Nat.cast_smul_eq_nsmul (WittVector p B), ht, add_smul, D.verschiebung_smul_frobenius]
  have e1 := expd_unique D hγ _ _ _ lhs
  have e2 := expd_unique D hγ _ _ _ rhs
  have := congrArg Prod.fst (e1.trans e2.symm)
  have := congrFun this 0
  simpa using this

end B29AC

open CerednikDrinfeld in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ) :
    ∃ a : ℕ → Fin 2 → B, D.HasStructureConstants γ a ∧ a 0 0 * a 0 1 = (p : B) :=
  ⟨B29AC.cst D hγ, fun i N => ⟨B29AC.sq D hγ i N, B29AC.main D hγ i N⟩, B29AC.prod_eq D hγ⟩

end
end S_CerednikDrinfeld_GradedCartierModuleData_exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis (solution)
