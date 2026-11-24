-- Prove2me | solution 1 for FockRL.pderiv_homog_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:04.967861+00:00
-- url     : https://prove2.me/submissions/7528c4cb-f9fa-4445-b16f-40464b5faa8e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial
namespace FockRL
variable {p q r s : ℕ}
private theorem mem_homog_iff_isHomogeneous' {σ : Type} {d : ℕ} {P : MvPolynomial σ ℂ} :
    P ∈ FockH1Action.homog σ d ↔ P.IsHomogeneous d := by
  exact mem_homogeneousSubmodule d P
private theorem isHomogeneous_X_complex {σ : Type} (l : σ) : (X l : MvPolynomial σ ℂ).IsHomogeneous 1 := by
  exact isHomogeneous_X ℂ l
private theorem exists_forall_isHomogeneous_monomial {σ : Type} (u : σ →₀ ℕ) :
    ∃ k : ℕ, ∀ c : ℂ, (monomial u c).IsHomogeneous k := by
  exact ⟨_, fun c => isHomogeneous_monomial c rfl⟩
private theorem homogeneousComponent_eq_ite_of_isHomogeneous {σ : Type} {m n : ℕ} {P : MvPolynomial σ ℂ}
    (h : P.IsHomogeneous m) : homogeneousComponent n P = if m = n then P else 0 := by
  have h' : P ∈ homogeneousSubmodule σ ℂ m := mem_homog_iff_isHomogeneous'.mpr h
  first
  | exact homogeneousComponent_of_mem h'
  | exact homogeneousComponent_homogeneous_polynomial m n P h'
  | (by_cases hmn : m = n
     · subst hmn
       rw [if_pos rfl]
       ext d
       rw [coeff_homogeneousComponent]
       split_ifs with hd
       · rfl
       · exact (h.coeff_eq_zero hd).symm
     · rw [if_neg hmn]
       ext d
       rw [coeff_homogeneousComponent, coeff_zero]
       split_ifs with hd
       · exact h.coeff_eq_zero (by omega)
       · rfl)
private theorem homogeneousComponent_pderiv_monomial {σ : Type} (l : σ) (e : ℕ) (u : σ →₀ ℕ) (a : ℂ) :
    homogeneousComponent e (pderiv l (monomial u a)) =
      pderiv l (homogeneousComponent (e + 1) (monomial u a)) := by
  by_cases hu : u l = 0
  · obtain ⟨k, hk⟩ := exists_forall_isHomogeneous_monomial u
    have h0 : pderiv l (monomial u a) = 0 := by
      rw [pderiv_monomial, hu]
      simp
    rw [h0, map_zero, homogeneousComponent_eq_ite_of_isHomogeneous (hk a)]
    split_ifs
    · exact h0.symm
    · exact (map_zero _).symm
  · obtain ⟨k, hk⟩ := exists_forall_isHomogeneous_monomial (u - Finsupp.single l 1)
    have huv : u - Finsupp.single l 1 + Finsupp.single l 1 = u := by
      exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hu))
    have hmul : monomial u a = monomial (u - Finsupp.single l 1) a * X l := by
      rw [X, monomial_mul, huv, mul_one]
    have hu' : (monomial u a).IsHomogeneous (k + 1) := by
      rw [hmul]
      exact (hk a).mul (isHomogeneous_X_complex l)
    rw [pderiv_monomial, homogeneousComponent_eq_ite_of_isHomogeneous (hk _), homogeneousComponent_eq_ite_of_isHomogeneous hu']
    by_cases hke : k = e
    · subst hke
      rw [if_pos rfl, if_pos rfl, pderiv_monomial]
    · rw [if_neg hke, if_neg (show ¬ (k + 1 = e + 1) by omega), map_zero]
private theorem homogeneousComponent_pderiv {σ : Type} (l : σ) (e : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent e (pderiv l P) = pderiv l (homogeneousComponent (e + 1) P) := by
  rw [P.as_sum]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun u _ => homogeneousComponent_pderiv_monomial l e u _
section Inner
variable {σ : Type}
end Inner
end FockRL
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial
open FockRL
variable {p q r s : ℕ}
namespace FockRL
theorem _root_.solution {σ : Type} (l : σ) {P : MvPolynomial σ ℂ} (h : P.IsHomogeneous 0) :
    pderiv l P = 0 := by
  rw [← sum_homogeneousComponent (pderiv l P)]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [homogeneousComponent_pderiv, homogeneousComponent_eq_ite_of_isHomogeneous h,
    if_neg (show ¬ (0 = e + 1) by omega), map_zero]
end FockRL
