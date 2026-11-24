-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrfc_coeffT_Phi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:18.893433+00:00
-- url     : https://prove2.me/submissions/76b75f25-6dd9-4105-85d5-a78f6e089518

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_coeffT_sum
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_coeffT_C_monomial_mul
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_coeffT_iota
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_tau_iota
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_Phi_nil
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_Phi_append_single
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_applyWord_append_single
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_applyWord_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (L : List (Fin r × Fin r × (Fin r × Fin n)))
    (hL : (L.map (·.2.2)).Nodup) (F : MvPolynomial (Fin r × Fin n) R) (d : Fin r × Fin n →₀ ℕ) :
    lrfc_coeffT d (lrfc_Phi L (lrfc_iota F)) =
      if (∀ u, u ∉ L.map (·.2.2) → d u = 0) then
        applyWord R (L.map fun l => (l.1, l.2.1, d l.2.2)) F else 0 := by
  classical
  induction L using List.reverseRecOn generalizing F d with
  | nil =>
    rw [lrfc_Phi_nil, lrfc_coeffT_iota]
    have : (∀ u, u ∉ ([] : List (Fin r × Fin r × (Fin r × Fin n))).map (·.2.2) → d u = 0) ↔ d = 0 := by
      simp [Finsupp.ext_iff]
    simp only [this]
    rfl
  | append_singleton w l ih =>
    obtain ⟨s, a, v⟩ := l
    have hL' : (w.map (·.2.2) ++ [v]).Nodup := by simpa using hL
    have hw : (w.map (·.2.2)).Nodup := hL'.sublist (List.sublist_append_left _ _)
    have hv : v ∉ w.map (·.2.2) := by
      rw [List.nodup_append] at hL'
      intro h
      exact hL'.2.2 v h v (by simp) rfl
    rw [lrfc_Phi_append_single, lrfc_tau_iota, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
      map_sum, lrfc_coeffT_sum]
    have key : ∀ (j : ℕ) (c : MvPolynomial (Fin r × Fin n) R),
        lrfc_coeffT d (lrfc_Phi w (lrfc_iota c * C (X (s, a, v).2.2) ^ j)) =
          if j ≤ d v then lrfc_coeffT (d - Finsupp.single v j) (lrfc_Phi w (lrfc_iota c)) else 0 := by
      intro j c
      have e0 : (C (X (s, a, v).2.2) : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) ^ j =
          C (X v ^ j) := (map_pow C (X v) j).symm
      rw [e0, map_mul]
      have hC : lrfc_Phi w (C (X v ^ j)) = C (X v ^ j : MvPolynomial (Fin r × Fin n) R) :=
        (lrfc_Phi w).commutes (X v ^ j)
      rw [hC, mul_comm, X_pow_eq_monomial, lrfc_coeffT_C_monomial_mul]
      simp only [Finsupp.single_le_iff]
    simp only [key, ih hw]
    rw [Finset.sum_eq_single (d v)]
    · simp only [le_refl, if_true]
      have hfill : w.map (fun l => (l.1, l.2.1, (d - Finsupp.single v (d v)) l.2.2)) =
          w.map (fun l => (l.1, l.2.1, d l.2.2)) := by
        apply List.map_congr_left
        intro l hl
        have hne : l.2.2 ≠ v := by
          intro h; exact hv (List.mem_map.mpr ⟨l, hl, h⟩)
        simp [Finsupp.single_apply, Ne.symm hne]
      have hcond : (∀ u, u ∉ w.map (·.2.2) → (d - Finsupp.single v (d v)) u = 0) ↔
          (∀ u, u ∉ (w ++ [(s, a, v)]).map (·.2.2) → d u = 0) := by
        constructor
        · intro h u hu
          simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton,
            not_or] at hu
          have := h u hu.1
          simpa [Finsupp.single_apply, Ne.symm hu.2] using this
        · intro h u hu
          by_cases huv : u = v
          · subst huv; simp
          · have := h u (by simp [hu, huv])
            simp [this]
      rw [hfill]
      simp only [hcond]
      split_ifs
      · rw [List.map_append, List.map_cons, List.map_nil, lrfc_applyWord_append_single]
        rfl
      · rfl
    · intro j _ hj
      split_ifs with h1 h2
      · exfalso
        have := h2 v hv
        simp at this
        omega
      · rfl
      · rfl
    · intro hnot
      rw [Polynomial.notMem_support_iff.mp hnot]
      simp [lrfc_applyWord_zero]
end Formalism.CohomologicalDescent.LR
