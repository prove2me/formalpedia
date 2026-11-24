-- Prove2me | solution 1 for Formalism.GM.determinant_block_leading_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:47.691094+00:00
-- url     : https://prove2.me/submissions/025c6aff-4fec-4fbb-b334-8da5b17f3384

import Definitions.Def_Formalism_MahlerMeasure_Statement
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_DeterminantBlockLeadingTerm
import Theorems.Thm_Formalism_GM_det_natDegree_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
namespace Formalism.GM
theorem _root_.solution : DetBlockLead := by
  unfold DetBlockLead
  intro K _ n A D e he hA
  set M : Matrix (Fin n) (Fin n) K :=
    Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0 with hM
  have hdeg : ∀ σ : Equiv.Perm (Fin n), ∀ i, (A (σ i) i).natDegree ≤ D - e i := by
    intro σ i
    have h3 := hA (σ i) i
    have h4 : e i ≤ max (e (σ i)) (e i) := le_max_right _ _
    omega
  obtain ⟨h1, h2⟩ := det_natDegree_coeff A (∑ i, (D - e i)) (fun _ i => D - e i)
    (fun _ => rfl) hdeg
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      ∏ i, (A (σ i) i).coeff (D - e i) = ∏ i, M (σ i) i := by
    intro σ
    by_cases hall : ∀ i, e (σ i) = e i
    · refine Finset.prod_congr rfl (fun i _ => ?_)
      simp [hM, Matrix.of_apply, hall i]
    · push_neg at hall
      have hex : ∃ j, e j < e (σ j) := by
        by_contra hno
        push_neg at hno
        have hsum : ∑ j, e (σ j) = ∑ j, e j := Equiv.sum_comp σ e
        have hall' := (Finset.sum_eq_sum_iff_of_le (fun j _ => hno j)).1 hsum
        obtain ⟨i, hi⟩ := hall
        exact hi (hall' i (Finset.mem_univ i))
      obtain ⟨j, hj⟩ := hex
      have hne : e (σ j) ≠ e j := ne_of_gt hj
      have hL : (A (σ j) j).coeff (D - e j) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have h3 := hA (σ j) j
        have h4 : e (σ j) ≤ max (e (σ j)) (e j) := le_max_left _ _
        have h5 := he (σ j)
        omega
      have hR : M (σ j) j = 0 := by simp [hM, Matrix.of_apply, hne]
      rw [Finset.prod_eq_zero (f := fun i => (A (σ i) i).coeff (D - e i)) (Finset.mem_univ j) hL,
        Finset.prod_eq_zero (f := fun i => M (σ i) i) (Finset.mem_univ j) hR]
  have hdet : A.det.coeff (∑ i, (D - e i)) = M.det := by
    rw [h2, Matrix.det_apply]
    exact Finset.sum_congr rfl (fun σ _ => by rw [hprod σ])
  refine ⟨h1, hdet, fun hne => ?_⟩
  have hN : A.det.natDegree = ∑ i, (D - e i) :=
    le_antisymm h1 (Polynomial.le_natDegree_of_ne_zero (by rw [hdet]; exact hne))
  refine ⟨hN, ?_⟩
  rw [Polynomial.leadingCoeff, hN, hdet]
end Formalism.GM
