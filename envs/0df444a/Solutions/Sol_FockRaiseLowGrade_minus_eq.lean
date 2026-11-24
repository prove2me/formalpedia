-- Prove2me | solution 1 for FockRaiseLowGrade.minus_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:07.504793+00:00
-- url     : https://prove2.me/submissions/95068222-7579-437d-86dc-5b0b3b1fc80d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit
import Theorems.Thm_FockRaiseLowGrade_hc_hc
import Theorems.Thm_FockRaiseLowGrade_eq_zero_of_hc
import Theorems.Thm_FockRaiseLowGrade_sum_hc_of_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace FockRaiseLowGrade
open MvPolynomial FockH1Action
variable {σ : Type*}
private theorem apply_homogeneousComponent_eq_zero_of_lt_two (L : Module.End ℂ (MvPolynomial σ ℂ))
    (hL : ∀ (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e (L P) = L (homogeneousComponent (e + 2) P))
    (Q : MvPolynomial σ ℂ) (k : ℕ) (hk : k < 2) : L (homogeneousComponent k Q) = 0 := by
  apply eq_zero_of_hc
  intro e
  rw [hL, hc_hc, if_neg (show ¬ (e + 2 = k) by omega), map_zero]
end FockRaiseLowGrade
end
end

set_option autoImplicit false
noncomputable section
open FockRaiseLowGrade
open MvPolynomial FockH1Action
variable {σ : Type*}
namespace FockRaiseLowGrade
theorem _root_.solution (R L : Module.End ℂ (MvPolynomial σ ℂ))
    (hR : ∀ (d : ℕ) (P : MvPolynomial σ ℂ), P ∈ homog σ d → R P ∈ homog σ (d + 2))
    (hL : ∀ (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e (L P) = L (homogeneousComponent (e + 2) P))
    (P : MvPolynomial σ ℂ) : minusPart (R + L) P = L P := by
  classical
  have hterm : ∀ d, homogeneousComponent d ((R + L) (homogeneousComponent (d + 2) P)) =
      L (homogeneousComponent (d + 2) P) := by
    intro d
    have hmem := hR (d + 2) _ (homogeneousComponent_mem (d + 2) P)
    rw [LinearMap.add_apply, map_add, hL, hc_hc, if_pos rfl,
      homogeneousComponent_of_mem hmem]
    split_ifs with hc
    · exact absurd hc (by omega)
    · rw [zero_add]
  have hsupp : (Function.support fun d => L (homogeneousComponent (d + 2) P)) ⊆
      ↑(Finset.range (P.totalDegree + 1)) := by
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hd
    have h0 : homogeneousComponent (d + 2) P = 0 := by
      apply homogeneousComponent_eq_zero
      omega
    rw [h0, map_zero]
  rw [FockH1Action.minusPart, finsum_congr hterm, finsum_eq_sum_of_support_subset _ hsupp]
  calc ∑ d ∈ Finset.range (P.totalDegree + 1), L (homogeneousComponent (d + 2) P)
      = ∑ i ∈ Finset.range (P.totalDegree + 1 + 1 + 1), L (homogeneousComponent i P) := by
        rw [Finset.sum_range_succ' _ (P.totalDegree + 1 + 1),
          Finset.sum_range_succ' _ (P.totalDegree + 1),
          apply_homogeneousComponent_eq_zero_of_lt_two L hL P 0 (by norm_num)]
        simp only [zero_add, apply_homogeneousComponent_eq_zero_of_lt_two L hL P 1 (by norm_num), add_zero]
        try rfl
    _ = L P := by
        rw [← map_sum L, sum_hc_of_le P (P.totalDegree + 1 + 1 + 1) (by omega)]
end FockRaiseLowGrade
