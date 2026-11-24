-- Prove2me | solution 1 for FockRaiseLowGrade.plus_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:07.950802+00:00
-- url     : https://prove2.me/submissions/2b758d8b-327e-4a4d-b0e8-516737ea49b1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit
import Theorems.Thm_FockRaiseLowGrade_hc_hc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    (P : MvPolynomial σ ℂ) : plusPart (R + L) P = R P := by
  classical
  have hterm : ∀ d, homogeneousComponent (d + 2) ((R + L) (homogeneousComponent d P)) =
      R (homogeneousComponent d P) := by
    intro d
    have hmem := hR d _ (homogeneousComponent_mem d P)
    rw [LinearMap.add_apply, map_add, hL, hc_hc,
      if_neg (show ¬ (d + 2 + 2 = d) by omega), map_zero, add_zero,
      homogeneousComponent_of_mem hmem, if_pos rfl]
  have hsupp : (Function.support fun d => R (homogeneousComponent d P)) ⊆
      ↑(Finset.range (P.totalDegree + 1)) := by
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hd
    have h0 : homogeneousComponent d P = 0 := by
      apply homogeneousComponent_eq_zero
      omega
    rw [h0, map_zero]
  rw [FockH1Action.plusPart, finsum_congr hterm, finsum_eq_sum_of_support_subset _ hsupp,
    ← map_sum R, sum_homogeneousComponent]
end FockRaiseLowGrade
