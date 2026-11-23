-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrkb_sq_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:02.85608+00:00
-- url     : https://prove2.me/submissions/79149e5c-346c-4832-aea2-307f7593ce42

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkbLeOneAddSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup G} [Countable Γ] {D : Set G}
omit [Group G] [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μ]
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (f : Lp ℂ 2 (μ.restrict D)) : ∫⁻ y in D, ‖(f : G → ℂ) y‖ₑ ^ 2 ∂μ ≠ ∞ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) two_ne_zero ENNReal.ofNat_ne_top
    (Lp.eLpNorm_lt_top f)
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
  exact h.ne
end Formalism.MainNotions.LeviCoordinates
