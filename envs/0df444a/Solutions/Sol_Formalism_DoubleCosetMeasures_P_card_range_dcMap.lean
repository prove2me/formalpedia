-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.card_range_dcMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:51.88709+00:00
-- url     : https://prove2.me/submissions/121dca47-e043-4056-acd0-1aacfdfa1a8f

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_dcMap_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
variable {G : Type} [Group G]
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution (K₀ : Subgroup G) (g : G) :
    Nat.card (Set.range (dcMap K₀ g)) = (K₀.map (MulAut.conj g).toMonoidHom).relIndex K₀ := by
  have hker : Setoid.ker (dcMap K₀ g) =
      QuotientGroup.leftRel ((K₀.map (MulAut.conj g).toMonoidHom).subgroupOf K₀) := by
    ext k k'
    rw [Setoid.ker_def, QuotientGroup.leftRel_apply]
    exact dcMap_eq_iff K₀ g k k'
  rw [Subgroup.relIndex, Subgroup.index,
    ← Nat.card_congr (Setoid.quotientKerEquivRange (dcMap K₀ g)), hker]
  rfl
end Formalism.DoubleCosetMeasures.P
