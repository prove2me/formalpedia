-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.doubleCoset_eq_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:05.632647+00:00
-- url     : https://prove2.me/submissions/2a45685e-2baa-415e-8c61-da55cab832d9

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage

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
    DoubleCoset.doubleCoset g (K₀ : Set G) K₀ =
      (QuotientGroup.mk : G → G ⧸ K₀) ⁻¹' Set.range (dcMap K₀ g) := by
  ext y
  rw [DoubleCoset.mem_doubleCoset]
  simp only [Set.mem_preimage, Set.mem_range, dcMap, SetLike.mem_coe]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using hb
  · rintro ⟨k, hk⟩
    rw [QuotientGroup.eq] at hk
    exact ⟨k, k.2, _, hk, by group⟩
end Formalism.DoubleCosetMeasures.P
