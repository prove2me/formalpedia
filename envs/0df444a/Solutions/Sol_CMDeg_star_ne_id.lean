-- Prove2me | solution 1 for CMDeg.star_ne_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:44.904599+00:00
-- url     : https://prove2.me/submissions/ac0ad925-0f6a-4d77-aab3-70464718c927

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_MassRatio
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDegreeEquality_FinrankEqTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open CMDeg
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
namespace CMDeg
theorem _root_.solution (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) : ∃ a : E, star a ≠ a := by
  by_contra h
  simp only [not_exists, not_not] at h
  have : IsTotallyComplex E := hE.1
  let φ : E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding
  apply IsTotallyComplex.complexEmbedding_not_isReal φ
  rw [ComplexEmbedding.isReal_iff]
  ext a
  show starRingEnd ℂ (φ a) = φ a
  rw [← hE.2.1 φ a, h a]
end CMDeg
