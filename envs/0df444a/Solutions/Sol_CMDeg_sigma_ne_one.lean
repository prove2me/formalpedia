-- Prove2me | solution 1 for CMDeg.sigma_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:24.424576+00:00
-- url     : https://prove2.me/submissions/f24aea31-3791-48bf-9de1-b44e91dede84

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_MassRatio
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDegreeEquality_FinrankEqTwo
import Theorems.Thm_CMDeg_sigma_apply
import Theorems.Thm_CMDeg_star_ne_id

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
theorem _root_.solution (hE : Formalism.HermitianLatticesTheory.IsCMUnram E)
    (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) : sigma hfix ≠ 1 := by
  intro h1
  obtain ⟨a, ha⟩ := star_ne_id hE
  apply ha
  have := congrArg (fun g : E ≃ₐ[F] E => g a) h1
  simpa [sigma_apply] using this
end CMDeg
