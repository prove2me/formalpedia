-- Prove2me | solution 1 for CompanionTheory.Bmu.one_uw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:40.910518+00:00
-- url     : https://prove2.me/submissions/0f114ae5-64f5-4f40-b92e-e20a4a02fc29

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_NormPsiGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open CompanionTheory CompanionTheory.Bmu
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace CompanionTheory.Bmu
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mat (2 * r + k + 1)) ∈ UWset k r z :=
  ⟨by simp [UH], fun _ => ⟨one_mulVec _, one_mulVec _⟩, one_mulVec _⟩
end CompanionTheory.Bmu
