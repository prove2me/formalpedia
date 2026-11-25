-- Prove2me | solution 1 for CompanionTheory.Bmu.psiGen_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:18:47.739278+00:00
-- url     : https://prove2.me/submissions/38c8e8da-1ca8-40bd-9cc5-992079cb3ee1

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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin r → ℂ) :
    PI.BesselMapUniq.psiGen k r z c 1 = 1 := by
  have h : ∀ a, PI.BesselMapUniq.ellA k r z 1 a = 0 := by
    intro a
    unfold PI.BesselMapUniq.ellA
    split_ifs with h
    · refine Matrix.one_apply_ne fun e => ?_
      have := congrArg Fin.val e
      simp [eI] at this
    · rw [one_mulVec]
      exact hz _ (Or.inl a.2)
  simp [PI.BesselMapUniq.psiGen, h]
end CompanionTheory.Bmu
