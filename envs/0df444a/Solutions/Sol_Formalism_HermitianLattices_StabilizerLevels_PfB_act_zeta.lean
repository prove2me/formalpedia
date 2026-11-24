-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.act_zeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:16:23.052104+00:00
-- url     : https://prove2.me/submissions/f6db829d-68d9-4fbe-8d7c-9867dfdab311

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IntermediateField
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution (h : IsLayer (e + 2) q d ζ a b) (τ : Gal(L/ℚ)) (k : ℕ)
    (hk : (k : ZMod (2 ^ (e + 2))) = ((galMap h.1 a b τ).1 : ZMod (2 ^ (e + 2)))) : τ ζ = ζ ^ k := by
  have := h.1.autToPow_spec ℚ τ
  rw [← this]
  have e1 : ((h.1.autToPow ℚ τ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = (k : ZMod (2 ^ (e + 2))) :=
    hk.symm
  rw [e1, ZMod.val_natCast]
  exact (pow_eq_pow_mod k h.1.pow_eq_one).symm
end Formalism.HermitianLattices.StabilizerLevels.PfB
