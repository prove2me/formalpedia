-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.IsPol.shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:00:50.788874+00:00
-- url     : https://prove2.me/submissions/58f0b3b2-b0a8-440b-a121-52a144b625c9

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
namespace IsPol
theorem _root_.solution {d : ℕ} {f : ℂ → X} (hf : IsPol d f) : IsPol (d + 1) (fun u => u • f u) := by
  obtain ⟨c, h⟩ := hf
  refine ⟨shiftC c, fun u => ?_⟩
  show u • f u = _
  rw [Finset.sum_range_succ', h u, Finset.smul_sum]
  simp only [shiftC, smul_zero, add_zero]
  exact Finset.sum_congr rfl (fun s _ => by rw [pow_succ', mul_smul])
end IsPol
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
