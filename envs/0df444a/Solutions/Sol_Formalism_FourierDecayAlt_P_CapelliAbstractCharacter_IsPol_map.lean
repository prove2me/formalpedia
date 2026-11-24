-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.IsPol.map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:58:16.578115+00:00
-- url     : https://prove2.me/submissions/701b9c80-e754-4707-a12b-062006207121

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum


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
theorem _root_.solution {d : ℕ} {f : ℂ → X} (L : X →ₗ[ℂ] Y) (hf : IsPol d f) : IsPol d (fun u => L (f u)) := by
  obtain ⟨c, h⟩ := hf
  exact ⟨fun s => L (c s), fun u => by simp only [h u, map_sum, map_smul]⟩
end IsPol
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
