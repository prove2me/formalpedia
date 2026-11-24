-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.IsPol.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:59:28.815793+00:00
-- url     : https://prove2.me/submissions/bd992a20-5893-4484-a717-35446bf0d3ca

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
theorem _root_.solution {d : ℕ} {f g : ℂ → X} (hf : IsPol d f) (hg : IsPol d g) : IsPol d (fun u => f u + g u) := by
  obtain ⟨c1, h1⟩ := hf
  obtain ⟨c2, h2⟩ := hg
  exact ⟨fun s => c1 s + c2 s, fun u => by simp only [h1 u, h2 u, smul_add, Finset.sum_add_distrib]⟩
end IsPol
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
