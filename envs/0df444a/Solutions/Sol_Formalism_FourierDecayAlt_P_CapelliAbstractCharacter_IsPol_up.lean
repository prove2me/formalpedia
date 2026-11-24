-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.IsPol.up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:58:29.328636+00:00
-- url     : https://prove2.me/submissions/6a891226-64d6-4338-88e4-3c3a1501e618

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
theorem _root_.solution {d : ℕ} {f : ℂ → X} (hf : IsPol d f) : IsPol (d + 1) f := by
  obtain ⟨c, h⟩ := hf
  refine ⟨fun s => if s < d then c s else 0, fun u => ?_⟩
  rw [Finset.sum_range_succ, h u]
  simp only [lt_irrefl, if_false, smul_zero, add_zero]
  exact Finset.sum_congr rfl (fun s hs => by rw [if_pos (Finset.mem_range.mp hs)])
end IsPol
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
