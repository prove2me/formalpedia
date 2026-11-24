-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.W_mem_Wall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:38:51.066137+00:00
-- url     : https://prove2.me/submissions/f6bbbac1-7746-4534-bc98-c28ef61485dc

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_W_mem_wall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
open Classical
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution (w0 : S.W) : w0 ∈ S.base.Wall := by
  unfold C.HidaSetting.base C.HidaSetting.mkData
  dsimp only
  rw [Finset.mem_subtype]
  exact W_mem_wall S w0
end Formalism.FourierDecayAlt.P.PBA
