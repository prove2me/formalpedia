-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.mem_Wb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:57:09.781153+00:00
-- url     : https://prove2.me/submissions/459b8a6a-a47a-4fd6-bc73-b1c5b4b3e6db

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_W_mem_Wall__4debfb

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
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution {w0 : S.W} {n : ℕ} (h : w0.1.cnt ≤ n) : w0 ∈ S.base.Wb n := by
  unfold TB.Data.Wb
  rw [Finset.mem_filter]
  exact ⟨W_mem_Wall S w0, h⟩
end Formalism.FourierDecayAlt.P.PBA
