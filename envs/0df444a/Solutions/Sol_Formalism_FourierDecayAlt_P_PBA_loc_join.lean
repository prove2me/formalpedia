-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.loc_join
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:57:31.345704+00:00
-- url     : https://prove2.me/submissions/f471044b-86e5-4db8-b387-4a9e8c8d90f7

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SizeAtNonneg

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
theorem _root_.solution (σ : E →+* ℂ) (h : TB.Pt E) (s : ℕ) (t : E) :
    C.loc σ (TB.join h s t) = C.loc σ h ++ [(s, σ t)] := by
  simp only [C.loc, TB.join, List.map_append, List.map_cons, List.map_nil]
end Formalism.FourierDecayAlt.P.PBA
