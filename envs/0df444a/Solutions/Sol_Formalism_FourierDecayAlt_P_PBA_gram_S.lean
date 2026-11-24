-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.gram_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:08:36.35382+00:00
-- url     : https://prove2.me/submissions/7913bdf3-09c6-4c2a-907d-9cd9e751f9ff

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalNormNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
  (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution (ε : ℝ) (i : ℕ) (w : C.Word S.f) (p q : TB.Pt E) :
    S.gram ε i w p q = if i ≤ S.G.r + 1 then ∏ v, ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G
      (C.loc (S.σ v) p)) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) q)) : ℝ) : ℂ) *
        (S.pd v).RR ε i (w v) (C.loc (S.σ v) p) (C.loc (S.σ v) q) else 0 := rfl
end Formalism.FourierDecayAlt.P.PBA
