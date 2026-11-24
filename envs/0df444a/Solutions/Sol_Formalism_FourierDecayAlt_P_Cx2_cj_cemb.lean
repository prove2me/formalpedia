-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Cx2.cj_cemb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:42:35.549871+00:00
-- url     : https://prove2.me/submissions/7113ebf7-362b-45b1-bd23-90bd2ad5c235

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstNormRealNonneg
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Cx2___or_c4f8023df5f0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_cj_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C NumberField MeasureTheory
open scoped ComplexOrder ComplexConjugate RealInnerProductSpace
noncomputable section
open Formalism.FourierDecayAlt.P.Cx2
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {Wp Wq : InfinitePlace E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.Cx2
theorem _root_.solution (S : HidaSetting E Wp Wq) (t : E) (v : Fin S.f) : cj S (J.cemb E t) (S.pl v) = S.σ v t := by
  have hc : J.cemb E t (S.pl v) = (S.pl v).embedding t := rfl
  by_cases h : S.σ v = (S.pl v).embedding
  · rw [(cj_apply S _ v).1 h, hc, h]
  · rw [(cj_apply S _ v).2 h, hc]
    rcases σ_or S v with h' | h'
    · exact absurd h' h
    · rw [← h', ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
end Formalism.FourierDecayAlt.P.Cx2
