-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Cx2.re_cj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:15:41.806301+00:00
-- url     : https://prove2.me/submissions/79936156-36d8-4bae-a5e5-3b36868bfc54

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
theorem _root_.solution (S : HidaSetting E Wp Wq) (c : J.CV E) (l : E) (v : Fin S.f) :
    (S.σ v l * cj S c (S.pl v)).re = ((S.pl v).embedding l * c (S.pl v)).re := by
  by_cases h : S.σ v = (S.pl v).embedding
  · rw [(cj_apply S c v).1 h, h]
  · rw [(cj_apply S c v).2 h]
    rcases σ_or S v with h' | h'
    · exact absurd h' h
    · rw [← h', ComplexEmbedding.conjugate_coe_eq]
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
end Formalism.FourierDecayAlt.P.Cx2
