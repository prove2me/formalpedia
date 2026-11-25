-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.tendsto_smul_cocompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:34.493196+00:00
-- url     : https://prove2.me/submissions/b8d1cc9b-3274-4cfe-8195-019c7a6a245e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralPsiMoving
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {α : Type} {l : Filter α} (c : ℂ) (hc : c ≠ 0) (y : α → ℂ)
    (hy : Tendsto y l (cocompact ℂ)) : Tendsto (fun a => c * y a) l (cocompact ℂ) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded] at hy ⊢
  simp only [norm_mul]
  exact hy.const_mul_atTop (norm_pos_iff.mpr hc)
end Formalism.FourierDecayAlt.P.PBK
