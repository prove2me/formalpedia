-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.induction_all_levels
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:41:33.396085+00:00
-- url     : https://prove2.me/submissions/c221879d-3928-467c-9147-28d66b6ca595

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivedCoefficientIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
private theorem le_claimAll_proof : Formalism.FourierDecayAlt.LE.ClaimAll := by
  intro hStep hInd S σ CR Cd CP hσ hCR hCd hCP hL hbig hJL2 hImp
  refine hInd S hJL2 ?_
  intro w Y hOn hlen hint
  have hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w := hOn
  have hY : Y ∈ (S.step w).J := by
    show Y ∈ Set.Icc (S.step w).a ((S.step w).a + (S.step w).L)
    rw [S.step_a, S.step_L]
    exact hOn'.1
  have hst := hStep S.B (S.step w) S.c σ CR Cd CP hσ hCR hCd hCP (by rw [S.step_L]; exact hL)
    (by rw [S.step_r, S.step_L]; exact hbig) (hImp w hOn'.2 hlen) hint Y hY
  have hfun : S.dens (Y :: w) = fun ω => Formalism.FourierDecayAlt.LE.sq S.B ((S.step w).d Y) ((S.step w).gX Y) ω :=
    funext (S.step_new w Y)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hst.1
  · calc ∫ ω, S.dens (Y :: w) ω ∂S.B.μ
        = ∫ ω, Formalism.FourierDecayAlt.LE.sq S.B ((S.step w).d Y) ((S.step w).gX Y) ω ∂S.B.μ := by rw [hfun]
      _ = |(S.step w).P Y| * (S.step w).A0 := hst.2
      _ = |S.P Y| * ∫ ω, S.dens w ω ∂S.B.μ := by
        rw [S.step_P]
        rfl
end Formalism.FourierDecayAlt.P.LEx2
end

set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.LE.ClaimAll := Formalism.FourierDecayAlt.P.LEx2.le_claimAll_proof
end Formalism.FourierDecayAlt.P
