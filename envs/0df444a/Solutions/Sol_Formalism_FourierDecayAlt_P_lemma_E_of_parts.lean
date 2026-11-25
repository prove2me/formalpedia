-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lemma_E_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:44:18.647824+00:00
-- url     : https://prove2.me/submissions/77b6289b-994e-42cd-b2db-d5bdf22f21a1

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
private theorem le_eFromConstituents_proof : Formalism.FourierDecayAlt.LE.LemmaEFromSteps := by
  intro hConst hRed hGrid hSign hFit hAll hStep hInd hBL hLB hLA hLL2 hPL hCL2 hLeib hCut
  intro CR Cd CP hCR hCd hCP C₂ hC₂ C₆ hC₆ S hN hL hI hRO hI1 hJL2 hThm hImp hFam
  have hC₂64 : 64 ≤ C₂ :=
    le_trans (le_mul_of_one_le_right (by norm_num) (le_add_of_nonneg_right (by positivity))) hC₂
  have hN1' : 1 ≤ S.Ntot := by omega
  have hN1 : (1:ℝ) ≤ S.Ntot := by exact_mod_cast hN1'
  have hr0 : (0:ℝ) ≤ S.r := Nat.cast_nonneg _
  have hQ : (1:ℝ) ≤ ((S.r:ℝ) + 1) ^ 2 := by nlinarith
  have hNQ : (1:ℝ) ≤ (S.Ntot:ℝ) * ((S.r:ℝ) + 1) ^ 2 := by nlinarith
  have hNQ0 : (0:ℝ) ≤ (S.Ntot:ℝ) * ((S.r:ℝ) + 1) ^ 2 := by linarith
  have hL64 : 64 ≤ S.L := by
    rw [hL]
    nlinarith [mul_le_mul hC₂64 hNQ (by norm_num) (by linarith)]
  have hL2 : 2 < S.L := by linarith
  have hL0 : 0 < S.L := by linarith
  obtain ⟨-, -, h6⟩ := hConst S.k S.r S.Ntot C₂ C₆ (S.β - S.α) hN (by linarith) hC₆ hI
  have hfit : 6 * (S.Ntot:ℝ) * S.L ≤ S.β - S.α := by
    rw [hL]
    linarith
  have hσ : (4:ℝ) ≤ 4 * (S.Ntot:ℝ) := by linarith
  have hclaims := hAll hStep hInd S (4 * (S.Ntot:ℝ)) CR Cd CP hσ hCR hCd hCP hL0
    (by rw [hL]; nlinarith [mul_le_mul_of_nonneg_right hC₂ hNQ0]) hJL2 hImp
  have hBox := hBL hLB hLA hLL2 hPL hCL2 hLeib hCut S hL0 hFam hThm hclaims
  exact hRed hGrid hSign hFit S hL2 hfit hRO hI1 hBox
end Formalism.FourierDecayAlt.P.LEx2
end

set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.LE.LemmaEFromSteps := Formalism.FourierDecayAlt.P.LEx2.le_eFromConstituents_proof
end Formalism.FourierDecayAlt.P
