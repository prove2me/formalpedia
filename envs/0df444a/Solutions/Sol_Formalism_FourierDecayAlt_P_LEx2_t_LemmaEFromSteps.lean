-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.t_LemmaEFromSteps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:33:01.018606+00:00
-- url     : https://prove2.me/submissions/2f739416-f861-4730-9325-90dac82f74b0

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : LemmaEFromSteps := by
  intro hConst hRed hGrid hSign hFit hClaimAll hStep hInd hBox hLB hLA hL2 hPair hCoef hLeib hCut
  intro CR Cd CP h1 h2 h3 C₂ hC2 C₆ hC6 S hr hL hI hRoots hI1 hJ hP hSI hFI
  have hK0 : 0 ≤ 2 * Real.exp 1 * √(C7 CR Cd CP) := by positivity
  have hC2' : 64 ≤ C₂ := by linarith
  have hN : (1:ℝ) ≤ S.Ntot := by exact_mod_cast (by omega : 1 ≤ S.Ntot)
  have hr1 : (1:ℝ) ≤ ((S.r:ℝ)+1)^2 := by
    have : (0:ℝ) ≤ S.r := Nat.cast_nonneg _
    nlinarith
  have hc := hConst S.k S.r S.Ntot C₂ C₆ (S.β - S.α) hr (by linarith) hC6 hI
  have hNr : (1:ℝ) ≤ S.Ntot * ((S.r:ℝ)+1)^2 := by nlinarith
  have hL64 : 64 ≤ S.L := by
    rw [hL, mul_assoc]; nlinarith
  have h6 : 6 * (S.Ntot:ℝ) * S.L ≤ S.β - S.α := by rw [hL]; exact hc.2.2
  apply hRed hGrid hSign hFit S (by linarith) h6 hRoots hI1
  apply hBox hLB hLA hL2 hPair hCoef hLeib hCut S (by linarith) hFI hP
  apply hClaimAll hStep hInd S (4 * S.Ntot) CR Cd CP (by linarith) h1 h2 h3 (by linarith) _ hJ hSI
  rw [hL]
  have : 64 * (1 + 2 * Real.exp 1 * √(C7 CR Cd CP)) * (S.Ntot * ((S.r:ℝ)+1)^2) ≤ C₂ * (S.Ntot * ((S.r:ℝ)+1)^2) :=
    mul_le_mul_of_nonneg_right hC2 (by linarith)
  nlinarith [this]
end Formalism.FourierDecayAlt.P.LEx2
