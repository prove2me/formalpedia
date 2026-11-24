-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.mean_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:45:21.290797+00:00
-- url     : https://prove2.me/submissions/35456dcb-5a1e-481b-9771-f259fe2ae32b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_hasDerivAt_cv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {H : Mat k r → E} (hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H) {Z g : Mat k r}
    (hZ : inLie k r Z) (hg : g ∈ GV k r) (b : Bool) {lm B L : ℝ} (hlm : 0 ≤ lm)
    (hB : ∀ σ : ℝ, |σ| ≤ L → lm * ‖op b Z H (cv b Z σ g)‖ ≤ B) {s : ℝ} (hs : |s| ≤ L) :
    lm * ‖H (cv b Z s g) - H g‖ ≤ B * |s| := by
  have hL : 0 ≤ L := le_trans (abs_nonneg s) hs
  have hB0 : 0 ≤ B :=
    le_trans (mul_nonneg hlm (norm_nonneg _)) (hB 0 (by rw [abs_zero]; exact hL))
  rcases eq_or_lt_of_le hlm with h0 | hpos
  · rw [← h0, zero_mul]
    exact mul_nonneg hB0 (abs_nonneg s)
  · have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun σ => H (cv b Z σ g)) (f' := fun σ => op b Z H (cv b Z σ g)) (C := B / lm)
      (s := Set.Icc (-L) L)
      (fun x _ => (hasDerivAt_cv hH hZ hg b x).hasDerivWithinAt)
      (fun x hx => by
        rw [le_div_iff₀ hpos, mul_comm]
        exact hB x (abs_le.mpr hx))
      (convex_Icc _ _) (show (0 : ℝ) ∈ Set.Icc (-L) L from ⟨by linarith, hL⟩)
      (show s ∈ Set.Icc (-L) L from abs_le.mp hs)
    simp only [sub_zero, Real.norm_eq_abs] at hmv
    rw [cv_zero] at hmv
    have hne : lm ≠ 0 := hpos.ne'
    calc lm * ‖H (cv b Z s g) - H g‖ ≤ lm * (B / lm * |s|) := mul_le_mul_of_nonneg_left hmv hlm
      _ = B * |s| := by
        first
          | (field_simp; done)
          | (field_simp; ring)
end Formalism.FourierDecayAlt.P.B4
