-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.phase_function_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:44:00.553801+00:00
-- url     : https://prove2.me/submissions/10cf01af-c093-49a2-aecd-9357f55b8646

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hsK_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hs_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_aesm_of_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_sgs_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_inSS_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_inSS_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_rho_norm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.B5
namespace _root_.Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B.StepPhBound := by
  intro k r Wp Wq _ _ _ _ _ _ D Ξ A hCB
  obtain ⟨C, hC⟩ := hCB
  refine ⟨hsK Wp Wq * max C 0, fun F F' c c' hF hF' p hp => ?_⟩
  have hK : 0 ≤ hsK Wp Wq := hsK_nonneg
  have hb : ∀ g ∈ GV k r, gN g ^ A * ‖F g‖ ≤ c := fun g hg => by
    have h0 := hF.2 [] [] (by simp) (by simp) (by simp) g hg
    first
    | exact h0
    | simpa [dLR] using h0
    | simpa [dLR, Rw] using h0
  have hb' : ∀ g ∈ GV k r, gN g ^ A * ‖F' g‖ ≤ c' := fun g hg => by
    have h0 := hF'.2 [] [] (by simp) (by simp) (by simp) g hg
    first
    | exact h0
    | simpa [dLR] using h0
    | simpa [dLR, Rw] using h0
  have h1G : (1 : Mat k r) ∈ GV k r := by
    show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  have hc : 0 ≤ c :=
    le_trans (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)) (hb 1 h1G)
  have hc' : 0 ≤ c' :=
    le_trans (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)) (hb' 1 h1G)
  have mF : AEStronglyMeasurable (fun g : Mt k r => F (Matrix.of g)) D.μG :=
    aesm_of_continuousOn D.haarG (ckOn_continuousOn hF.1)
  have mF' : AEStronglyMeasurable (fun g : Mt k r => F' (Matrix.of g)) D.μG :=
    aesm_of_continuousOn D.haarG (ckOn_continuousOn hF'.1)
  have hx := inSS_left D hp
  have hy := inSS_right D hp
  have hL := hC F F' c c' mF mF' hb hb' _ hx _ hy
  have hpt : ∀ g : Mt k r, ENNReal.ofReal ‖hsInner (rho D p F (Matrix.of g)) (F' (Matrix.of g))‖ ≤
      ENNReal.ofReal (hsK Wp Wq) *
        (‖F ((Matrix.of p.1.2 * Matrix.of p.1.1)⁻¹ * Matrix.of g * (Matrix.of p.2.2 * Matrix.of p.2.1))‖ₑ *
          ‖F' (Matrix.of g)‖ₑ) := by
    intro g
    have e1 := hs_norm_le (rho D p F (Matrix.of g)) (F' (Matrix.of g))
    have e2 := rho_norm_le D hp F (Matrix.of g)
    rw [sgs_eq] at e2
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _),
      ← ENNReal.ofReal_mul hK]
    apply ENNReal.ofReal_le_ofReal
    exact e1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e2 (norm_nonneg _)) hK)
  have hlint : (∫⁻ g : Mt k r, ENNReal.ofReal ‖hsInner (rho D p F (Matrix.of g)) (F' (Matrix.of g))‖ ∂D.μG) ≤
      ENNReal.ofReal (hsK Wp Wq) * (ENNReal.ofReal (C * c * c') * Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) *
        Ξ (Matrix.of p.2.2 * Matrix.of p.2.1)) := by
    calc _ ≤ ∫⁻ g : Mt k r, ENNReal.ofReal (hsK Wp Wq) *
            (‖F ((Matrix.of p.1.2 * Matrix.of p.1.1)⁻¹ * Matrix.of g * (Matrix.of p.2.2 * Matrix.of p.2.1))‖ₑ *
              ‖F' (Matrix.of g)‖ₑ) ∂D.μG := lintegral_mono hpt
      _ = ENNReal.ofReal (hsK Wp Wq) * ∫⁻ g : Mt k r,
            ‖F ((Matrix.of p.1.2 * Matrix.of p.1.1)⁻¹ * Matrix.of g * (Matrix.of p.2.2 * Matrix.of p.2.1))‖ₑ *
              ‖F' (Matrix.of g)‖ₑ ∂D.μG := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr
  have hM : 0 ≤ max C 0 * c * c' := mul_nonneg (mul_nonneg (le_max_right _ _) hc) hc'
  have hMx : 0 ≤ max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) :=
    mul_nonneg hM (NNReal.coe_nonneg _)
  have hR : 0 ≤ hsK Wp Wq * max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) *
      (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ) := by
    have e : hsK Wp Wq * max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) *
        (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ) =
        hsK Wp Wq * (max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) *
          (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ)) := by ring
    rw [e]
    exact mul_nonneg hK (mul_nonneg hMx (NNReal.coe_nonneg _))
  unfold Ph
  refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_le_of_le_ofReal hR (hlint.trans ?_))
  have hle : C * c * c' ≤ max C 0 * c * c' :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hc) hc'
  calc ENNReal.ofReal (hsK Wp Wq) * (ENNReal.ofReal (C * c * c') * Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) *
        Ξ (Matrix.of p.2.2 * Matrix.of p.2.1))
      ≤ ENNReal.ofReal (hsK Wp Wq) * (ENNReal.ofReal (max C 0 * c * c') *
          Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) * Ξ (Matrix.of p.2.2 * Matrix.of p.2.1)) := by
        have h' : ENNReal.ofReal (C * c * c') ≤ ENNReal.ofReal (max C 0 * c * c') := ENNReal.ofReal_le_ofReal hle
        gcongr ENNReal.ofReal (hsK Wp Wq) * (?_ * _ * _)
    _ = ENNReal.ofReal (hsK Wp Wq * max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) *
          (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ)) := by
        rw [show hsK Wp Wq * max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) *
            (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ) =
            hsK Wp Wq * (max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) *
              (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ)) by ring,
          ENNReal.ofReal_mul hK, ENNReal.ofReal_mul hMx, ENNReal.ofReal_mul hM,
          ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
end _root_.Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P.B5
