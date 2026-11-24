-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.vol_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:37:40.439081+00:00
-- url     : https://prove2.me/submissions/af88e1ee-a829-406b-a8d1-db4065b4c29f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_mp
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_trick
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Mv_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Lv_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Mv_lt_top
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Mv_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (F : Frame H Ep Em) (hH : IsUnit H.det) (μ : Measure (m → m → ℂ)) [SFinite μ]
    (conc : ∀ᵐ g ∂μ, Matrix.of g ∈ UH H)
    (left : ∀ a ∈ UH H, μ.map (lmF a) = μ) (right : ∀ a ∈ UH H, μ.map (rmF a) = μ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    μ (Bset Ep Em ρ) = μ (invF ⁻¹' Bset Ep Em 1) * ENNReal.ofReal (ρ ^ (2 * Fintype.card P * Fintype.card Q)) := by
  obtain ⟨c, hc, hL⟩ := Lv_eq F
  have h := trick F hH μ conc left right ρ
  rw [hL 1, hL ρ, Mv_scale hρ] at h
  have hne : (c : ℝ≥0∞) * Mv P Q 1 ≠ 0 := mul_ne_zero (ENNReal.coe_ne_zero.mpr hc.ne') Mv_pos.ne'
  have hnt : (c : ℝ≥0∞) * Mv P Q 1 ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top Mv_lt_top.ne
  have h' : (c : ℝ≥0∞) * Mv P Q 1 * μ (Bset Ep Em ρ) = (c : ℝ≥0∞) * Mv P Q 1 *
      (μ (invF ⁻¹' Bset Ep Em 1) * ENNReal.ofReal (ρ ^ (2 * Fintype.card P * Fintype.card Q))) := by
    rw [h]; ring
  exact (ENNReal.mul_right_inj hne hnt).mp h'
end Formalism.FourierDecayAlt.P.HermitianFormFactor
