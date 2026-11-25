-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.model_integral_first_error
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:18:54.338899+00:00
-- url     : https://prove2.me/submissions/e562f278-f13b-4388-8157-437338420959

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_cut_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_quad_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_wt_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_sqrt_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_sqrt_le_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_est
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_ph_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_modelAmplitude_eq_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_constant_amplitude_symbol
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_linear_amplitude_symbol
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_cut_smul_tsupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_cut_smul_compact
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_integral_odd
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_osc_quad_neg
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_sym__920f37ab2922
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_Pe_sym__647cdd861ec3
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_cut_continuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {d : ℕ} {β : ℂ} {r Γ c₁ ρ τ Cχ S : ℝ} {φ : (Fin d → ℂ) → ℝ}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {a₀ : V} {ℓ : (Fin d → ℂ) →L[ℝ] V}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {C : ℝ} (hβ : β ≠ 0) (hOB : E_OB d 2 β (Γ + Γ * (r + 1) ^ (d + 5)) (c₁ / 2) C)
    (hr : 0 < r) (hΓ : 0 < Γ) (hph : E_Phase d r Γ c₁ φ) (hρ0 : 0 < ρ) (hρr : ρ ≤ r)
    (hρ : (Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6) * ρ ≤ c₁ / 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hCχ : 0 ≤ Cχ) (hC : ∀ i : ℕ, i ≤ d + 6 → ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ Cχ)
    (ha : ‖a₀‖ ≤ S) (hl : ‖ℓ‖ ≤ S) :
    ‖∫ x, osc (quad φ) τ x • (E_P φ x • modelAmplitude d ρ a₀ ℓ x) ∂(muPi β (Fin d))‖ ≤
      2 * (C * (2 ^ (d + 1 + 2) * ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) *
        (2 ^ (d + 1 + 2) * (Cχ * (ρ + 1) ^ (d + 1 + 2)) * S)) * τ ^ (d + 2)) := by
  have hS : 0 ≤ S := (norm_nonneg _).trans ha
  have hw : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) ρ, 0 < wt (Real.sqrt τ) x :=
    fun x _ => E_wt_pos (E_sqrt_pos hτ) x
  have hs0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hφc : Continuous φ := hph.smooth.continuous
  have hqc : Continuous (quad φ) := (E_quad_contDiff φ 0).continuous
  have hPc : Continuous (E_P φ) := hφc.sub hqc
  have hPn : Continuous (fun x => E_P φ (-x)) := hPc.comp continuous_neg
  have hPec : Continuous (E_Pe φ) := continuous_const.mul (hPc.add hPn)
  have hχc := E_cut_continuous (d := d) hρ0
  have hb0c : Continuous (constantAmplitude d ρ a₀) := hχc.smul continuous_const
  have hb1c : Continuous (linearAmplitude d ρ ℓ) := hχc.smul ℓ.continuous
  have hb0s : HasCompactSupport (constantAmplitude d ρ a₀) := E_cut_smul_compact hρ0 _
  have hb1s : HasCompactSupport (linearAmplitude d ρ ℓ) := E_cut_smul_compact hρ0 _

  have hPe := E_Pe_sym' (N := d + 1 + 2) hr hph hρr hτ hτ1 (by omega)
  have hP := E_P_sym' (N := d + 1 + 2) hr hph hρr hτ hτ1 (by omega)
  have hB0 := constant_amplitude_symbol (N := d + 1 + 2) (a₀ := a₀) hρ0 (fun i hi => hC i (by omega)) hρ0 (E_sqrt_pos hτ)
    (E_sqrt_le_one hτ1) ha
  have hB1 := linear_amplitude_symbol (N := d + 1 + 2) (ℓ := ℓ) hρ0 (fun i hi => hC i (by omega)) hρ0 (E_sqrt_pos hτ)
    (E_sqrt_le_one hτ1) hl
  have h0 := Sym.smul hw hPe hB0
  have h1 := Sym.smul hw hP hB1
  have e0 : ((4 : ℤ) + 0) = 2 * ((2 : ℕ) : ℤ) := by norm_num
  have e1 : ((3 : ℤ) + 1) = 2 * ((2 : ℕ) : ℤ) := by norm_num
  rw [e0] at h0
  rw [e1] at h1
  have k0 := E_est (q := 2) (by norm_num) hOB hr hph hρr hρ hτ hτ1 hs0 _ _ (by positivity)
    (hb0s.smul_left (f := E_Pe φ)) ((tsupport_smul_subset_right _ _).trans (E_cut_smul_tsupport hρ0 _)) h0
  have k1 := E_est (q := 2) (by norm_num) hOB hr hph hρr hρ hτ hτ1 hs0 _ _ (by positivity)
    (hb1s.smul_left (f := E_P φ)) ((tsupport_smul_subset_right _ _).trans (E_cut_smul_tsupport hρ0 _)) h1
  rw [E_ph_zero] at k0 k1

  have hodd : ∫ x, osc (quad φ) τ x • (((1 / 2 : ℝ) * (E_P φ x - E_P φ (-x))) • constantAmplitude d ρ a₀ x)
      ∂(muPi β (Fin d)) = 0 := by
    refine E_integral_odd hβ _ fun x => ?_
    rw [E_osc_quad_neg]
    simp only [constantAmplitude, E_cut_neg hρ0, neg_neg]
    rw [← smul_neg, ← neg_smul]
    congr 2
    ring
  have hsplit : ∀ x, osc (quad φ) τ x • (E_P φ x • modelAmplitude d ρ a₀ ℓ x) =
      (osc (quad φ) τ x • (E_Pe φ x • constantAmplitude d ρ a₀ x) +
        osc (quad φ) τ x • (((1 / 2 : ℝ) * (E_P φ x - E_P φ (-x))) • constantAmplitude d ρ a₀ x)) +
        osc (quad φ) τ x • (E_P φ x • linearAmplitude d ρ ℓ x) := by
    intro x
    rw [modelAmplitude_eq_add, ← smul_add, ← add_smul, ← smul_add, smul_add (E_P φ x)]
    congr 3
    unfold E_Pe
    ring
  simp_rw [hsplit]
  have i0 : Integrable (fun x => osc (quad φ) τ x • (E_Pe φ x • constantAmplitude d ρ a₀ x)) (muPi β (Fin d)) :=
    E_integrable (τ := τ) hβ hqc (hPec.smul hb0c) (hb0s.smul_left (f := E_Pe φ))
  have i1 : Integrable (fun x => osc (quad φ) τ x • (((1 / 2 : ℝ) * (E_P φ x - E_P φ (-x))) • constantAmplitude d ρ a₀ x))
      (muPi β (Fin d)) := E_integrable (τ := τ) hβ hqc
    ((continuous_const.mul (hPc.sub hPn) : Continuous fun x => (1 / 2 : ℝ) * (E_P φ x - E_P φ (-x))).smul hb0c)
    (hb0s.smul_left (f := fun x => (1 / 2 : ℝ) * (E_P φ x - E_P φ (-x))))
  have i2 : Integrable (fun x => osc (quad φ) τ x • (E_P φ x • linearAmplitude d ρ ℓ x)) (muPi β (Fin d)) :=
    E_integrable (τ := τ) hβ hqc (hPc.smul hb1c) (hb1s.smul_left (f := E_P φ))
  have i01 : Integrable (fun x => osc (quad φ) τ x • (E_Pe φ x • constantAmplitude d ρ a₀ x) +
      osc (quad φ) τ x • (((1 / 2 : ℝ) * (E_P φ x - E_P φ (-x))) • constantAmplitude d ρ a₀ x)) (muPi β (Fin d)) := i0.add i1
  rw [integral_add i01 i2, integral_add i0 i1, hodd, add_zero]
  refine (norm_add_le _ _).trans ?_
  rw [two_mul]
  exact add_le_add k0 k1
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
