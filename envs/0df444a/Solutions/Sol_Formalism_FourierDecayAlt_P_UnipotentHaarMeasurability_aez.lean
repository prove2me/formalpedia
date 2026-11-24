-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.aez
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:58.618332+00:00
-- url     : https://prove2.me/submissions/86c7ce1b-443a-4703-a59b-7bb4d7e69072

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroOfAe
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_uh_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_zero_of_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_uh_cancel
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_uh_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TranslationBesselVanishing_uh_mul
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability
variable {k r : ℕ}
local notation "MX" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
local notation "UHk" => Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)
namespace Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability
theorem _root_.solution {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : MX → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hμN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (hμG : PI.BesselPeriodGGP.IsHaarOn UHk μG)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) νq)
    (F : MX → Wp) (hFc : ContinuousOn F UHk)
    (hFeq : ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ g ∈ UHk,
      F (h * n * g) = Formalism.QuantumDeterminants.psi k r z c n • π h (F g))
    (hl2 : PI.BesselPeriodGGP.l2SG νq F = 0) : ∀ g ∈ UHk, F g = 0 := by
  classical
  have := hμW.1
  have := hμN.1
  let S : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ UHk}
  let G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ :=
    S.piecewise (fun x => (‖F (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) (fun _ => 0)
  have hSm : MeasurableSet S := uh_meas
  have hc1 : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : MX)) := continuous_id
  have hGc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => (‖F (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) S := by
    have h2 : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) S :=
      hFc.comp hc1.continuousOn (fun x hx => hx)
    exact (ENNReal.continuous_pow 2).comp_continuousOn
      ((ENNReal.continuous_coe.comp continuous_nnnorm).comp_continuousOn h2)
  have hGm : Measurable G := hGc.measurable_piecewise continuousOn_const hSm
  have hGle : ∀ x, G x ≤ (‖F (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 := by
    intro x
    by_cases hx : x ∈ S
    · simp [G, hx]
    · simp [G, hx]
  have hνG : ∫⁻ x, G x ∂νq = 0 := by
    refine nonpos_iff_eq_zero.mp ?_
    calc ∫⁻ x, G x ∂νq ≤ ∫⁻ x, (‖F (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νq := lintegral_mono hGle
      _ = PI.BesselPeriodGGP.l2SG νq F := rfl
      _ = 0 := hl2
  have hGae : ∀ᵐ x ∂νq, G x = 0 := (lintegral_eq_zero_iff hGm).1 hνG
  have hGval : ∀ x, x ∈ S → G x = 0 → F (Matrix.of x) = 0 := by
    intro x hx h0
    simp only [G, Set.piecewise, hx, if_true] at h0
    have : (‖F (Matrix.of x)‖₊ : ℝ≥0∞) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
    simpa using this
  have hmul : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
    have h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : MX)) := continuous_fst
    have h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : MX)) := continuous_snd
    exact h1.matrix_mul h2
  have hW : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 hμW.2.2.1)
  have hN : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (ae_iff.2 hμN.2.2.1)
  have hμGint : ∫⁻ x, G x ∂μG = 0 := by
    rw [hQ G hGm]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hGae] with x hx
    show ∫⁻ s, G (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) = 0
    have hrm : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r =>
        G (fun i j => (Matrix.of s * Matrix.of x) i j)) :=
      hGm.comp ((show Continuous (fun s : Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => (Matrix.of s * Matrix.of x) i j : Formalism.QuantumDeterminants.Mt k r)) from
          hc1.matrix_mul continuous_const).measurable)
    rw [Formalism.FourierDecayAlt.ThreeDimData.muSof, lintegral_map hrm hmul.measurable]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hW, hN] with p hp1 hp2
    have hsU : Matrix.of p.1 * Matrix.of p.2 ∈ UHk := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hp1.1 hp2.1
    show G (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) * Matrix.of x) i j) = 0
    by_cases hxU : x ∈ S
    · have hFx := hGval x hxU hx
      have hmem : (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) * Matrix.of x) i j :
          Formalism.QuantumDeterminants.Mt k r) ∈ S := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hsU hxU
      simp only [G, Set.piecewise, hmem, if_true]
      show (‖F (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 = 0
      rw [hFeq _ hp1 _ hp2 (Matrix.of x) hxU, hFx, map_zero, smul_zero]
      simp
    · have hnot : (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) * Matrix.of x) i j :
          Formalism.QuantumDeterminants.Mt k r) ∉ S := by
        intro hm
        exact hxU (DDSmoothness.uh_cancel hsU hm)
      simp only [G, Set.piecewise, hnot, if_false]
  have hGaeG : ∀ᵐ x ∂μG, G x = 0 := (lintegral_eq_zero_iff hGm).1 hμGint
  have hae : ∀ᵐ x ∂μG, Matrix.of x ∈ UHk → F (Matrix.of x) = 0 := by
    filter_upwards [hGaeG] with x hx hxU
    exact hGval x hxU hx
  intro g hg
  exact zero_of_ae hμG hFc hae hg
end Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability
