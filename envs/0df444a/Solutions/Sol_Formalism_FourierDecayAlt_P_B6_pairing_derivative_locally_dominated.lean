-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.pairing_derivative_locally_dominated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:05:51.59626+00:00
-- url     : https://prove2.me/submissions/b5c40c52-444a-44ba-8e54-ce35ac18306b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_two_sided_translate
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_constant_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_ae_strongly_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_inSS_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_sgs_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hsInner_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hsInner_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_rho_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Sd_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_model_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ph_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_parametric_derivative_under_integral
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_norm_admissible_of_double_translate_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_translated_norm_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_product_bound_monotone_factors_le
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (H : Hyp D Ξ α) {A B A1 B1 : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : admitted α cA A) (hA1 : admitted α cA A1) (hB : admitted α cB B) (hB1 : admitted α cB B1)
    {p : SS k r} (hp : D.inSS p) {a b : ℝ → Mat k r} {κ : ℝ → ℝ} {t₀ : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t₀)
    {K : ℝ} (ha : ∀ t ∈ s, a t ∈ GV k r) (hb : ∀ t ∈ s, b t ∈ GV k r)
    (hKa : ∀ t ∈ s, gN (a t)⁻¹ ≤ K) (hKb : ∀ t ∈ s, gN (b t)⁻¹ ≤ K) (hκ : ∀ t ∈ s, |κ t| ≤ K)
    (dA : ∀ z ∈ GV k r, ∀ t ∈ s, HasDerivAt (fun t => A (a t * z * b t)) (κ t • A1 (a t * z * b t)) t)
    (dB : ∀ z ∈ GV k r, ∀ t ∈ s, HasDerivAt (fun t => B (a t * z * b t)) (κ t • B1 (a t * z * b t)) t) :
    HasDerivAt (fun t => Ph D (fun g => A (a t * g * b t)) (fun g => B (a t * g * b t)) p)
      ((κ t₀ : ℂ) * (Ph D (fun g => A1 (a t₀ * g * b t₀)) (fun g => B (a t₀ * g * b t₀)) p +
        Ph D (fun g => A (a t₀ * g * b t₀)) (fun g => B1 (a t₀ * g * b t₀)) p)) t₀ := by
  have hα := H.α_nonneg
  have ht₀ : t₀ ∈ s := mem_of_mem_nhds hs
  obtain ⟨hS1, hS2⟩ := inSS_mem D hp
  have hS1i := WeylGroupFacts.uh_inv hS1
  have hK0 : 0 ≤ K := le_trans (gN_nonneg _) (hKa t₀ ht₀)
  have hcA := admissible_constant_nonneg hA
  have hcB := admissible_constant_nonneg hB
  obtain ⟨S1, hS1d⟩ : ∃ S1 : Mat k r, S1 = (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)⁻¹ := ⟨_, rfl⟩
  obtain ⟨S2, hS2d⟩ : ∃ S2 : Mat k r, S2 = (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r) := ⟨_, rfl⟩
  rw [← hS1d] at hS1i
  rw [← hS2d] at hS2
  have hsgs : ∀ g : Mat k r, sgs p g = S1 * g * S2 := by
    intro g; rw [sgs_eq, hS1d, hS2d]
  obtain ⟨P, hPd⟩ : ∃ P : ℝ, P = (K * K) ^ α := ⟨_, rfl⟩
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = (gN S1⁻¹ * gN S2⁻¹) ^ α := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hPd]; exact Real.rpow_nonneg (mul_nonneg hK0 hK0) _
  have hM0 : 0 ≤ M := by rw [hMd]; exact Real.rpow_nonneg (mul_nonneg (gN_nonneg _) (gN_nonneg _)) _
  have hG := haar_ae D.haarG

  have ms2 : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)} {c : ℝ}, admitted α c f → ∀ t ∈ s,
      AEStronglyMeasurable (fun g : Mt k r => f (a t * sgs p (Matrix.of g) * b t)) D.μG := by
    intro f c hf t ht
    have := admissible_ae_strongly_measurable (admissible_two_sided_translate hα (admissible_two_sided_translate hα hf (ha t ht) (hb t ht)) hS1i hS2) D.haarG
    simpa only [hsgs] using this
  have ms1 : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)} {c : ℝ}, admitted α c f → ∀ t ∈ s,
      AEStronglyMeasurable (fun g : Mt k r => f (a t * Matrix.of g * b t)) D.μG := by
    intro f c hf t ht
    exact admissible_ae_strongly_measurable (admissible_two_sided_translate hα hf (ha t ht) (hb t ht)) D.haarG

  have b2 : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)} {c : ℝ}, admitted α c f → ∀ g : Mt k r,
      (Matrix.of g : Mat k r) ∈ GV k r → ∀ t ∈ s,
      ‖f (a t * sgs p (Matrix.of g) * b t)‖ ≤ c * P * M * gN (Matrix.of g : Mat k r) ^ (-α) := by
    intro f c hf g hg t ht
    rw [hsgs, hPd, hMd]
    exact translated_norm_bound hα hf (ha t ht) (hb t ht) hS1i hS2 hg (hKa t ht) (hKb t ht)
  have b1 : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)} {c : ℝ}, admitted α c f → ∀ g : Mt k r,
      (Matrix.of g : Mat k r) ∈ GV k r → ∀ t ∈ s,
      ‖f (a t * Matrix.of g * b t)‖ ≤ c * P * 1 * gN (Matrix.of g : Mat k r) ^ (-α) := by
    intro f c hf g hg t ht
    rw [hPd, mul_one]
    exact norm_admissible_of_double_translate_le hα hf (ha t ht) (hb t ht) hg (hKa t ht) (hKb t ht)
  have hm0 : ∀ g : Mt k r, 0 ≤ gN (Matrix.of g : Mat k r) ^ (-α) := fun g => Real.rpow_nonneg (gN_nonneg _) _
  have key := parametric_derivative_under_integral (μ := D.μG) (Sd D p) (Sd_norm_le D hp)
    (u := fun t g => A (a t * sgs p (Matrix.of g) * b t)) (v := fun t g => B (a t * Matrix.of g * b t))
    (u' := fun t g => κ t • A1 (a t * sgs p (Matrix.of g) * b t))
    (v' := fun t g => κ t • B1 (a t * Matrix.of g * b t))
    hs (m := fun g => gN (Matrix.of g : Mat k r) ^ (-α)) (C := (1 + K) * (cA + cB) * P * (1 + M))
    (model_integrable H) (ms2 hA) (ms1 hB) (fun t ht => (ms2 hA1 t ht).const_smul (κ t))
    (fun t ht => (ms1 hB1 t ht).const_smul (κ t))
    (by
      filter_upwards [hG] with g hg t ht
      have hz : sgs p (Matrix.of g) ∈ GV k r := by
        rw [hsgs]; exact WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul hS1i hg) hS2
      exact dA _ hz t ht)
    (by
      filter_upwards [hG] with g hg t ht
      exact dB _ hg t ht)
    (by
      filter_upwards [hG] with g hg t ht
      have h := b2 hA g hg t ht
      have h2 := product_bound_monotone_factors_le (e := 1) (K := K) (c₀ := cA + cB) (M := M) zero_le_one (by linarith) hcA
        (by linarith) hP0 hM0 (by linarith) (hm0 g)
      linarith)
    (by
      filter_upwards [hG] with g hg t ht
      have h := b1 hB g hg t ht
      have h2 := product_bound_monotone_factors_le (e := 1) (K := K) (c₀ := cA + cB) (M := M) zero_le_one (by linarith) hcB
        (by linarith) hP0 zero_le_one (by linarith) (hm0 g)
      linarith)
    (by
      filter_upwards [hG] with g hg t ht
      have h := b2 hA1 g hg t ht
      have h2 := product_bound_monotone_factors_le (e := |κ t|) (K := K) (c₀ := cA + cB) (M := M) (abs_nonneg _)
        (by have := hκ t ht; linarith) hcA (by linarith) hP0 hM0 (by linarith) (hm0 g)
      rw [norm_smul, Real.norm_eq_abs]
      exact le_trans (mul_le_mul_of_nonneg_left h (abs_nonneg _)) h2)
    (by
      filter_upwards [hG] with g hg t ht
      have h := b1 hB1 g hg t ht
      have h2 := product_bound_monotone_factors_le (e := |κ t|) (K := K) (c₀ := cA + cB) (M := M) (abs_nonneg _)
        (by have := hκ t ht; linarith) hcB (by linarith) hP0 zero_le_one (by linarith) (hm0 g)
      rw [norm_smul, Real.norm_eq_abs]
      exact le_trans (mul_le_mul_of_nonneg_left h (abs_nonneg _)) h2)
  have i1 := ph_integrable H (admissible_two_sided_translate hα hA1 (ha t₀ ht₀) (hb t₀ ht₀))
    (admissible_two_sided_translate hα hB (ha t₀ ht₀) (hb t₀ ht₀)) hp
  have i2 := ph_integrable H (admissible_two_sided_translate hα hA (ha t₀ ht₀) (hb t₀ ht₀))
    (admissible_two_sided_translate hα hB1 (ha t₀ ht₀) (hb t₀ ht₀)) hp
  have e1 : (∫ g : Mt k r, (hsInner (Sd D p (κ t₀ • A1 (a t₀ * sgs p (Matrix.of g) * b t₀)))
        (B (a t₀ * Matrix.of g * b t₀)) +
      hsInner (Sd D p (A (a t₀ * sgs p (Matrix.of g) * b t₀))) (κ t₀ • B1 (a t₀ * Matrix.of g * b t₀))) ∂D.μG) =
      (κ t₀ : ℂ) * (Ph D (fun g => A1 (a t₀ * g * b t₀)) (fun g => B (a t₀ * g * b t₀)) p +
        Ph D (fun g => A (a t₀ * g * b t₀)) (fun g => B1 (a t₀ * g * b t₀)) p) := by
    unfold Ph
    rw [← integral_add i1 i2, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [rho_eq]
    rw [← Complex.coe_smul (κ t₀) (A1 _), ← Complex.coe_smul (κ t₀) (B1 _), map_smul, hsInner_smul_left,
      hsInner_smul_right, Complex.conj_ofReal]
    ring
  rw [← e1]
  have e2 : (fun t => Ph D (fun g => A (a t * g * b t)) (fun g => B (a t * g * b t)) p) =
      fun t => ∫ g : Mt k r, hsInner (Sd D p (A (a t * sgs p (Matrix.of g) * b t)))
        (B (a t * Matrix.of g * b t)) ∂D.μG := by
    funext t
    unfold Ph
    simp only [rho_eq]
  rw [e2]
  exact key
end Formalism.FourierDecayAlt.P.B6
