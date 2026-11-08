-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_topcap_original_joint_gaussian_generator_L1_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:44:05.019383+00:00
-- url     : https://prove2.me/submissions/913e9626-c9d5-4c06-af0d-fad3f015530b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_topcap_original_compact_generator_HJB_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_source_interior_compact_derivative_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual predictable physical-clock Gaussian coefficient has finite
    energy on a clipped compact interior strip, without changing measures. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D)
    (hTop : C = ⊤)
    (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 < q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u v δ B : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < B)
    (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0)
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ v then y else δ
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      Integrable R μ ∧
      (∫ p, R p ∂μ) ≤ 0 ∧
      (∫⁻ p, ENNReal.ofReal
        ((Real.exp (-(q * (p.1 : ℝ))) * (X.σ * deriv w (U p))) ^ 2) ∂μ) < ⊤ := by
  classical
  have hδv : δ ≤ v := by linarith
  have hband : Icc δ v ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    have hypos : 0 < y := lt_of_lt_of_le hδ hy.1
    exact ⟨hypos, by simp [hTop]⟩
  obtain ⟨Bgrad, hB⟩ := avram_p4_f3_source_interior_compact_derivative_bound
    w C hw_smooth (avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen C)
      δ v hband
  have hBnonneg : 0 ≤ Bgrad :=
    le_trans (abs_nonneg _) (hB δ ⟨le_rfl, hδv⟩)
  obtain ⟨μ, hμfinite, hμagreement, hRintegrable, hRsign⟩ :=
    avram_ubv_loc6_topcap_original_compact_generator_HJB_L1
      X x D C hD hTop w hw_smooth hw_cont hw_neg q
      hw_gen hw_grad u v δ B hu hδ hδone huv hv T
  refine ⟨μ, hμfinite, hμagreement, hRintegrable, hRsign, ?_⟩
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let U : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc δ v then Y p else δ
  have hU (p : ℝ≥0 × Ω) : U p ∈ Icc δ v := by
    dsimp [U]
    split_ifs with hp
    · exact hp
    · exact ⟨le_rfl, hδv⟩
  let K : ℝ := |X.σ| * Bgrad
  have hK : 0 ≤ K := mul_nonneg (abs_nonneg _) hBnonneg
  have hcoef (p : ℝ≥0 × Ω) :
      |Real.exp (-(q * (p.1 : ℝ))) * (X.σ * deriv w (U p))| ≤ K := by
    have hexp : Real.exp (-(q * (p.1 : ℝ))) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have ht : 0 ≤ (p.1 : ℝ) := NNReal.coe_nonneg _
      nlinarith [mul_nonneg (le_of_lt hq) ht]
    calc
      _ = Real.exp (-(q * (p.1 : ℝ))) * (|X.σ| * |deriv w (U p)|) := by
        rw [abs_mul, abs_mul, Real.abs_exp]
      _ ≤ Real.exp (-(q * (p.1 : ℝ))) * (|X.σ| * Bgrad) := by
        gcongr
        exact hB (U p) (hU p)
      _ ≤ 1 * (|X.σ| * Bgrad) := by
        gcongr
      _ = K := by simp [K]
  have hcoefSq (p : ℝ≥0 × Ω) :
      (Real.exp (-(q * (p.1 : ℝ))) * (X.σ * deriv w (U p))) ^ 2 ≤ K ^ 2 := by
    let z : ℝ := Real.exp (-(q * (p.1 : ℝ))) * (X.σ * deriv w (U p))
    have hz : |z| ≤ K := hcoef p
    have hmult : 0 ≤ (K - |z|) * (K + |z|) :=
      mul_nonneg (sub_nonneg.mpr hz) (add_nonneg hK (abs_nonneg z))
    have hsabs : |z| ^ 2 = z ^ 2 := by rw [sq_abs]
    change z ^ 2 ≤ K ^ 2
    nlinarith [hmult, hsabs]
  have hli :
      (∫⁻ p, ENNReal.ofReal
        ((Real.exp (-(q * (p.1 : ℝ))) * (X.σ * deriv w (U p))) ^ 2) ∂μ) ≤
        ENNReal.ofReal (K ^ 2) * μ Set.univ := by
    calc
      _ ≤ ∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal (K ^ 2) ∂μ :=
        lintegral_mono (fun p => ENNReal.ofReal_le_ofReal (hcoefSq p))
      _ = ENNReal.ofReal (K ^ 2) * μ Set.univ := by simp
  exact lt_of_le_of_lt hli (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμfinite)
