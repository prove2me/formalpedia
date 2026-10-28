-- Prove2me | solution 1 for AzumaWeightedSums.IteratedLog.mgf_weightedSum_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T18:29:39.1636+00:00
-- url     : https://prove2.me/submissions/c34aa502-05bc-4cac-8231-94d38953c154

import Mathlib
import Definitions.Def_AzumaWeightedSums_IteratedLog_ClassG
import Definitions.Def_AzumaWeightedSums_IteratedLog_WeightedSums

open MeasureTheory ProbabilityTheory Filter Topology

open AzumaWeightedSums.IteratedLog

namespace Prove2SwarmSubmission


namespace AzumaWeightedSums.IteratedLog.Lead34MGF

theorem weightedSum_zero {Ω : Type*} (b : ℕ → ℝ) (x : ℕ → Ω → ℝ) (ω : Ω) :
    weightedSum b x 0 ω = 0 := by
  show (∑ k ∈ Finset.Icc 1 0, b k * x k ω) = 0
  rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]

theorem weightedSum_succ {Ω : Type*} (b : ℕ → ℝ) (x : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    weightedSum b x (n + 1) ω = weightedSum b x n ω + b (n + 1) * x (n + 1) ω := by
  show (∑ k ∈ Finset.Icc 1 (n + 1), b k * x k ω) =
    (∑ k ∈ Finset.Icc 1 n, b k * x k ω) + b (n + 1) * x (n + 1) ω
  rw [Finset.sum_Icc_succ_top (by omega)]

theorem sqWeightSum_zero (b : ℕ → ℝ) : sqWeightSum b 0 = 0 := by
  show (∑ k ∈ Finset.Icc 1 0, b k ^ 2) = 0
  rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]

theorem sqWeightSum_succ (b : ℕ → ℝ) (n : ℕ) :
    sqWeightSum b (n + 1) = sqWeightSum b n + b (n + 1) ^ 2 := by
  show (∑ k ∈ Finset.Icc 1 (n + 1), b k ^ 2) = (∑ k ∈ Finset.Icc 1 n, b k ^ 2) + b (n + 1) ^ 2
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- `S_n` is `ℱ n`-measurable. -/
theorem weightedSum_stronglyMeasurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ} (hx : IsCondSubgaussianOne μ ℱ x) (b : ℕ → ℝ) :
    ∀ n : ℕ, StronglyMeasurable[ℱ n] (weightedSum b x n) := by
  intro n
  induction n with
  | zero =>
      have h0 : weightedSum b x 0 = fun _ => (0 : ℝ) := by
        funext ω
        exact weightedSum_zero b x ω
      rw [h0]
      exact stronglyMeasurable_const
  | succ n ih =>
      have hxn : StronglyMeasurable[ℱ (n + 1)] (x (n + 1)) := (hx.1 (n + 1) (by omega)).1
      have hS : StronglyMeasurable[ℱ (n + 1)] (weightedSum b x n) :=
        ih.mono (ℱ.mono (Nat.le_succ n))
      have heq : weightedSum b x (n + 1) =
          weightedSum b x n + fun ω => b (n + 1) * x (n + 1) ω := by
        funext ω
        exact weightedSum_succ b x n ω
      rw [heq]
      exact hS.add (hxn.const_mul (b (n + 1)))

/-- Every exponential moment of `S_n` is finite: `exp(s S_{n+1}) ≤ exp(2 s S_n) + exp(2 s b x)`. -/
theorem integrable_exp_weightedSum {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}
    (hx : IsCondSubgaussianOne μ ℱ x) (b : ℕ → ℝ) :
    ∀ n : ℕ, ∀ s : ℝ, Integrable (fun ω => Real.exp (s * weightedSum b x n ω)) μ := by
  intro n
  induction n with
  | zero =>
      intro s
      have hExp0 : (fun ω => Real.exp (s * weightedSum b x 0 ω)) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
        filter_upwards with ω
        rw [weightedSum_zero b x ω, mul_zero, Real.exp_zero]
      exact (integrable_const (1 : ℝ)).congr hExp0.symm
  | succ n ih =>
      intro s
      have hxi : Integrable (fun ω => Real.exp (2 * s * b (n + 1) * x (n + 1) ω)) μ :=
        hx.2.1 (n + 1) (by omega) (2 * s * b (n + 1))
      have hSi : Integrable (fun ω => Real.exp (2 * s * weightedSum b x n ω)) μ := ih (2 * s)
      have hS1 : StronglyMeasurable[ℱ (n + 1)] (weightedSum b x (n + 1)) :=
        weightedSum_stronglyMeasurable hx b (n + 1)
      have hmeas : AEStronglyMeasurable (fun ω => Real.exp (s * weightedSum b x (n + 1) ω)) μ :=
        (Real.continuous_exp.comp_stronglyMeasurable
          ((hS1.mono (ℱ.le (n + 1))).const_mul s)).aestronglyMeasurable
      refine (hSi.add hxi).mono' hmeas ?_
      filter_upwards with ω
      show ‖Real.exp (s * weightedSum b x (n + 1) ω)‖ ≤
        Real.exp (2 * s * weightedSum b x n ω) + Real.exp (2 * s * b (n + 1) * x (n + 1) ω)
      have hA := Real.exp_pos (s * weightedSum b x n ω)
      have hB := Real.exp_pos (s * b (n + 1) * x (n + 1) ω)
      have hsplit : Real.exp (s * weightedSum b x (n + 1) ω) =
          Real.exp (s * weightedSum b x n ω) * Real.exp (s * b (n + 1) * x (n + 1) ω) := by
        rw [weightedSum_succ b x n ω, ← Real.exp_add]
        congr 1
        ring
      have hsqA : Real.exp (2 * s * weightedSum b x n ω) =
          Real.exp (s * weightedSum b x n ω) ^ 2 := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      have hsqB : Real.exp (2 * s * b (n + 1) * x (n + 1) ω) =
          Real.exp (s * b (n + 1) * x (n + 1) ω) ^ 2 := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hsplit, hsqA, hsqB]
      nlinarith [sq_nonneg (Real.exp (s * weightedSum b x n ω) -
        Real.exp (s * b (n + 1) * x (n + 1) ω)), mul_pos hA hB]

/-- Display (2.4) in integral form, by conditioning on `ℱ n` one step at a time. -/
theorem integral_exp_weightedSum_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}
    (hx : IsCondSubgaussianOne μ ℱ x) (b : ℕ → ℝ) (t : ℝ) :
    ∀ n : ℕ, ∫ ω, Real.exp (t * weightedSum b x n ω) ∂μ ≤
      Real.exp (t ^ 2 / 2 * sqWeightSum b n) := by
  intro n
  induction n with
  | zero =>
      have hExp0 : (fun ω => Real.exp (t * weightedSum b x 0 ω)) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
        filter_upwards with ω
        rw [weightedSum_zero b x ω, mul_zero, Real.exp_zero]
      have hIntEq : ∫ ω, Real.exp (t * weightedSum b x 0 ω) ∂μ = 1 := by
        calc
          ∫ ω, Real.exp (t * weightedSum b x 0 ω) ∂μ = ∫ _ : Ω, (1 : ℝ) ∂μ :=
            integral_congr_ae hExp0
          _ = 1 := by simp
      rw [hIntEq, sqWeightSum_zero b]
      simp
  | succ n ih =>
      have hSn : StronglyMeasurable[ℱ n] (weightedSum b x n) :=
        weightedSum_stronglyMeasurable hx b n
      have hf_sm : StronglyMeasurable[ℱ n] (fun ω => Real.exp (t * weightedSum b x n ω)) :=
        Real.continuous_exp.comp_stronglyMeasurable (hSn.const_mul t)
      have hgInt : Integrable (fun ω => Real.exp (t * b (n + 1) * x (n + 1) ω)) μ :=
        hx.2.1 (n + 1) (by omega) (t * b (n + 1))
      have hcond : μ[(fun ω => Real.exp (t * b (n + 1) * x (n + 1) ω)) | ℱ n] ≤ᵐ[μ]
          (fun _ => Real.exp ((t * b (n + 1)) ^ 2 / 2)) := by
        have h := hx.2.2 (n + 1) (by omega) (t * b (n + 1))
        rwa [Nat.add_sub_cancel] at h
      have hprod_eq : (fun ω => Real.exp (t * weightedSum b x (n + 1) ω)) =
          fun ω => Real.exp (t * weightedSum b x n ω) * Real.exp (t * b (n + 1) * x (n + 1) ω) := by
        funext ω
        rw [weightedSum_succ b x n ω, ← Real.exp_add]
        congr 1
        ring
      have hprodInt : Integrable (fun ω => Real.exp (t * weightedSum b x n ω) *
          Real.exp (t * b (n + 1) * x (n + 1) ω)) μ :=
        (integrable_exp_weightedSum hx b (n + 1) t).congr (Filter.EventuallyEq.of_eq hprod_eq)
      have hpull : μ[(fun ω => Real.exp (t * weightedSum b x n ω) *
            Real.exp (t * b (n + 1) * x (n + 1) ω)) | ℱ n] =ᵐ[μ]
          (fun ω => Real.exp (t * weightedSum b x n ω) *
            μ[(fun ω => Real.exp (t * b (n + 1) * x (n + 1) ω)) | ℱ n] ω) :=
        condExp_mul_of_aestronglyMeasurable_left hf_sm.aestronglyMeasurable hprodInt hgInt
      have hcondNext : μ[(fun ω => Real.exp (t * weightedSum b x n ω) *
            Real.exp (t * b (n + 1) * x (n + 1) ω)) | ℱ n] ≤ᵐ[μ]
          (fun ω => Real.exp (t * weightedSum b x n ω) * Real.exp ((t * b (n + 1)) ^ 2 / 2)) := by
        filter_upwards [hpull, hcond] with ω h1 h2
        rw [h1]
        exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      have hIntIneq : ∫ ω, Real.exp (t * weightedSum b x (n + 1) ω) ∂μ ≤
          ∫ ω, Real.exp (t * weightedSum b x n ω) * Real.exp ((t * b (n + 1)) ^ 2 / 2) ∂μ := by
        rw [hprod_eq]
        calc
          ∫ ω, Real.exp (t * weightedSum b x n ω) * Real.exp (t * b (n + 1) * x (n + 1) ω) ∂μ
              = ∫ ω, μ[(fun ω => Real.exp (t * weightedSum b x n ω) *
                  Real.exp (t * b (n + 1) * x (n + 1) ω)) | ℱ n] ω ∂μ :=
                (integral_condExp (ℱ.le n)).symm
          _ ≤ ∫ ω, Real.exp (t * weightedSum b x n ω) * Real.exp ((t * b (n + 1)) ^ 2 / 2) ∂μ :=
                integral_mono_ae integrable_condExp
                  ((integrable_exp_weightedSum hx b n t).mul_const _) hcondNext
      calc
        ∫ ω, Real.exp (t * weightedSum b x (n + 1) ω) ∂μ
            ≤ ∫ ω, Real.exp (t * weightedSum b x n ω) * Real.exp ((t * b (n + 1)) ^ 2 / 2) ∂μ :=
              hIntIneq
        _ = (∫ ω, Real.exp (t * weightedSum b x n ω) ∂μ) * Real.exp ((t * b (n + 1)) ^ 2 / 2) := by
              rw [integral_mul_const]
        _ ≤ Real.exp (t ^ 2 / 2 * sqWeightSum b n) * Real.exp ((t * b (n + 1)) ^ 2 / 2) :=
              mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
        _ = Real.exp (t ^ 2 / 2 * sqWeightSum b (n + 1)) := by
              rw [← Real.exp_add, sqWeightSum_succ b n]
              congr 1
              ring

end AzumaWeightedSums.IteratedLog.Lead34MGF

namespace AzumaWeightedSums.IteratedLog

/-- Azuma 1967, display (2.4) (proof of Lemma 2, pp. 358–359): under [G] with `τ(x_n) ≤ 1`,
`E exp(t Σ_{k=1}^n b_k x_k) ≤ exp((t²/2) Σ_{k=1}^n b_k²)` for every `n`, every real
sequence `(b_k)` and every real `t`. -/
theorem mgf_weightedSum_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}
    (hx : IsCondSubgaussianOne μ ℱ x) (b : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * weightedSum b x n ω)) ∂μ
      ≤ ENNReal.ofReal (Real.exp (t ^ 2 / 2 * sqWeightSum b n)) := by
  have hnn : 0 ≤ᵐ[μ] fun ω => Real.exp (t * weightedSum b x n ω) := by
    filter_upwards with ω
    exact (Real.exp_pos _).le
  calc
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * weightedSum b x n ω)) ∂μ
        = ENNReal.ofReal (∫ ω, Real.exp (t * weightedSum b x n ω) ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal
            (Lead34MGF.integrable_exp_weightedSum hx b n t) hnn).symm
    _ ≤ ENNReal.ofReal (Real.exp (t ^ 2 / 2 * sqWeightSum b n)) :=
          ENNReal.ofReal_le_ofReal (Lead34MGF.integral_exp_weightedSum_le hx b t n)

end AzumaWeightedSums.IteratedLog

end Prove2SwarmSubmission

theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}
    (hx : IsCondSubgaussianOne μ ℱ x) (b : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * weightedSum b x n ω)) ∂μ
      ≤ ENNReal.ofReal (Real.exp (t ^ 2 / 2 * sqWeightSum b n)) := by
  exact _root_.Prove2SwarmSubmission.AzumaWeightedSums.IteratedLog.mgf_weightedSum_le hx b n t
