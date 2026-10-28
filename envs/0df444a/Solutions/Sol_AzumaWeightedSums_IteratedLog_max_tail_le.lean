-- Prove2me | solution 1 for AzumaWeightedSums.IteratedLog.max_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T19:00:18.569611+00:00
-- url     : https://prove2.me/submissions/0ac7af4d-f60e-43c3-8e63-3e807615d3e3

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

namespace AzumaWeightedSums.IteratedLog.Peer82MaxTail

open scoped ENNReal NNReal

/-- Negating the weights negates every partial sum. -/
theorem weightedSum_neg {Ω : Type*} (b : ℕ → ℝ) (x : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) :
    weightedSum (fun k => -b k) x m ω = -weightedSum b x m ω := by
  show (∑ k ∈ Finset.Icc 1 m, (-b k) * x k ω) = -(∑ k ∈ Finset.Icc 1 m, b k * x k ω)
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => neg_mul (b k) (x k ω)

/-- Negating the weights does not change the sum of squared weights. -/
theorem sqWeightSum_neg (b : ℕ → ℝ) (n : ℕ) :
    sqWeightSum (fun k => -b k) n = sqWeightSum b n := by
  show (∑ k ∈ Finset.Icc 1 n, (-b k) ^ 2) = ∑ k ∈ Finset.Icc 1 n, b k ^ 2
  exact Finset.sum_congr rfl fun k _ => neg_sq (b k)

/-- Every partial sum `S_m` is integrable. -/
theorem weightedSum_integrable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}
    (hx : IsCondSubgaussianOne μ ℱ x) (b : ℕ → ℝ) :
    ∀ m : ℕ, Integrable (weightedSum b x m) μ := by
  intro m
  induction m with
  | zero =>
      have h0 : weightedSum b x 0 = fun _ => (0 : ℝ) := by
        funext ω
        exact Lead34MGF.weightedSum_zero b x ω
      rw [h0]
      exact integrable_const (0 : ℝ)
  | succ m ih =>
      have hxi : Integrable (x (m + 1)) μ := (hx.1 (m + 1) (by omega)).2.1
      have heq : weightedSum b x (m + 1) =
          weightedSum b x m + fun ω => b (m + 1) * x (m + 1) ω := by
        funext ω
        exact Lead34MGF.weightedSum_succ b x m ω
      rw [heq]
      exact ih.add (hxi.const_mul (b (m + 1)))

/-- The increment `S_{m+1} - S_m = b_{m+1} x_{m+1}` has conditional mean zero given `ℱ m`. -/
theorem weightedSum_condExp_sub {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ} (hx : IsCondSubgaussianOne μ ℱ x) (b : ℕ → ℝ)
    (m : ℕ) : μ[weightedSum b x (m + 1) - weightedSum b x m | ℱ m] =ᵐ[μ] 0 := by
  have hmean : μ[x (m + 1) | ℱ m] =ᵐ[μ] 0 := by
    have h := (hx.1 (m + 1) (by omega)).2.2
    rwa [Nat.add_sub_cancel] at h
  have heq : weightedSum b x (m + 1) - weightedSum b x m = b (m + 1) • x (m + 1) := by
    funext ω
    show weightedSum b x (m + 1) ω - weightedSum b x m ω = b (m + 1) * x (m + 1) ω
    rw [Lead34MGF.weightedSum_succ]
    ring
  calc μ[weightedSum b x (m + 1) - weightedSum b x m | ℱ m]
      = μ[b (m + 1) • x (m + 1) | ℱ m] := by rw [heq]
    _ =ᵐ[μ] b (m + 1) • μ[x (m + 1) | ℱ m] :=
        condExp_smul (μ := μ) (b (m + 1)) (x (m + 1)) (ℱ m)
    _ =ᵐ[μ] b (m + 1) • (0 : Ω → ℝ) := hmean.const_smul (b (m + 1))
    _ = 0 := smul_zero (b (m + 1))

/-- `S_m = weightedSum b x m` is a martingale for `ℱ`. -/
theorem weightedSum_martingale {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}
    (hx : IsCondSubgaussianOne μ ℱ x) (b : ℕ → ℝ) :
    Martingale (weightedSum b x) ℱ μ :=
  martingale_of_condExp_sub_eq_zero_nat (Lead34MGF.weightedSum_stronglyMeasurable hx b)
    (weightedSum_integrable hx b) (weightedSum_condExp_sub hx b)

/-- `exp (s S_m)` is a submartingale for every real `s`, by conditional Jensen. The proof follows
`submartingale_exp` in the accepted Azuma packet 708142aa. -/
theorem submartingale_exp_weightedSum {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}
    (hx : IsCondSubgaussianOne μ ℱ x) (b : ℕ → ℝ) (s : ℝ) :
    Submartingale (fun m ω => Real.exp (s * weightedSum b x m ω)) ℱ μ := by
  have hM : Martingale (weightedSum b x) ℱ μ := weightedSum_martingale hx b
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact Real.continuous_exp.comp_stronglyMeasurable ((hM.stronglyMeasurable k).const_mul s)
  · intro i j hij
    have hfj_int : Integrable (fun ω => s * weightedSum b x j ω) μ :=
      (hM.integrable j).const_mul s
    have hexp_int : Integrable (fun ω => Real.exp (s * weightedSum b x j ω)) μ :=
      Lead34MGF.integrable_exp_weightedSum hx b j s
    have hJ := convexOn_exp.map_condExp_le_univ (μ := μ) (m := ℱ i) (ℱ.le i)
      Real.continuous_exp.lowerSemicontinuous hfj_int hexp_int
    have hsmul_eq : (s • weightedSum b x j) =ᵐ[μ] (fun ω => s * weightedSum b x j ω) := by
      filter_upwards with ω
      simp [Pi.smul_apply, smul_eq_mul]
    have hcond_s : μ[(fun ω => s * weightedSum b x j ω) | ℱ i] =ᵐ[μ]
        (fun ω => s * weightedSum b x i ω) := by
      calc
        μ[(fun ω => s * weightedSum b x j ω) | ℱ i] =ᵐ[μ] μ[s • weightedSum b x j | ℱ i] :=
          (condExp_congr_ae hsmul_eq).symm
        _ =ᵐ[μ] s • μ[weightedSum b x j | ℱ i] :=
          condExp_smul (μ := μ) s (weightedSum b x j) (ℱ i)
        _ =ᵐ[μ] s • weightedSum b x i := (hM.condExp_ae_eq hij).const_smul s
        _ =ᵐ[μ] (fun ω => s * weightedSum b x i ω) := by
          filter_upwards with ω
          simp [Pi.smul_apply, smul_eq_mul]
    calc
      (fun ω => Real.exp (s * weightedSum b x i ω))
          =ᵐ[μ] (fun ω => Real.exp (μ[(fun ω => s * weightedSum b x j ω) | ℱ i] ω)) := by
            filter_upwards [hcond_s] with ω hω
            rw [hω]
      _ ≤ᵐ[μ] μ[(fun ω => Real.exp (s * weightedSum b x j ω)) | ℱ i] := by
            have hJright : μ[Real.exp ∘ (fun ω => s * weightedSum b x j ω) | ℱ i] =ᵐ[μ]
                μ[(fun ω => Real.exp (s * weightedSum b x j ω)) | ℱ i] := by
              apply condExp_congr_ae
              filter_upwards with ω
              rfl
            have hJ' : (fun ω => Real.exp (μ[(fun ω => s * weightedSum b x j ω) | ℱ i] ω)) ≤ᵐ[μ]
                μ[(fun ω => Real.exp (s * weightedSum b x j ω)) | ℱ i] :=
              hJ.trans_eq hJright
            exact hJ'
  · intro k
    exact Lead34MGF.integrable_exp_weightedSum hx b k s

/-- One-sided maximal bound from Doob's maximal inequality at `t = λ / D`, where
`D = sqWeightSum c n`: `P(exp (t λ) ≤ max_{m ≤ n} exp (t S_m)) ≤ exp (-λ² / (2 D))`. The Doob step
and the division follow `lemma_8_scratch` in the accepted Azuma packet 708142aa. -/
theorem one_sided_tail {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}
    (hx : IsCondSubgaussianOne μ ℱ x) (c : ℕ → ℝ) (n : ℕ) (hc : 0 < sqWeightSum c n)
    (lam : ℝ) :
    μ {ω | Real.exp (lam / sqWeightSum c n * lam) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun m => Real.exp (lam / sqWeightSum c n * weightedSum c x m ω))}
      ≤ ENNReal.ofReal (Real.exp (-(lam ^ 2) / (2 * sqWeightSum c n))) := by
  let Y : ℕ → Ω → ℝ := fun m ω => Real.exp (lam / sqWeightSum c n * weightedSum c x m ω)
  have hsubY : Submartingale Y ℱ μ :=
    submartingale_exp_weightedSum hx c (lam / sqWeightSum c n)
  have hnonneg : 0 ≤ Y := by
    intro m ω
    exact (Real.exp_pos _).le
  let ε : ℝ≥0 := ⟨Real.exp (lam / sqWeightSum c n * lam), (Real.exp_pos _).le⟩
  let E : Set Ω := {ω | (ε : ℝ) ≤
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun m => Y m ω)}
  have hdoob := maximal_ineq (μ := μ) (f := Y) (𝒢 := ℱ) hsubY hnonneg (ε := ε) n
  have hdoobE : (ε : ℝ≥0∞) * μ E ≤ ENNReal.ofReal (∫ ω in E, Y n ω ∂μ) := by
    simpa only [E, Y] using hdoob
  have hYint : Integrable (fun ω => Y n ω) μ :=
    Lead34MGF.integrable_exp_weightedSum hx c n (lam / sqWeightSum c n)
  have hYnonneg : 0 ≤ᵐ[μ] (fun ω => Y n ω) :=
    Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le
  have hsetIntLe : ∫ ω in E, Y n ω ∂μ ≤ ∫ ω, Y n ω ∂μ :=
    setIntegral_le_integral hYint hYnonneg
  have hfullIntLe : ∫ ω, Y n ω ∂μ ≤
      Real.exp ((lam / sqWeightSum c n) ^ 2 / 2 * sqWeightSum c n) :=
    Lead34MGF.integral_exp_weightedSum_le hx c (lam / sqWeightSum c n) n
  have hdoobBound : (ε : ℝ≥0∞) * μ E ≤
      ENNReal.ofReal (Real.exp ((lam / sqWeightSum c n) ^ 2 / 2 * sqWeightSum c n)) :=
    hdoobE.trans (ENNReal.ofReal_le_ofReal (hsetIntLe.trans hfullIntLe))
  have hεeq : (ε : ℝ≥0∞) = ENNReal.ofReal (Real.exp (lam / sqWeightSum c n * lam)) :=
    (ENNReal.ofReal_coe_nnreal (p := ε)).symm
  rw [hεeq] at hdoobBound
  have hεne0 : ENNReal.ofReal (Real.exp (lam / sqWeightSum c n * lam)) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    positivity
  have hεnetop : ENNReal.ofReal (Real.exp (lam / sqWeightSum c n * lam)) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hPE : μ E ≤
      ENNReal.ofReal (Real.exp ((lam / sqWeightSum c n) ^ 2 / 2 * sqWeightSum c n)) /
        ENNReal.ofReal (Real.exp (lam / sqWeightSum c n * lam)) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hεne0) (Or.inl hεnetop), mul_comm (μ E)]
    exact hdoobBound
  have hexp : (lam / sqWeightSum c n) ^ 2 / 2 * sqWeightSum c n -
      lam / sqWeightSum c n * lam = -(lam ^ 2) / (2 * sqWeightSum c n) := by
    have key : lam / sqWeightSum c n * sqWeightSum c n = lam := div_mul_cancel₀ lam hc.ne'
    calc (lam / sqWeightSum c n) ^ 2 / 2 * sqWeightSum c n - lam / sqWeightSum c n * lam
        = lam / sqWeightSum c n * (lam / sqWeightSum c n * sqWeightSum c n) / 2 -
            lam / sqWeightSum c n * lam := by ring
      _ = lam / sqWeightSum c n * lam / 2 - lam / sqWeightSum c n * lam := by rw [key]
      _ = -(lam ^ 2) / (2 * sqWeightSum c n) := by ring
  have hdiv : ENNReal.ofReal (Real.exp ((lam / sqWeightSum c n) ^ 2 / 2 * sqWeightSum c n)) /
        ENNReal.ofReal (Real.exp (lam / sqWeightSum c n * lam)) =
      ENNReal.ofReal (Real.exp (-(lam ^ 2) / (2 * sqWeightSum c n))) := by
    rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub, hexp]
  exact hPE.trans_eq hdiv

end AzumaWeightedSums.IteratedLog.Peer82MaxTail

namespace AzumaWeightedSums.IteratedLog

/-- The maximal tail bound that "the Tchebycheff inequality and (2.3)" give in the proof of
Theorem 2 of Azuma 1967 (pp. 362–363): under [G] with `τ(x_n) ≤ 1`, for every `n`, every
real sequence `(b_k)` with `Σ_{k=1}^n b_k² > 0` and every `λ ≥ 0`,
`P{S_n^* > λ} ≤ 8 exp(−λ² / (2 Σ_{k=1}^n b_k²))`. -/
theorem max_tail_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}
    (hx : IsCondSubgaussianOne μ ℱ x) (b : ℕ → ℝ) (n : ℕ) (hb : 0 < sqWeightSum b n)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    μ {ω | lam < maxAbsWeightedSum b x n ω}
      ≤ ENNReal.ofReal (8 * Real.exp (-(lam ^ 2) / (2 * sqWeightSum b n))) := by
  rcases eq_or_lt_of_le hlam with h0 | hpos
  · have hexp0 : -(lam ^ 2) / (2 * sqWeightSum b n) = 0 := by
      rw [← h0]
      ring
    rw [hexp0, Real.exp_zero, mul_one]
    calc μ {ω | lam < maxAbsWeightedSum b x n ω} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal 8 := ENNReal.ofReal_le_ofReal (by norm_num)
  · have hnegD : sqWeightSum (fun k => -b k) n = sqWeightSum b n :=
      Peer82MaxTail.sqWeightSum_neg b n
    have hb' : 0 < sqWeightSum (fun k => -b k) n := by
      rw [hnegD]
      exact hb
    have h1 := Peer82MaxTail.one_sided_tail hx b n hb lam
    have h2 := Peer82MaxTail.one_sided_tail hx (fun k => -b k) n hb' lam
    rw [hnegD] at h2
    have ht : 0 ≤ lam / sqWeightSum b n := (div_pos hpos hb).le
    have hsub : {ω | lam < maxAbsWeightedSum b x n ω} ⊆
        {ω | Real.exp (lam / sqWeightSum b n * lam) ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun m => Real.exp (lam / sqWeightSum b n * weightedSum b x m ω))} ∪
        {ω | Real.exp (lam / sqWeightSum b n * lam) ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun m => Real.exp (lam / sqWeightSum b n * weightedSum (fun k => -b k) x m ω))} := by
      intro ω hω
      have hlt : lam < (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun m => |weightedSum b x m ω|) := hω
      obtain ⟨m, hm, hm_lt⟩ := (Finset.lt_sup'_iff _).mp hlt
      rcases lt_abs.mp hm_lt with hpos' | hneg'
      · have hmem : Real.exp (lam / sqWeightSum b n * lam) ≤
            (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
              (fun m => Real.exp (lam / sqWeightSum b n * weightedSum b x m ω)) :=
          Finset.le_sup'_of_le (fun m => Real.exp (lam / sqWeightSum b n * weightedSum b x m ω))
            hm (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpos'.le ht))
        exact Or.inl hmem
      · have hval : weightedSum (fun k => -b k) x m ω = -weightedSum b x m ω :=
          Peer82MaxTail.weightedSum_neg b x m ω
        have hstep : Real.exp (lam / sqWeightSum b n * lam) ≤
            Real.exp (lam / sqWeightSum b n * weightedSum (fun k => -b k) x m ω) := by
          rw [hval]
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hneg'.le ht)
        have hmem : Real.exp (lam / sqWeightSum b n * lam) ≤
            (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
              (fun m => Real.exp (lam / sqWeightSum b n * weightedSum (fun k => -b k) x m ω)) :=
          Finset.le_sup'_of_le
            (fun m => Real.exp (lam / sqWeightSum b n * weightedSum (fun k => -b k) x m ω))
            hm hstep
        exact Or.inr hmem
    have hsum : μ {ω | lam < maxAbsWeightedSum b x n ω} ≤
        ENNReal.ofReal (Real.exp (-(lam ^ 2) / (2 * sqWeightSum b n))) +
          ENNReal.ofReal (Real.exp (-(lam ^ 2) / (2 * sqWeightSum b n))) :=
      (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add h1 h2))
    have hpe := Real.exp_pos (-(lam ^ 2) / (2 * sqWeightSum b n))
    calc μ {ω | lam < maxAbsWeightedSum b x n ω}
        ≤ ENNReal.ofReal (Real.exp (-(lam ^ 2) / (2 * sqWeightSum b n))) +
            ENNReal.ofReal (Real.exp (-(lam ^ 2) / (2 * sqWeightSum b n))) := hsum
      _ = ENNReal.ofReal (2 * Real.exp (-(lam ^ 2) / (2 * sqWeightSum b n))) := by
          rw [← ENNReal.ofReal_add hpe.le hpe.le,
            two_mul (Real.exp (-(lam ^ 2) / (2 * sqWeightSum b n)))]
      _ ≤ ENNReal.ofReal (8 * Real.exp (-(lam ^ 2) / (2 * sqWeightSum b n))) := by
          apply ENNReal.ofReal_le_ofReal
          linarith

end AzumaWeightedSums.IteratedLog

end Prove2SwarmSubmission

theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}
    (hx : IsCondSubgaussianOne μ ℱ x) (b : ℕ → ℝ) (n : ℕ) (hb : 0 < sqWeightSum b n)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    μ {ω | lam < maxAbsWeightedSum b x n ω}
      ≤ ENNReal.ofReal (8 * Real.exp (-(lam ^ 2) / (2 * sqWeightSum b n))) := by
  exact _root_.Prove2SwarmSubmission.AzumaWeightedSums.IteratedLog.max_tail_le hx b n hb lam hlam
