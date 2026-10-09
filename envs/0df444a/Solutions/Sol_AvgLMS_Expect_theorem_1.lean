-- Prove2me | solution 1 for AvgLMS.Expect.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T13:31:22.826984+00:00
-- url     : https://prove2.me/submissions/878892e1-ceb1-4190-bfb5-d1e65089b859
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model
import Theorems.Thm_AvgLMS_Expect_noise_bound
import Theorems.Thm_AvgLMS_Expect_initial_conditions_bound
import Theorems.Thm_AvgLMS_Expect_excess_risk_eq

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace AvgLMSRed

open AvgLMS.Expect

theorem lms_eq {Ω : Type*} {d : ℕ} (γ : ℝ) (θ0 θstar : Hs d) (x z : ℕ → Ω → Hs d) :
    ∀ (k : ℕ) (ω : Ω), lmsIter γ θ0 x z k ω =
      lmsIter γ θstar x z k ω + biasIter γ (θ0 - θstar) x k ω
  | 0, ω => by simp only [lmsIter, biasIter]; abel
  | k + 1, ω => by
    simp only [lmsIter, biasIter]
    rw [lms_eq γ θ0 θstar x z k ω, inner_add_left,
      real_inner_comm (x (k + 1) ω) (biasIter γ (θ0 - θstar) x k ω), add_smul]
    simp only [smul_sub, smul_add]
    abel

theorem avg_split {Ω : Type*} {d : ℕ} (γ : ℝ) (θ0 θstar : Hs d) (x z : ℕ → Ω → Hs d)
    (m : ℕ) (ω : Ω) :
    avg (lmsIter γ θ0 x z) m ω - θstar =
      (avg (lmsIter γ θstar x z) m ω - θstar) + avg (biasIter γ (θ0 - θstar) x) m ω := by
  have h : avg (lmsIter γ θ0 x z) m ω =
      avg (lmsIter γ θstar x z) m ω + avg (biasIter γ (θ0 - θstar) x) m ω := by
    unfold avg
    rw [← smul_add, ← Finset.sum_add_distrib]
    exact congrArg _ (Finset.sum_congr rfl fun k _ => lms_eq γ θ0 θstar x z k ω)
  rw [h]; abel

theorem lms_meas {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (γ : ℝ) (θ0 : Hs d)
    (x z : ℕ → Ω → Hs d) (hx : ∀ n, Measurable (x n)) (hz : ∀ n, Measurable (z n)) :
    ∀ k, Measurable (lmsIter γ θ0 x z k)
  | 0 => measurable_const
  | k + 1 => by
    have h := (Continuous.measurable (by fun_prop :
      Continuous fun p : Hs d × Hs d × Hs d => p.1 - γ • (⟪p.1, p.2.1⟫_ℝ • p.2.1 - p.2.2))).comp
      ((lms_meas γ θ0 x z hx hz k).prodMk ((hx (k + 1)).prodMk (hz (k + 1))))
    exact h

theorem bias_meas {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (γ : ℝ) (η0 : Hs d)
    (x : ℕ → Ω → Hs d) (hx : ∀ n, Measurable (x n)) :
    ∀ k, Measurable (biasIter γ η0 x k)
  | 0 => measurable_const
  | k + 1 => by
    have h := (Continuous.measurable (by fun_prop :
      Continuous fun p : Hs d × Hs d => p.1 - γ • (⟪p.2, p.1⟫_ℝ • p.2))).comp
      ((bias_meas γ η0 x hx k).prodMk (hx (k + 1)))
    exact h

theorem avg_meas {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (p : ℕ → Ω → Hs d)
    (hp : ∀ k, Measurable (p k)) (m : ℕ) : Measurable (avg p m) := by
  unfold avg
  exact (Finset.measurable_sum _ fun k _ => hp k).const_smul (((m : ℝ) + 1)⁻¹)

theorem q_nonneg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (v : Hs d) :
    0 ≤ ⟪v, H v⟫_ℝ := by
  rw [hA.cov_eq v v]; exact integral_nonneg fun _ => mul_self_nonneg _

theorem quad_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (t : ℝ) (ht : 0 < t) (u v : Hs d) :
    ⟪u + v, H (u + v)⟫_ℝ ≤ (1 + t) * ⟪u, H u⟫_ℝ + (1 + 1 / t) * ⟪v, H v⟫_ℝ := by
  have hsym : ⟪v, H u⟫_ℝ = ⟪u, H v⟫_ℝ := by
    rw [hA.cov_eq, hA.cov_eq]; congr 1; funext ω; ring
  have h0 := q_nonneg hA (t • u - v)
  have e1 : ⟪u + v, H (u + v)⟫_ℝ = ⟪u, H u⟫_ℝ + 2 * ⟪u, H v⟫_ℝ + ⟪v, H v⟫_ℝ := by
    simp only [map_add, inner_add_left, inner_add_right]; rw [hsym]; ring
  have e2 : ⟪t • u - v, H (t • u - v)⟫_ℝ =
      t ^ 2 * ⟪u, H u⟫_ℝ - 2 * t * ⟪u, H v⟫_ℝ + ⟪v, H v⟫_ℝ := by
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [hsym]; ring
  rw [e1]; rw [e2] at h0
  have key : 0 ≤ (t ^ 2 * ⟪u, H u⟫_ℝ - 2 * t * ⟪u, H v⟫_ℝ + ⟪v, H v⟫_ℝ) / t :=
    div_nonneg h0 ht.le
  have e3 : (t ^ 2 * ⟪u, H u⟫_ℝ - 2 * t * ⟪u, H v⟫_ℝ + ⟪v, H v⟫_ℝ) / t =
      t * ⟪u, H u⟫_ℝ - 2 * ⟪u, H v⟫_ℝ + 1 / t * ⟪v, H v⟫_ℝ := by
    field_simp
  rw [e3] at key
  nlinarith

end AvgLMSRed


namespace AvgLMSRed
open AvgLMS.Expect

theorem main_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (a b : Ω → Hs d)
    (hma : Measurable a) (hmb : Measurable b)
    (hint1 : Integrable (fun ω => ⟪a ω, H (a ω)⟫_ℝ) μ)
    (hint2 : Integrable (fun ω => ⟪b ω, H (b ω)⟫_ℝ) μ) (α β : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (hle1 : Real.sqrt (∫ ω, ⟪a ω, H (a ω)⟫_ℝ ∂μ) ≤ α)
    (hle2 : ∫ ω, ⟪b ω, H (b ω)⟫_ℝ ∂μ ≤ β ^ 2) :
    Integrable (fun ω => ⟪a ω + b ω, H (a ω + b ω)⟫_ℝ) μ ∧
    ∫ ω, ⟪a ω + b ω, H (a ω + b ω)⟫_ℝ ∂μ ≤ (α + β) ^ 2 := by
  have hms : Measurable fun ω => a ω + b ω := hma.add hmb
  have hmq : Measurable fun ω => ⟪a ω + b ω, H (a ω + b ω)⟫_ℝ :=
    hms.inner (H.continuous.measurable.comp hms)
  have hintS : Integrable (fun ω => ⟪a ω + b ω, H (a ω + b ω)⟫_ℝ) μ := by
    refine Integrable.mono' ((hint1.const_mul 2).add (hint2.const_mul 2))
      hmq.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (q_nonneg hA _)]
    have h := quad_le hA 1 one_pos (a ω) (b ω)
    rw [show (1 : ℝ) + 1 = 2 by norm_num, show (1 : ℝ) + 1 / 1 = 2 by norm_num] at h
    simp only [Pi.add_apply]
    linarith
  refine ⟨hintS, ?_⟩
  have hI : ∀ t : ℝ, 0 < t → ∫ ω, ⟪a ω + b ω, H (a ω + b ω)⟫_ℝ ∂μ ≤
      (1 + t) * ∫ ω, ⟪a ω, H (a ω)⟫_ℝ ∂μ + (1 + 1 / t) * ∫ ω, ⟪b ω, H (b ω)⟫_ℝ ∂μ := by
    intro t ht
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hint1.const_mul _) (hint2.const_mul _)]
    exact integral_mono hintS ((hint1.const_mul (1 + t)).add (hint2.const_mul (1 + 1 / t)))
      (fun ω => quad_le hA t ht (a ω) (b ω))
  have hA0 : 0 ≤ ∫ ω, ⟪a ω, H (a ω)⟫_ℝ ∂μ := integral_nonneg fun ω => q_nonneg hA _
  have hB0 : 0 ≤ ∫ ω, ⟪b ω, H (b ω)⟫_ℝ ∂μ := integral_nonneg fun ω => q_nonneg hA _
  have hAle : ∫ ω, ⟪a ω, H (a ω)⟫_ℝ ∂μ ≤ α ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle1 2
    rwa [Real.sq_sqrt hA0] at this
  generalize ∫ ω, ⟪a ω, H (a ω)⟫_ℝ ∂μ = A at hI hA0 hAle
  generalize ∫ ω, ⟪b ω, H (b ω)⟫_ℝ ∂μ = B at hI hB0 hle2
  generalize ∫ ω, ⟪a ω + b ω, H (a ω + b ω)⟫_ℝ ∂μ = I at hI ⊢
  rcases hβ.eq_or_lt with h | h
  · rw [← h, add_zero]
    have hB : B = 0 := le_antisymm (by rw [← h] at hle2; simpa using hle2) hB0
    apply le_of_forall_pos_le_add
    intro ε hε
    have h1 := hI (ε / α ^ 2) (by positivity)
    rw [hB, mul_zero, add_zero] at h1
    have h2 : (1 + ε / α ^ 2) * A ≤ (1 + ε / α ^ 2) * α ^ 2 :=
      mul_le_mul_of_nonneg_left hAle (by positivity)
    have h3 : (1 + ε / α ^ 2) * α ^ 2 = α ^ 2 + ε := by field_simp
    linarith
  · have h1 := hI (β / α) (by positivity)
    have h2 : (1 + β / α) * A ≤ (1 + β / α) * α ^ 2 :=
      mul_le_mul_of_nonneg_left hAle (by positivity)
    have h3 : (1 + 1 / (β / α)) * B ≤ (1 + 1 / (β / α)) * β ^ 2 :=
      mul_le_mul_of_nonneg_left hle2 (by positivity)
    have h4 : (1 + β / α) * α ^ 2 + (1 + 1 / (β / α)) * β ^ 2 = (α + β) ^ 2 := by
      field_simp; ring
    linarith

end AvgLMSRed

open MeasureTheory ProbabilityTheory InnerProductSpace RealInnerProductSpace AvgLMS.Expect in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (x z : ℕ → Ω → Hs d) (H : Hs d →L[ℝ] Hs d) (θstar : Hs d) (R σ : ℝ)
    (hA : LMSAssumptions μ x z H θstar R σ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ : γ < 1 / R ^ 2) (θ0 : Hs d) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun ω => lsObjective μ x z (avg (lmsIter γ θ0 x z) (n - 1) ω) -
      lsObjective μ x z θstar) μ ∧
    ∫ ω, (lsObjective μ x z (avg (lmsIter γ θ0 x z) (n - 1) ω) - lsObjective μ x z θstar) ∂μ ≤
      1 / (2 * n) * (σ * Real.sqrt d / (1 - Real.sqrt (γ * R ^ 2)) +
        R * ‖θ0 - θstar‖ * (1 / Real.sqrt (γ * R ^ 2))) ^ 2 := by
  have hR := hA.R_pos
  have hγR : γ * R ^ 2 < 1 := (lt_div_iff₀ (by positivity)).mp hγ
  obtain ⟨hint1, hle1⟩ := AvgLMS.Expect.noise_bound μ x z H θstar R σ hA γ hγ0 hγR n hn
  obtain ⟨hint2, hle2⟩ := AvgLMS.Expect.initial_conditions_bound μ x z H θstar R σ hA γ hγ0
    hγR.le (θ0 - θstar) n hn
  have hexc := AvgLMS.Expect.excess_risk_eq μ x z H θstar R σ hA
  have hfun : (fun ω => lsObjective μ x z (avg (lmsIter γ θ0 x z) (n - 1) ω) -
      lsObjective μ x z θstar) = fun ω => (1 / 2) *
        ⟪(avg (lmsIter γ θstar x z) (n - 1) ω - θstar) + avg (biasIter γ (θ0 - θstar) x) (n - 1) ω,
          H ((avg (lmsIter γ θstar x z) (n - 1) ω - θstar) +
            avg (biasIter γ (θ0 - θstar) x) (n - 1) ω)⟫_ℝ := by
    funext ω; rw [hexc, AvgLMSRed.avg_split]
  have hma : Measurable fun ω => avg (lmsIter γ θstar x z) (n - 1) ω - θstar :=
    (AvgLMSRed.avg_meas _ (AvgLMSRed.lms_meas γ θstar x z hA.measurable_x hA.measurable_z)
      (n - 1)).sub_const θstar
  have hmb : Measurable (avg (biasIter γ (θ0 - θstar) x) (n - 1)) :=
    AvgLMSRed.avg_meas _ (AvgLMSRed.bias_meas γ (θ0 - θstar) x hA.measurable_x) (n - 1)
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast hA.one_le_dim
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs1 : Real.sqrt (γ * R ^ 2) < 1 := by
    rw [Real.sqrt_lt' one_pos]; simpa using hγR
  have hsγ : Real.sqrt (γ * R ^ 2) = Real.sqrt γ * R := by
    rw [Real.sqrt_mul hγ0.le, Real.sqrt_sq hR.le]
  have hsq_n : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hsq_γ : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ0
  have hsq_d : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by linarith)
  have hα : 0 < σ * Real.sqrt d / Real.sqrt n * (1 / (1 - Real.sqrt (γ * R ^ 2))) := by
    have : 0 < 1 - Real.sqrt (γ * R ^ 2) := by linarith
    have := hA.σ_pos
    positivity
  have hβ : 0 ≤ ‖θ0 - θstar‖ / (Real.sqrt n * Real.sqrt γ) := by positivity
  have hle2' : ∫ ω, ⟪avg (biasIter γ (θ0 - θstar) x) (n - 1) ω,
      H (avg (biasIter γ (θ0 - θstar) x) (n - 1) ω)⟫_ℝ ∂μ ≤
      (‖θ0 - θstar‖ / (Real.sqrt n * Real.sqrt γ)) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt hγ0.le]; exact hle2
  obtain ⟨hS1, hS2⟩ := AvgLMSRed.main_bound hA
    (fun ω => avg (lmsIter γ θstar x z) (n - 1) ω - θstar)
    (avg (biasIter γ (θ0 - θstar) x) (n - 1)) hma hmb hint1 hint2 _ _ hα hβ hle1 hle2'
  rw [hfun]
  refine ⟨hS1.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hfin : (σ * Real.sqrt d / Real.sqrt n * (1 / (1 - Real.sqrt (γ * R ^ 2))) +
      ‖θ0 - θstar‖ / (Real.sqrt n * Real.sqrt γ)) ^ 2 =
      1 / n * (σ * Real.sqrt d / (1 - Real.sqrt (γ * R ^ 2)) +
        R * ‖θ0 - θstar‖ * (1 / Real.sqrt (γ * R ^ 2))) ^ 2 := by
    have h1s : 1 - Real.sqrt γ * R ≠ 0 := by rw [← hsγ]; linarith
    rw [show (1 : ℝ) / n = 1 / Real.sqrt n ^ 2 by rw [Real.sq_sqrt (by linarith)], hsγ]
    field_simp
  have : (1 : ℝ) / (2 * n) = 1 / 2 * (1 / n) := by field_simp
  rw [this, mul_assoc, ← hfin]
  have := hS2
  linarith
