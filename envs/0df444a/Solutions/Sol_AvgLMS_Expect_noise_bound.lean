-- Prove2me | solution 1 for AvgLMS.Expect.noise_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:18:13.337567+00:00
-- url     : https://prove2.me/submissions/de59987f-3f2d-4e99-a68e-078eb7fbc149

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model
import Theorems.Thm_AvgLMS_Expect_order_r_bound
import Theorems.Thm_AvgLMS_Expect_remainder_bound

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace


namespace AvgLMSNB

open AvgLMS.Expect

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


theorem residual_meas {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (x z : ℕ → Ω → Hs d) (θstar : Hs d)
    (hx : ∀ n, Measurable (x n)) (hz : ∀ n, Measurable (z n)) (n : ℕ) :
    Measurable (residual x z θstar n) := by
  have e : residual x z θstar n = fun ω => z n ω - ⟪θstar, x n ω⟫_ℝ • x n ω := rfl
  rw [e]
  exact (Continuous.measurable (by fun_prop :
    Continuous fun p : Hs d × Hs d => p.2 - ⟪θstar, p.1⟫_ℝ • p.1)).comp ((hx n).prodMk (hz n))

theorem etaR_meas {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (γ : ℝ) (H : Hs d →L[ℝ] Hs d)
    (x ξ : ℕ → Ω → Hs d) (hx : ∀ n, Measurable (x n)) (hξ : ∀ n, Measurable (ξ n)) :
    ∀ r n, Measurable (etaR γ H x ξ r n)
  | 0, 0 => measurable_const
  | 0, n + 1 => by
    have h := (Continuous.measurable (by fun_prop :
      Continuous fun p : Hs d × Hs d => (1 - γ • H) p.1 + γ • p.2)).comp
      ((etaR_meas γ H x ξ hx hξ 0 n).prodMk (hξ (n + 1)))
    exact h
  | r + 1, 0 => measurable_const
  | r + 1, n + 1 => by
    have h := (Continuous.measurable (by fun_prop :
      Continuous fun p : Hs d × Hs d × Hs d =>
        (1 - γ • H) p.1 + γ • (H p.2.1 - ⟪p.2.2, p.2.1⟫_ℝ • p.2.2))).comp
      ((etaR_meas γ H x ξ hx hξ (r + 1) n).prodMk ((etaR_meas γ H x ξ hx hξ r n).prodMk (hx (n + 1))))
    exact h

theorem sum_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (f : ℕ → Ω → Hs d) (hf : ∀ i, Measurable (f i))
    (hint : ∀ i, Integrable (fun ω => ⟪f i ω, H (f i ω)⟫_ℝ) μ)
    (A q : ℝ) (hA0 : 0 < A) (hq : 0 ≤ q)
    (hle : ∀ i, ∫ ω, ⟪f i ω, H (f i ω)⟫_ℝ ∂μ ≤ (A * q ^ i) ^ 2) :
    ∀ r : ℕ, Integrable (fun ω => ⟪∑ i ∈ Finset.range (r + 1), f i ω,
        H (∑ i ∈ Finset.range (r + 1), f i ω)⟫_ℝ) μ ∧
      Real.sqrt (∫ ω, ⟪∑ i ∈ Finset.range (r + 1), f i ω,
        H (∑ i ∈ Finset.range (r + 1), f i ω)⟫_ℝ ∂μ) ≤ A * ∑ i ∈ Finset.range (r + 1), q ^ i
  | 0 => by
    simp only [zero_add, Finset.sum_range_one, pow_zero, mul_one]
    refine ⟨hint 0, ?_⟩
    have h0 := hle 0
    simp only [pow_zero, mul_one] at h0
    calc Real.sqrt _ ≤ Real.sqrt (A ^ 2) := Real.sqrt_le_sqrt h0
      _ = A := Real.sqrt_sq hA0.le
  | r + 1 => by
    obtain ⟨h1, h2⟩ := sum_bound hA f hf hint A q hA0 hq hle r
    have hpos : 0 < A * ∑ i ∈ Finset.range (r + 1), q ^ i := by
      apply mul_pos hA0
      exact Finset.sum_pos' (fun i _ => pow_nonneg hq i) ⟨0, by simp, by simp⟩
    obtain ⟨h3, h4⟩ := main_bound hA (fun ω => ∑ i ∈ Finset.range (r + 1), f i ω) (f (r + 1))
      (Finset.measurable_sum _ fun i _ => hf i) (hf (r + 1)) h1 (hint (r + 1)) _ _ hpos
      (by positivity) h2 (hle (r + 1))
    have e : ∀ ω, ∑ i ∈ Finset.range (r + 1 + 1), f i ω =
        ∑ i ∈ Finset.range (r + 1), f i ω + f (r + 1) ω := fun ω => Finset.sum_range_succ _ _
    simp only [e]
    refine ⟨h3, ?_⟩
    rw [Finset.sum_range_succ (fun i => q ^ i), mul_add]
    calc Real.sqrt _ ≤ Real.sqrt ((A * ∑ i ∈ Finset.range (r + 1), q ^ i + A * q ^ (r + 1)) ^ 2) :=
          Real.sqrt_le_sqrt h4
      _ = _ := Real.sqrt_sq (by positivity)

end AvgLMSNB

open MeasureTheory ProbabilityTheory InnerProductSpace RealInnerProductSpace AvgLMS.Expect in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (x z : ℕ → Ω → Hs d) (H : Hs d →L[ℝ] Hs d) (θstar : Hs d) (R σ : ℝ)
    (hA : LMSAssumptions μ x z H θstar R σ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγR : γ * R ^ 2 < 1) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun ω => ⟪avg (lmsIter γ θstar x z) (n - 1) ω - θstar,
      H (avg (lmsIter γ θstar x z) (n - 1) ω - θstar)⟫_ℝ) μ ∧
    Real.sqrt (∫ ω, ⟪avg (lmsIter γ θstar x z) (n - 1) ω - θstar,
        H (avg (lmsIter γ θstar x z) (n - 1) ω - θstar)⟫_ℝ ∂μ) ≤
      σ * Real.sqrt d / Real.sqrt n * (1 / (1 - Real.sqrt (γ * R ^ 2))) := by
  have hR := hA.R_pos
  have hσ := hA.σ_pos
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast hA.one_le_dim
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hγR0 : 0 ≤ γ * R ^ 2 := by positivity
  set q := Real.sqrt (γ * R ^ 2) with hqdef
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = γ * R ^ 2 := Real.sq_sqrt hγR0
  have hq1 : q < 1 := by rw [hqdef, Real.sqrt_lt' one_pos]; simpa using hγR
  set A := σ * Real.sqrt d / Real.sqrt n with hAdef
  have hA0 : 0 < A := by
    have : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
    have : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by linarith)
    positivity
  have hA2 : A ^ 2 = σ ^ 2 * d / n := by
    rw [hAdef, div_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
  let f : ℕ → Ω → Hs d := fun i => avg (etaR γ H x (residual x z θstar) i) (n - 1)
  let X : Ω → Hs d := fun ω => avg (lmsIter γ θstar x z) (n - 1) ω - θstar
  have hf : ∀ i, Measurable (f i) := fun i =>
    AvgLMSNB.avg_meas _ (AvgLMSNB.etaR_meas γ H x _ hA.measurable_x
      (AvgLMSNB.residual_meas x z θstar hA.measurable_x hA.measurable_z) i) (n - 1)
  have hX : Measurable X :=
    (AvgLMSNB.avg_meas _ (AvgLMSNB.lms_meas γ θstar x z hA.measurable_x hA.measurable_z)
      (n - 1)).sub_const θstar
  have hfi : ∀ i, Integrable (fun ω => ⟪f i ω, H (f i ω)⟫_ℝ) μ := fun i =>
    (AvgLMS.Expect.order_r_bound μ x z H θstar R σ hA γ hγ0 hγR.le i n hn).1
  have hfle : ∀ i, ∫ ω, ⟪f i ω, H (f i ω)⟫_ℝ ∂μ ≤ (A * q ^ i) ^ 2 := by
    intro i
    have h := (AvgLMS.Expect.order_r_bound μ x z H θstar R σ hA γ hγ0 hγR.le i n hn).2
    have e : (A * q ^ i) ^ 2 = 1 / n * γ ^ i * R ^ (2 * i) * d * σ ^ 2 := by
      rw [mul_pow, hA2, ← pow_mul, mul_comm i 2, pow_mul, hq2, mul_pow, ← pow_mul]
      field_simp
    rw [e]; exact h
  have hS := AvgLMSNB.sum_bound hA f hf hfi A q hA0 hq0 hfle
  -- for every r: the remainder piece
  have key : ∀ r : ℕ, Integrable (fun ω => ⟪X ω, H (X ω)⟫_ℝ) μ ∧
      Real.sqrt (∫ ω, ⟪X ω, H (X ω)⟫_ℝ ∂μ) ≤
        A * (1 / (1 - q)) + σ * q ^ 2 / Real.sqrt (1 - q ^ 2) * q ^ r := by
    intro r
    have hrem := AvgLMS.Expect.remainder_bound μ x z H θstar R σ hA γ hγ0 hγR r n hn
    simp only at hrem
    obtain ⟨hri, hrle⟩ := hrem
    obtain ⟨hs1, hs2⟩ := hS r
    have hpos : 0 < A * ∑ i ∈ Finset.range (r + 1), q ^ i := by
      apply mul_pos hA0
      exact Finset.sum_pos' (fun i _ => pow_nonneg hq0 i) ⟨0, by simp, by simp⟩
    have h1q : 0 < 1 - q ^ 2 := by nlinarith
    have hβ : 0 ≤ σ * q ^ (r + 2) / Real.sqrt (1 - q ^ 2) := by positivity
    have hrle' : ∫ ω, ⟪X ω - ∑ i ∈ Finset.range (r + 1), f i ω,
        H (X ω - ∑ i ∈ Finset.range (r + 1), f i ω)⟫_ℝ ∂μ ≤
        (σ * q ^ (r + 2) / Real.sqrt (1 - q ^ 2)) ^ 2 := by
      have e : (σ * q ^ (r + 2) / Real.sqrt (1 - q ^ 2)) ^ 2 =
          1 / (1 - γ * R ^ 2) * γ ^ (r + 2) * σ ^ 2 * R ^ (2 * r + 4) := by
        rw [div_pow, mul_pow, Real.sq_sqrt h1q.le, ← pow_mul, mul_comm (r + 2) 2, pow_mul, hq2,
          mul_pow, ← pow_mul]
        rw [show 2 * (r + 2) = 2 * r + 4 by ring]
        field_simp
      rw [e]; exact hrle
    have hmS : Measurable fun ω => ∑ i ∈ Finset.range (r + 1), f i ω :=
      Finset.measurable_sum _ fun i _ => hf i
    obtain ⟨h3, h4⟩ := AvgLMSNB.main_bound hA (fun ω => ∑ i ∈ Finset.range (r + 1), f i ω)
      (fun ω => X ω - ∑ i ∈ Finset.range (r + 1), f i ω) hmS (hX.sub hmS) hs1 hri _ _ hpos hβ
      hs2 hrle'
    have e2 : ∀ ω, ∑ i ∈ Finset.range (r + 1), f i ω + (X ω - ∑ i ∈ Finset.range (r + 1), f i ω)
        = X ω := fun ω => by abel
    simp only [e2] at h3 h4
    refine ⟨h3, ?_⟩
    have hgs : ∑ i ∈ Finset.range (r + 1), q ^ i ≤ 1 / (1 - q) := by
      have := geom_sum_Ico_le_of_lt_one (m := 0) (n := r + 1) hq0 hq1
      rw [← Finset.range_eq_Ico, pow_zero] at this
      exact this
    have hb : σ * q ^ (r + 2) / Real.sqrt (1 - q ^ 2) = σ * q ^ 2 / Real.sqrt (1 - q ^ 2) * q ^ r := by
      rw [pow_add]; ring
    calc Real.sqrt _ ≤ Real.sqrt ((A * ∑ i ∈ Finset.range (r + 1), q ^ i +
            σ * q ^ (r + 2) / Real.sqrt (1 - q ^ 2)) ^ 2) := Real.sqrt_le_sqrt h4
      _ = A * ∑ i ∈ Finset.range (r + 1), q ^ i + σ * q ^ (r + 2) / Real.sqrt (1 - q ^ 2) :=
          Real.sqrt_sq (by positivity)
      _ ≤ _ := by
          rw [hb]
          have := mul_le_mul_of_nonneg_left hgs hA0.le
          linarith
  refine ⟨(key 0).1, ?_⟩
  have hlim : Filter.Tendsto (fun r : ℕ => A * (1 / (1 - q)) + σ * q ^ 2 / Real.sqrt (1 - q ^ 2) * q ^ r)
      Filter.atTop (nhds (A * (1 / (1 - q)) + σ * q ^ 2 / Real.sqrt (1 - q ^ 2) * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1))
  rw [mul_zero, add_zero] at hlim
  exact ge_of_tendsto' hlim fun r => (key r).2
