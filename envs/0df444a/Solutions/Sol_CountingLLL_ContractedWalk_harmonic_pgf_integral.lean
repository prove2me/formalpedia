-- Prove2me | solution 1 for CountingLLL.ContractedWalk.harmonic_pgf_integral
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:10:57.646211+00:00
-- url     : https://prove2.me/submissions/27398cbe-bcfe-448b-a6b1-9f4d93a1f164

import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Interval BigOperators

/-- Fubini for a finite harmonic sum stopped at an integrable random index. -/
private theorem harmonic_pgf_fubini {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (K : β → ℕ) (hK : Measurable K) (hKi : Integrable (fun x => (K x : ℝ)) ν) :
    (∫ x, ∑ k ∈ Finset.range (K x), (1 : ℝ)/(k+2) ∂ν) =
      ∫ z in (0:ℝ)..1, ∫ x, ∑ k ∈ Finset.range (K x), z^(k+1) ∂ν := by
  classical
  let σ : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1)
  let S : ℝ × β → ℝ := fun p => if p.1 ∈ Set.Icc (0:ℝ) 1 then ∑ k ∈ Finset.range (K p.2), p.1^(k+1) else 0
  have hm : Measurable (fun p : ℝ × ℕ => ∑ k ∈ Finset.range p.2, p.1^(k+1)) := by
    apply measurable_from_prod_countable_left
    intro n
    change Measurable (fun z : ℝ => ∑ k ∈ Finset.range n, z^(k+1))
    exact Finset.measurable_fun_sum _ (fun k hk => (measurable_id : Measurable (fun z : ℝ => z)).pow measurable_const)
  have hS : Measurable S := by
    apply Measurable.ite (measurableSet_Icc.preimage measurable_fst)
    · exact hm.comp (measurable_fst.prodMk (hK.comp measurable_snd))
    · exact measurable_const
  have hbound (z : ℝ) (x : β) (hz : z ∈ Set.Icc (0:ℝ) 1) :
      0 ≤ ∑ k ∈ Finset.range (K x), z^(k+1) ∧ ∑ k ∈ Finset.range (K x), z^(k+1) ≤ (K x : ℝ) := by
    constructor
    · exact Finset.sum_nonneg (fun k hk => pow_nonneg hz.1 _)
    · calc
        _ ≤ ∑ _k ∈ Finset.range (K x), (1:ℝ) := Finset.sum_le_sum (fun k hk => pow_le_one₀ hz.1 hz.2)
        _ = (K x : ℝ) := by simp
  have hSi : Integrable S (σ.prod ν) := by
    apply (hKi.comp_snd σ).mono' hS.aestronglyMeasurable
    filter_upwards with p
    by_cases hz : p.1 ∈ Set.Icc (0:ℝ) 1
    · simp only [S, if_pos hz, Real.norm_eq_abs, abs_of_nonneg (hbound p.1 p.2 hz).1]
      exact (hbound p.1 p.2 hz).2
    · simp only [S, if_neg hz, norm_zero]
      exact Nat.cast_nonneg _
  have houter (x : β) : (∫ z, S (z,x) ∂σ) = ∑ k ∈ Finset.range (K x), (1:ℝ)/(k+2) := by
    have heq : (∫ z, S (z,x) ∂σ) = ∫ z in (0:ℝ)..1, ∑ k ∈ Finset.range (K x), z^(k+1) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
      simp only [S, if_pos (Set.Ioc_subset_Icc_self hz)]
    rw [heq, intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [integral_pow]
      simp [Nat.cast_add, add_assoc]
      norm_num
    · intro k hk
      exact (continuous_id.pow _).intervalIntegrable _ _
  have hinner (z : ℝ) (hz : z ∈ Set.Ioc (0:ℝ) 1) :
      (∫ x, S (z,x) ∂ν) = ∫ x, ∑ k ∈ Finset.range (K x), z^(k+1) ∂ν := by
    congr 1
    funext x
    simp only [S, if_pos (Set.Ioc_subset_Icc_self hz)]
  have houter' : (∫ z, ∫ x, S (z,x) ∂ν ∂σ) = ∫ z in (0:ℝ)..1, ∫ x, ∑ k ∈ Finset.range (K x), z^(k+1) ∂ν := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    exact hinner z hz
  calc
    _ = ∫ x, ∫ z, S (z,x) ∂σ ∂ν := by simp_rw [houter]
    _ = ∫ p, S p ∂(σ.prod ν) := (integral_prod_symm S hSi).symm
    _ = ∫ z, ∫ x, S (z,x) ∂ν ∂σ := integral_prod S hSi
    _ = _ := houter'

private theorem powers_geom (z : ℝ) (n : ℕ) (hz : z ≠ 1) :
    (∑ k ∈ Finset.range n, z^(k+1)) = z*(1-z^n)/(1-z) := by
  have hgeom := geom_sum_mul_neg z n
  have hz' : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  apply (eq_div_iff hz').2
  simp_rw [pow_succ, ← Finset.sum_mul]
  have hm := congrArg (fun r : ℝ => r*z) hgeom
  nlinarith [hm]

/-- Harmonic expectation as an integral of the probability generating function. -/
theorem solution {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (K : β → ℕ) (hK : Measurable K) (hKi : Integrable (fun x => (K x : ℝ)) ν) :
    (∫ x, ∑ k ∈ Finset.range (K x), (1 : ℝ)/(k+2) ∂ν) =
      ∫ z in (0:ℝ)..1, z*(1-(∫ x, z^K x ∂ν))/(1-z) := by
  rw [harmonic_pgf_fubini ν K hK hKi]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae ((volume : Measure ℝ).ae_ne (1:ℝ))] with z hz hz1
  have hz0 : 0 ≤ z := le_of_lt hz.1
  have hpow : Integrable (fun x => z^(K x)) ν := by
    apply (integrable_const (1:ℝ)).mono' ((measurable_const.pow hK).aestronglyMeasurable)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hz0 _)]
    exact pow_le_one₀ hz0 hz.2
  have heq (x : β) : (∑ k ∈ Finset.range (K x), z^(k+1)) = (z/(1-z))*(1-z^K x) := by
    rw [powers_geom z (K x) hz1]
    ring
  simp_rw [heq]
  rw [integral_const_mul, integral_sub (integrable_const 1) hpow]
  simp
  ring
