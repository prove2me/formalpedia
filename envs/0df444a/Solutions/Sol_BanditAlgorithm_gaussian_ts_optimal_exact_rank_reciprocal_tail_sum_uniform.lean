-- Prove2me | solution 1 for BanditAlgorithm.gaussian_ts_optimal_exact_rank_reciprocal_tail_sum_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T02:05:03.163125+00:00
-- url     : https://prove2.me/submissions/b1363859-19ac-45b3-9a6f-a83598b710dd

import Theorems.Thm_BanditAlgorithm_gaussian_exact_rank_reciprocal_tail_exponential_bound
import Mathlib.Analysis.SumIntegralExpDecay
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm

private theorem measurable_gaussianReal_real_Ioi_opt (c : ℝ) :
    Measurable (fun p : ℝ × NNReal ↦ (gaussianReal p.1 p.2).real (Set.Ioi c)) := by
  have hpdf :
      Measurable
        (fun p : (ℝ × NNReal) × ℝ ↦ gaussianPDF p.1.1 p.1.2 p.2) := by
    rw [show
      (fun p : (ℝ × NNReal) × ℝ ↦ gaussianPDF p.1.1 p.1.2 p.2) =
        fun p ↦ ENNReal.ofReal
          ((Real.sqrt (2 * Real.pi * (p.1.2 : ℝ)))⁻¹ *
            Real.exp (-((p.2 - p.1.1) ^ 2) / (2 * (p.1.2 : ℝ)))) by
      funext p
      rfl]
    fun_prop
  have hint :
      Measurable
        (fun p : ℝ × NNReal ↦
          (∫⁻ x in Set.Ioi c, gaussianPDF p.1 p.2 x).toReal) := by
    apply Measurable.ennreal_toReal
    have hrestricted :
        Measurable
          (fun z : (ℝ × NNReal) × ℝ ↦
            (Set.Ioi c).indicator
              (fun x ↦ gaussianPDF z.1.1 z.1.2 x) z.2) :=
      hpdf.indicator
        (measurableSet_Ioi.preimage measurable_snd)
    simpa only [lintegral_indicator measurableSet_Ioi] using
      (hrestricted.lintegral_prod_right' (ν := (volume : Measure ℝ)))
  have hzero :
      Measurable
        (fun p : ℝ × NNReal ↦ if c < p.1 then (1 : ℝ) else 0) :=
    Measurable.ite
      (measurableSet_lt measurable_const measurable_fst)
      measurable_const measurable_const
  have heq :
      (fun p : ℝ × NNReal ↦ (gaussianReal p.1 p.2).real (Set.Ioi c)) =
        fun p ↦ if p.2 = 0 then
          (if c < p.1 then 1 else 0)
        else
          (∫⁻ x in Set.Ioi c, gaussianPDF p.1 p.2 x).toReal := by
    funext p
    by_cases hp : p.2 = 0
    · rw [if_pos hp, hp, gaussianReal_zero_var]
      by_cases hc : c < p.1 <;> simp [Measure.real, Set.indicator, hc]
    · rw [if_neg hp, Measure.real, gaussianReal_apply p.1 hp]
  rw [heq]
  exact Measurable.ite
    ((measurableSet_singleton (0 : NNReal)).preimage measurable_snd)
    hzero hint

private theorem armPullCount_eq_sum_indicator_opt {k m : ℕ}
    (i : Fin k) (h : BanditHistory k m) :
    armPullCount i h =
      ∑ t : Fin m, if (h t).1 = i then 1 else 0 := by
  classical
  rw [armPullCount]
  have hset :
      {t | (h t).1 = i}.toFinset =
        Finset.univ.filter fun t ↦ (h t).1 = i := by
    ext t
    simp
  rw [hset]
  simpa using
    (Finset.sum_boole (R := ℕ) (fun t : Fin m ↦ (h t).1 = i)
      Finset.univ).symm

private theorem measurable_armPullCount_opt {k m : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k m ↦ armPullCount i h) := by
  simp_rw [armPullCount_eq_sum_indicator_opt]
  apply Finset.measurable_sum
  intro t ht
  exact Measurable.ite
    ((measurableSet_singleton i).preimage
      (measurable_fst.comp (measurable_pi_apply t)))
    measurable_const measurable_const

private theorem measurable_armPullCountBefore_opt {k n : ℕ}
    (i : Fin k) (t : Fin n) :
    Measurable (fun h : BanditHistory k n ↦ armPullCountBefore i t h) := by
  simp_rw [show ∀ h : BanditHistory k n,
      armPullCountBefore i t h =
        ∑ u : Fin n, if u < t ∧ (h u).1 = i then 1 else 0 by
    intro h
    unfold armPullCountBefore
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]]
  apply Finset.measurable_sum
  intro u hu
  apply Measurable.ite
  · change MeasurableSet
      {h : BanditHistory k n | u < t ∧ (h u).1 = i}
    by_cases hut : u < t
    · have heq :
          {h : BanditHistory k n | u < t ∧ (h u).1 = i} =
            (fun h : BanditHistory k n ↦ (h u).1) ⁻¹' {i} := by
          ext h
          simp [hut]
      rw [heq]
      exact (measurableSet_singleton i).preimage
        (measurable_fst.comp
          (measurable_pi_apply u :
            Measurable (fun h : BanditHistory k n ↦ h u)))
    · simp [hut]
  · exact measurable_const
  · exact measurable_const

private theorem measurable_armFirstRewardsMean_opt {k n : ℕ}
    (i : Fin k) (s : ℕ) :
    Measurable (fun h : BanditHistory k n ↦ armFirstRewardsMean i s h) := by
  rw [show
    (fun h : BanditHistory k n ↦ armFirstRewardsMean i s h) =
      fun h ↦
        (∑ t : Fin n,
          if (h t).1 = i ∧ armPullCountBefore i t h < s
          then (h t).2 else 0) / s by
    funext h
    unfold armFirstRewardsMean
    simp [Finset.sum_filter]]
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro t ht
  apply Measurable.ite
  · exact MeasurableSet.inter
      ((measurableSet_singleton i).preimage
        (measurable_fst.comp (measurable_pi_apply t)))
      (measurableSet_lt (measurable_armPullCountBefore_opt i t) measurable_const)
  · exact measurable_snd.comp (measurable_pi_apply t)
  · exact measurable_const

private theorem measurable_gaussianTSTailProb_opt {k n : ℕ}
    (i : Fin k) (s : ℕ) (c : ℝ) :
    Measurable (fun h : BanditHistory k n ↦ gaussianTSTailProb i s c h) := by
  unfold gaussianTSTailProb
  by_cases hs : s = 0
  · simp [hs]
  · simp only [hs, if_false]
    have hp : Measurable
        (fun h : BanditHistory k n ↦
          (armFirstRewardsMean i s h, ((s : NNReal))⁻¹)) :=
      (measurable_armFirstRewardsMean_opt i s).prodMk measurable_const
    exact
      (measurable_gaussianReal_real_Ioi_opt c).comp hp

private theorem armPullCount_le_horizon_opt {k n : ℕ}
    (i : Fin k) (h : BanditHistory k n) :
    armPullCount i h ≤ n := by
  rw [armPullCount]
  simpa using Finset.card_le_univ ({t | (h t).1 = i}.toFinset)

private theorem sum_realized_ranks_eq_opt {k n : ℕ}
    (i : Fin k) (h : BanditHistory k n) (f : ℕ → ENNReal) :
    (∑ s ∈ Finset.range (armPullCount i h), f s) =
      ∑ s ∈ Finset.range n,
        if s < armPullCount i h then f s else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_subset
  · intro s hs
    have hslt : s < armPullCount i h := Finset.mem_range.mp hs
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr
        (hslt.trans_le (armPullCount_le_horizon_opt i h)), hslt⟩
  · intro s hsn hsnot
    exact (hsnot (Finset.mem_range.mpr (Finset.mem_filter.mp hsn).2)).elim

end BanditAlgorithm

open BanditAlgorithm

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
        ∀ (i₀ : Fin k),
          banditArmMean (gaussianBandit μvec) i₀ =
            banditOptimalMean (gaussianBandit μvec) →
        ∀ ε : ℝ, 0 < ε →
        ∀ n : ℕ,
          (∫⁻ h, ∑ s ∈ Finset.range (armPullCount i₀ h),
              ENNReal.ofReal
                (1 / gaussianTSTailProb i₀ s
                  (banditArmMean (gaussianBandit μvec) i₀ - ε) h - 1)
              ∂banditMeasure (gaussianBandit μvec) π n) ≤
            ENNReal.ofReal
              (2 * Real.exp (ε ^ 2 / 8) / (ε ^ 2 / 8) +
                (2 * C / ε ^ 2) *
                  (Real.exp (3 * ε ^ 2 / 32) / (3 * ε ^ 2 / 32))) := by
  obtain ⟨C, hC, hrank⟩ :=
    gaussian_exact_rank_reciprocal_tail_exponential_bound
  refine ⟨C, hC, ?_⟩
  intro k _ μvec π i₀ hi₀ ε hε n
  let f : ℕ → BanditHistory k n → ENNReal := fun s h ↦
    if s < armPullCount i₀ h then
      ENNReal.ofReal
        (1 / gaussianTSTailProb i₀ s
          (banditArmMean (gaussianBandit μvec) i₀ - ε) h - 1)
    else 0
  have hf (s : ℕ) : Measurable (f s) := by
    apply Measurable.ite
    · exact measurableSet_lt measurable_const (measurable_armPullCount_opt i₀)
    · exact ((measurable_const.div
        (measurable_gaussianTSTailProb_opt i₀ s
          (banditArmMean (gaussianBandit μvec) i₀ - ε))).sub_const 1).ennreal_ofReal
    · exact measurable_const
  have hrewrite :
      (fun h : BanditHistory k n ↦
        ∑ s ∈ Finset.range (armPullCount i₀ h),
          ENNReal.ofReal
            (1 / gaussianTSTailProb i₀ s
              (banditArmMean (gaussianBandit μvec) i₀ - ε) h - 1)) =
        fun h ↦ ∑ s ∈ Finset.range n, f s h := by
    funext h
    exact sum_realized_ranks_eq_opt i₀ h
      (fun s ↦ ENNReal.ofReal
        (1 / gaussianTSTailProb i₀ s
          (banditArmMean (gaussianBandit μvec) i₀ - ε) h - 1))
  rw [hrewrite, MeasureTheory.lintegral_finsetSum (Finset.range n)
    (fun s hs ↦ hf s)]
  have hterms :
      (∑ s ∈ Finset.range n,
          ∫⁻ h, f s h ∂banditMeasure (gaussianBandit μvec) π n) ≤
        ∑ s ∈ Finset.range n,
          ENNReal.ofReal
            (2 * Real.exp (-((s : ℝ) * ε ^ 2) / 8) +
              (2 * C / ε ^ 2) *
                Real.exp (-(3 * (s : ℝ) * ε ^ 2) / 32)) := by
    apply Finset.sum_le_sum
    intro s hs
    by_cases hs0 : s = 0
    · subst s
      simpa [f, gaussianTSTailProb] using
        (show (0 : ENNReal) ≤
          ENNReal.ofReal
            (2 * Real.exp (-((0 : ℝ) * ε ^ 2) / 8) +
              (2 * C / ε ^ 2) *
                Real.exp (-(3 * (0 : ℝ) * ε ^ 2) / 32)) from bot_le)
    · have hspos : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs0
      have hbase := hrank k μvec π i₀ s (Nat.pos_of_ne_zero hs0) ε hε n
      apply hbase.trans
      apply ENNReal.ofReal_le_ofReal
      have heps2 : 0 < ε ^ 2 := sq_pos_of_pos hε
      have hexp : 0 ≤ Real.exp (-(3 * (s : ℝ) * ε ^ 2) / 32) :=
        Real.exp_nonneg _
      have hcoef :
          2 * C / ((s : ℝ) * ε ^ 2) ≤ 2 * C / ε ^ 2 := by
        have hC2 : 0 ≤ 2 * C := by positivity
        apply div_le_div_of_nonneg_left hC2 heps2
        have hsone : (1 : ℝ) ≤ s := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hs0)
        nlinarith
      gcongr
  apply hterms.trans
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · apply ENNReal.ofReal_le_ofReal
    have hc₁ : 0 < ε ^ 2 / 8 := by positivity
    have hc₂ : 0 < 3 * ε ^ 2 / 32 := by positivity
    have hsum₁ :
        (∑ s ∈ Finset.range n,
          Real.exp (-((ε ^ 2 / 8) * s))) ≤
            Real.exp (ε ^ 2 / 8) / (ε ^ 2 / 8) := by
      simpa using
        (sum_Ico_pow_mul_exp_neg_le (k := 0) (M := n) hc₁)
    have hsum₂ :
        (∑ s ∈ Finset.range n,
          Real.exp (-((3 * ε ^ 2 / 32) * s))) ≤
            Real.exp (3 * ε ^ 2 / 32) / (3 * ε ^ 2 / 32) := by
      simpa using
        (sum_Ico_pow_mul_exp_neg_le (k := 0) (M := n) hc₂)
    calc
      (∑ s ∈ Finset.range n,
          (2 * Real.exp (-((s : ℝ) * ε ^ 2) / 8) +
            (2 * C / ε ^ 2) *
              Real.exp (-(3 * (s : ℝ) * ε ^ 2) / 32))) =
          2 * (∑ s ∈ Finset.range n,
            Real.exp (-((ε ^ 2 / 8) * s))) +
          (2 * C / ε ^ 2) * (∑ s ∈ Finset.range n,
            Real.exp (-((3 * ε ^ 2 / 32) * s))) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro s hs <;>
          congr 2 <;> ring
      _ ≤ 2 * (Real.exp (ε ^ 2 / 8) / (ε ^ 2 / 8)) +
          (2 * C / ε ^ 2) *
            (Real.exp (3 * ε ^ 2 / 32) / (3 * ε ^ 2 / 32)) := by
        gcongr
      _ = 2 * Real.exp (ε ^ 2 / 8) / (ε ^ 2 / 8) +
          (2 * C / ε ^ 2) *
            (Real.exp (3 * ε ^ 2 / 32) / (3 * ε ^ 2 / 32)) := by
        ring
  · intro s hs
    positivity
