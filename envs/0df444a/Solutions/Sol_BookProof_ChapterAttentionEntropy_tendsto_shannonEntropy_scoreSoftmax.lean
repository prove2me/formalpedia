-- Prove2me | solution 1 for BookProof.ChapterAttentionEntropy.tendsto_shannonEntropy_scoreSoftmax
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:26:33.529979+00:00
-- url     : https://prove2.me/submissions/38aa8097-c22c-4d3e-9a52-b2bf4c6cc001

-- Generated from ChapterAttentionEntropy.lean — theorem BookProof.ChapterAttentionEntropy.tendsto_shannonEntropy_scoreSoftmax
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionEntropy


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}
open BookProof.ChapterSoftmaxOrder BookProof.ChapterCoherentOverlap
variable {n : ℕ}

theorem scoreSoftmax_eq_inv_sum (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta s j = 1 / ∑ l, Real.exp (beta * (s l - s j)) := by
  have hfac : ∑ l, Real.exp (beta * s l)
      = Real.exp (beta * s j) * ∑ l, Real.exp (beta * (s l - s j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Real.exp_add]
    ring_nf
  rw [scoreSoftmax, hfac, mul_comm, ← div_div, div_self (Real.exp_ne_zero _)]

theorem tendsto_exp_mul_neg (c : ℝ) (hc : c < 0) :
    Tendsto (fun b : ℝ => Real.exp (b * c)) atTop (𝓝 0) := by
  have h : Tendsto (fun b : ℝ => b * c) atTop atBot := by
    simpa using (tendsto_id (α := ℝ)).atTop_mul_const_of_neg hc
  exact Real.tendsto_exp_atBot.comp h

theorem tendsto_scoreSoftmax_denom (s : Fin m → ℝ) (j : Fin m)
    (hmax : ∀ l, l ≠ j → s l < s j) :
    Tendsto (fun b : ℝ => ∑ l, Real.exp (b * (s l - s j))) atTop (𝓝 1) := by
  have h : Tendsto (fun b : ℝ => ∑ l, Real.exp (b * (s l - s j))) atTop
      (𝓝 (∑ l : Fin m, if l = j then (1 : ℝ) else 0)) := by
    refine tendsto_finsetSum _ fun l _ => ?_
    by_cases hl : l = j
    · subst hl
      simp
    · simpa [hl] using tendsto_exp_mul_neg (s l - s j) (by linarith [hmax l hl])
  simpa using h

theorem tendsto_scoreSoftmax_max (s : Fin m → ℝ) (j : Fin m)
    (hmax : ∀ l, l ≠ j → s l < s j) :
    Tendsto (fun b : ℝ => scoreSoftmax b s j) atTop (𝓝 1) := by
  have h := (tendsto_scoreSoftmax_denom s j hmax).inv₀ (by norm_num)
  simpa [scoreSoftmax_eq_inv_sum, one_div] using h

theorem tendsto_scoreSoftmax_ne (s : Fin m → ℝ) (j i : Fin m)
    (hmax : ∀ l, l ≠ j → s l < s j) (hi : i ≠ j) :
    Tendsto (fun b : ℝ => scoreSoftmax b s i) atTop (𝓝 0) := by
  have hnum : Tendsto (fun b : ℝ => Real.exp (b * (s i - s j))) atTop (𝓝 0) :=
    tendsto_exp_mul_neg _ (by linarith [hmax i hi])
  have hden := tendsto_scoreSoftmax_denom s j hmax
  have hquot := hnum.div hden (by norm_num)
  have heq : ∀ b : ℝ, scoreSoftmax b s i
      = Real.exp (b * (s i - s j)) / ∑ l, Real.exp (b * (s l - s j)) := by
    intro b
    have hfac : ∑ l, Real.exp (b * s l)
        = Real.exp (b * s j) * ∑ l, Real.exp (b * (s l - s j)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Real.exp_add]
      ring_nf
    rw [scoreSoftmax, hfac, show Real.exp (b * s i)
        = Real.exp (b * s j) * Real.exp (b * (s i - s j)) by rw [← Real.exp_add]; ring_nf,
      mul_div_mul_left _ _ (Real.exp_ne_zero _)]
  change Tendsto (fun b : ℝ => Real.exp (b * (s i - s j)) / ∑ l, Real.exp (b * (s l - s j))) atTop (𝓝 (0 / 1)) at hquot
  simpa only [heq, zero_div] using hquot

theorem solution (s : Fin m → ℝ) (j : Fin m)
    (hmax : ∀ l, l ≠ j → s l < s j) :
    Tendsto (fun b : ℝ => shannonEntropy (fun l => scoreSoftmax b s l)) atTop (𝓝 0) := by
  have hterm : ∀ l : Fin m,
      Tendsto (fun b : ℝ => scoreSoftmax b s l * Real.log (scoreSoftmax b s l))
        atTop (𝓝 0) := by
    intro l
    by_cases hl : l = j
    · subst hl
      have h := (Real.continuous_mul_log.tendsto 1).comp (tendsto_scoreSoftmax_max s l hmax)
      change Tendsto (fun b : ℝ => scoreSoftmax b s l * Real.log (scoreSoftmax b s l)) atTop _ at h
      simpa only [Real.log_one, Real.log_zero, mul_zero] using h
    · have h := (Real.continuous_mul_log.tendsto 0).comp (tendsto_scoreSoftmax_ne s j l hmax hl)
      change Tendsto (fun b : ℝ => scoreSoftmax b s l * Real.log (scoreSoftmax b s l)) atTop _ at h
      simpa only [Real.log_one, Real.log_zero, mul_zero] using h
  have hsum : Tendsto
      (fun b : ℝ => ∑ l, scoreSoftmax b s l * Real.log (scoreSoftmax b s l)) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin m))
      (fun l _ => hterm l)
    simpa using h
  simpa [shannonEntropy] using hsum.neg

#print axioms solution
