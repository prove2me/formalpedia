-- Prove2me | solution 1 for BookProof.ChapterAttentionEntropy.tendsto_shannonEntropy_bornWeight_smul_query
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:26:35.512154+00:00
-- url     : https://prove2.me/submissions/49215bc4-f32a-4708-abf6-0375651e0106

-- Generated from ChapterAttentionEntropy.lean — theorem BookProof.ChapterAttentionEntropy.tendsto_shannonEntropy_bornWeight_smul_query
import Mathlib
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxBorn
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

theorem tendsto_shannonEntropy_scoreSoftmax (s : Fin m → ℝ) (j : Fin m)
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

theorem coherentBorn_sq_eq (q k : EuclideanSpace ℝ (Fin n)) :
    bornNumer q k =
      Real.exp (-‖q‖ ^ 2) * Real.exp (-‖k‖ ^ 2) * Real.exp (2 * inner ℝ q k) := by
  rw [bornNumer, coherentOverlap, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem coherentBorn_cancel_q (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    bornWeight q k j =
      Real.exp (-‖k j‖ ^ 2) * Real.exp (2 * inner ℝ q (k j)) /
        ∑ l, Real.exp (-‖k l‖ ^ 2) * Real.exp (2 * inner ℝ q (k l)) := by
  have hc : (0 : ℝ) < Real.exp (-‖q‖ ^ 2) := Real.exp_pos _
  have hsum : ∑ l, bornNumer q (k l)
      = Real.exp (-‖q‖ ^ 2) *
        ∑ l, Real.exp (-‖k l‖ ^ 2) * Real.exp (2 * inner ℝ q (k l)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [coherentBorn_sq_eq]
    ring
  rw [bornWeight, hsum, coherentBorn_sq_eq]
  rw [mul_assoc, mul_div_mul_left _ _ (ne_of_gt hc)]

theorem coherentBorn_eq_softmax (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j : Fin m) :
    bornWeight q k j = softmax 2 q k j := by
  have hc : (0 : ℝ) < Real.exp (-r ^ 2) := Real.exp_pos _
  rw [coherentBorn_cancel_q, softmax]
  have hnum : Real.exp (-‖k j‖ ^ 2) * Real.exp (2 * inner ℝ q (k j))
      = Real.exp (-r ^ 2) * Real.exp (2 * inner ℝ q (k j)) := by rw [hk j]
  have hden : ∑ l, Real.exp (-‖k l‖ ^ 2) * Real.exp (2 * inner ℝ q (k l))
      = Real.exp (-r ^ 2) * ∑ l, Real.exp (2 * inner ℝ q (k l)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hk l]
  rw [hnum, hden, mul_div_mul_left _ _ (ne_of_gt hc)]

theorem softmax_smul_query (beta c : ℝ) (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    softmax beta (c • q) k j = softmax (beta * c) q k j := by
  have hinner : ∀ l, (inner ℝ (c • q) (k l) : ℝ) = c * inner ℝ q (k l) := fun l =>
    real_inner_smul_left _ _ _
  have hexp : ∀ l, Real.exp (beta * inner ℝ (c • q) (k l))
      = Real.exp (beta * c * inner ℝ q (k l)) := by
    intro l
    rw [hinner]
    ring_nf
  rw [softmax, softmax, hexp j]
  exact congrArg _ (Finset.sum_congr rfl fun l _ => hexp l)

theorem softmax_eq_scoreSoftmax (beta : ℝ) (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    softmax beta q k j = scoreSoftmax beta (fun l => inner ℝ q (k l)) j := rfl

theorem solution {n : ℕ}
    (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hk : ∀ l, ‖k l‖ = r) (j : Fin m)
    (hmax : ∀ l, l ≠ j → (inner ℝ q (k l) : ℝ) < inner ℝ q (k j)) :
    Tendsto (fun c : ℝ => shannonEntropy (fun l => bornWeight (c • q) k l)) atTop (𝓝 0) := by
  have hrewrite : ∀ c : ℝ, (fun l => bornWeight (c • q) k l)
      = fun l => scoreSoftmax (2 * c) (fun i => inner ℝ q (k i)) l := by
    intro c
    funext l
    rw [coherentBorn_eq_softmax (c • q) k r hk l, softmax_smul_query, softmax_eq_scoreSoftmax]
  have hscale : Tendsto (fun c : ℝ => 2 * c) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop (by norm_num)
  have hlim := (tendsto_shannonEntropy_scoreSoftmax (fun i => inner ℝ q (k i)) j hmax).comp hscale
  change Tendsto (fun c : ℝ => shannonEntropy (fun l => scoreSoftmax (2 * c) (fun i => inner ℝ q (k i)) l)) atTop (𝓝 0) at hlim
  simpa only [hrewrite] using hlim

#print axioms solution
