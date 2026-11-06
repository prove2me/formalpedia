-- Prove2me | solution 1 for DROOptimal.Predictor.proposition_1_iii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T09:50:29.673521+00:00
-- url     : https://prove2.me/submissions/499f3d48-4701-4a28-82fd-b109f1d1b5e9

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting

open DROOptimal.Predictor Filter Topology

namespace DROm4P3

lemma coord_cont {d : ℕ} (i : Fin d) : Continuous (fun q : Δ d => (q : Fin d → ℝ) i) :=
  (continuous_apply i).comp continuous_subtype_val

lemma coord_nonneg {d : ℕ} (q : Δ d) (i : Fin d) : 0 ≤ (q : Fin d → ℝ) i := q.2.1 i

lemma coord_le_one {d : ℕ} (q : Δ d) (i : Fin d) : (q : Fin d → ℝ) i ≤ 1 := by
  have := Finset.single_le_sum (fun j _ => q.2.1 j) (Finset.mem_univ i)
  rw [q.2.2] at this; exact this

lemma coord_sum {d : ℕ} (q : Δ d) : ∑ i, (q : Fin d → ℝ) i = 1 := q.2.2

/-- a log(a/b) ≥ a − b. -/
lemma mul_log_div_ge_sub (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    a - b ≤ a * Real.log (a / b) := by
  rcases ha.eq_or_lt with h | h
  · subst h; simp; linarith
  · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos h hb)
    rw [inv_div] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 h.le
    have h3 : a * (b / a) = b := by field_simp
    rw [mul_sub, mul_one, h3] at h2
    exact h2

lemma mul_log_div_eq (a b : ℝ) (hb : b ≠ 0) :
    a * Real.log (a / b) = a * Real.log a - a * Real.log b := by
  rcases eq_or_ne a 0 with h | h
  · subst h; simp
  · rw [Real.log_div h hb]; ring

lemma mul_le_abs (a t : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : a * t ≤ |t| := by
  nlinarith [le_abs_self t, abs_nonneg t, neg_abs_le t]

/-- Joint lower semicontinuity of the relative entropy on 𝒫 × 𝒫. -/
lemma relEntropy_lsc {d : ℕ} :
    LowerSemicontinuous (fun pq : Δ d × Δ d => relEntropy pq.1 pq.2) := by
  classical
  rintro ⟨p, q⟩ y hy
  change y < relEntropy p q at hy
  have c1 : ∀ i, Continuous (fun pq : Δ d × Δ d => (pq.1 : Fin d → ℝ) i) :=
    fun i => (coord_cont i).comp continuous_fst
  have c2 : ∀ i, Continuous (fun pq : Δ d × Δ d => (pq.2 : Fin d → ℝ) i) :=
    fun i => (coord_cont i).comp continuous_snd
  by_cases hc : ∀ i, (q : Fin d → ℝ) i = 0 → (p : Fin d → ℝ) i = 0
  · let G : Δ d × Δ d → ℝ := fun pq => ∑ i,
      if (q : Fin d → ℝ) i = 0 then (pq.1 : Fin d → ℝ) i - (pq.2 : Fin d → ℝ) i
      else (pq.1 : Fin d → ℝ) i * Real.log ((pq.1 : Fin d → ℝ) i / (pq.2 : Fin d → ℝ) i)
    have hGeq : relEntropy p q = (G (p, q) : EReal) := by
      simp only [relEntropy, if_pos hc, G]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      split_ifs with h
      · simp [h, hc i h]
      · rfl
    have hGc : ContinuousAt G (p, q) := by
      refine tendsto_finsetSum _ (fun i _ => ?_)
      by_cases h : (q : Fin d → ℝ) i = 0
      · simp only [if_pos h]
        exact ((c1 i).continuousAt (x := (p, q))).sub ((c2 i).continuousAt (x := (p, q)))
      · simp only [if_neg h]
        have hq : 0 < (q : Fin d → ℝ) i := lt_of_le_of_ne (coord_nonneg q i) (Ne.symm h)
        have hev : (fun pq : Δ d × Δ d => (pq.1 : Fin d → ℝ) i * Real.log ((pq.1 : Fin d → ℝ) i /
            (pq.2 : Fin d → ℝ) i)) =ᶠ[𝓝 (p, q)] (fun pq => (pq.1 : Fin d → ℝ) i *
            Real.log ((pq.1 : Fin d → ℝ) i) - (pq.1 : Fin d → ℝ) i *
            Real.log ((pq.2 : Fin d → ℝ) i)) := by
          filter_upwards [(c2 i).continuousAt.eventually (lt_mem_nhds hq)] with pq hpq
          exact mul_log_div_eq _ _ hpq.ne'
        refine ContinuousAt.congr ?_ hev.symm
        exact (Real.continuous_mul_log.comp (c1 i)).continuousAt.sub
          ((c1 i).continuousAt.mul ((c2 i).continuousAt.log hq.ne'))
    rw [hGeq] at hy
    obtain ⟨R, hyR, hRG⟩ := EReal.lt_iff_exists_real_btwn.mp hy
    have hRG' : R < G (p, q) := by exact_mod_cast hRG
    filter_upwards [hGc.eventually (lt_mem_nhds hRG')] with pq hpq
    change y < relEntropy pq.1 pq.2
    by_cases hc' : ∀ i, (pq.2 : Fin d → ℝ) i = 0 → (pq.1 : Fin d → ℝ) i = 0
    · simp only [relEntropy, if_pos hc']
      refine lt_of_lt_of_le hyR ?_
      have hle : G pq ≤ ∑ i, (pq.1 : Fin d → ℝ) i *
          Real.log ((pq.1 : Fin d → ℝ) i / (pq.2 : Fin d → ℝ) i) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        split_ifs with h
        · rcases (coord_nonneg pq.2 i).eq_or_lt with h2 | h2
          · rw [← h2, hc' i h2.symm]; simp
          · exact mul_log_div_ge_sub _ _ (coord_nonneg pq.1 i) h2
        · exact le_rfl
      exact_mod_cast (hpq.le.trans hle)
    · simp only [relEntropy, if_neg hc']
      exact lt_of_lt_of_le hyR le_top
  · push Not at hc
    obtain ⟨j, hqj, hpj⟩ := hc
    have hpj' : 0 < (p : Fin d → ℝ) j := lt_of_le_of_ne (coord_nonneg p j) (Ne.symm hpj)
    obtain ⟨R, hR⟩ : ∃ R : ℝ, y ≤ (R : EReal) := by
      induction y using EReal.rec with
      | bot => exact ⟨0, bot_le⟩
      | coe a => exact ⟨a, le_rfl⟩
      | top => exact absurd hy (not_lt.mpr le_top)
    set A : ℝ := |R| + d + 1 with hAdef
    have hA : 0 ≤ A := by positivity
    set h2 : ℝ := (p : Fin d → ℝ) j / 2 with hh2def
    have hh2 : 0 < h2 := by positivity
    set δ : ℝ := h2 * Real.exp (-(A / h2)) with hδdef
    have hδ : 0 < δ := mul_pos hh2 (Real.exp_pos _)
    have ev1 : ∀ᶠ pq : Δ d × Δ d in 𝓝 (p, q), (pq.2 : Fin d → ℝ) j < δ :=
      (c2 j).continuousAt.eventually (gt_mem_nhds (by simpa [hqj] using hδ))
    have ev2 : ∀ᶠ pq : Δ d × Δ d in 𝓝 (p, q), h2 < (pq.1 : Fin d → ℝ) j :=
      (c1 j).continuousAt.eventually (lt_mem_nhds (by
        change (p : Fin d → ℝ) j / 2 < (p : Fin d → ℝ) j; linarith))
    filter_upwards [ev1, ev2] with pq hq' hp'
    change y < relEntropy pq.1 pq.2
    by_cases hc' : ∀ i, (pq.2 : Fin d → ℝ) i = 0 → (pq.1 : Fin d → ℝ) i = 0
    · simp only [relEntropy, if_pos hc']
      refine lt_of_le_of_lt hR ?_
      have hqj' : 0 < (pq.2 : Fin d → ℝ) j :=
        lt_of_le_of_ne (coord_nonneg _ j) (fun h => (ne_of_gt (hh2.trans hp')) (hc' j h.symm))
      have hterm : ∀ i, -1 ≤ (pq.1 : Fin d → ℝ) i *
          Real.log ((pq.1 : Fin d → ℝ) i / (pq.2 : Fin d → ℝ) i) := by
        intro i
        rcases (coord_nonneg pq.2 i).eq_or_lt with h | h
        · rw [← h, hc' i h.symm]; simp
        · have := mul_log_div_ge_sub _ _ (coord_nonneg pq.1 i) h
          linarith [coord_nonneg pq.1 i, coord_le_one pq.2 i]
      have hj : A ≤ (pq.1 : Fin d → ℝ) j *
          Real.log ((pq.1 : Fin d → ℝ) j / (pq.2 : Fin d → ℝ) j) := by
        have hratio : h2 / δ ≤ (pq.1 : Fin d → ℝ) j / (pq.2 : Fin d → ℝ) j := by
          rw [div_le_div_iff₀ hδ hqj']
          nlinarith
        have hlog : Real.log (h2 / δ) = A / h2 := by
          rw [hδdef, div_mul_eq_div_div, div_self hh2.ne', one_div, Real.log_inv,
            Real.log_exp, neg_neg]
        have hl : A / h2 ≤ Real.log ((pq.1 : Fin d → ℝ) j / (pq.2 : Fin d → ℝ) j) :=
          hlog ▸ Real.log_le_log (div_pos hh2 hδ) hratio
        calc A = h2 * (A / h2) := by field_simp
          _ ≤ (pq.1 : Fin d → ℝ) j * (A / h2) :=
              mul_le_mul_of_nonneg_right hp'.le (div_nonneg hA hh2.le)
          _ ≤ _ := mul_le_mul_of_nonneg_left hl (by linarith)
      have hsum := Finset.single_le_sum (f := fun i =>
          (pq.1 : Fin d → ℝ) i * Real.log ((pq.1 : Fin d → ℝ) i / (pq.2 : Fin d → ℝ) i) + 1)
        (fun i _ => by linarith [hterm i]) (Finset.mem_univ j)
      rw [Finset.sum_add_distrib] at hsum
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one] at hsum
      have : R < ∑ i, (pq.1 : Fin d → ℝ) i *
          Real.log ((pq.1 : Fin d → ℝ) i / (pq.2 : Fin d → ℝ) i) := by
        have := le_abs_self R
        linarith
      exact_mod_cast this
    · simp only [relEntropy, if_neg hc']
      exact lt_of_le_of_lt hR (EReal.coe_lt_top R)

end DROm4P3

theorem solution {d : ℕ} :
    LowerSemicontinuous (fun q : Δ d × Δ d => relEntropy q.1 q.2) :=
  DROm4P3.relEntropy_lsc
