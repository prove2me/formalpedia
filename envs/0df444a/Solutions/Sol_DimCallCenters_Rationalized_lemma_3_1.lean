-- Prove2me | solution 1 for DimCallCenters.Rationalized.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T06:14:10.323295+00:00
-- url     : https://prove2.me/submissions/ab75245d-0c5b-4543-99ff-87d6dfd2a1a7

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Clam
import Definitions.Def_DimCallCenters_Rationalized_surrogate

open Filter Topology

lemma lemma31_key_04b280d0 (a b s t : ℝ) (hab : a ≤ b) (hts : t ≤ s)
    (h1 : 1 / 2 < a / s) (h2 : 1 / 2 < b / t) :
    |b / a - 1| ≤ |(b / t) * (s / a) - 1| := by
  have h1' : 0 < a / s := lt_trans (by norm_num) h1
  have h2' : 0 < b / t := lt_trans (by norm_num) h2
  rcases div_pos_iff.mp h1' with ⟨ha, hs⟩ | ⟨ha, hs⟩
  · have hb : 0 < b := lt_of_lt_of_le ha hab
    have ht : 0 < t := by
      rcases div_pos_iff.mp h2' with ⟨_, ht⟩ | ⟨hb', _⟩
      · exact ht
      · exact absurd hb (not_lt.mpr hb'.le)
    have hge : 1 ≤ b / a := (one_le_div ha).mpr hab
    have hle : b / a ≤ (b / t) * (s / a) := by
      rw [div_mul_div_comm, div_le_div_iff₀ ha (mul_pos ht ha)]
      have : b * t ≤ b * s := mul_le_mul_of_nonneg_left hts hb.le
      nlinarith
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · have ht : t < 0 := lt_of_le_of_lt hts hs
    have hb : b < 0 := by
      rcases div_pos_iff.mp h2' with ⟨hb', ht'⟩ | ⟨hb', _⟩
      · exact absurd ht (not_lt.mpr ht'.le)
      · exact hb'
    have hle : b / a ≤ 1 := (div_le_one_of_neg ha).mpr hab
    have hge : (b / t) * (s / a) ≤ b / a := by
      have heq : b / a = (b / t) * (s / a) * (t / s) := by
        have e : b / t * (s / a) * (t / s) = b / a * ((t / t) * (s / s)) := by ring
        rw [e, div_self ht.ne, div_self hs.ne]
        ring
      have hts1 : 1 ≤ t / s := by
        rw [← neg_div_neg_eq]
        exact (one_le_div (by linarith)).mpr (by linarith)
      have huv : 0 < (b / t) * (s / a) := mul_pos h2' (div_pos_of_neg_of_neg hs ha)
      rw [heq]
      exact le_mul_of_one_le_right huv.le hts1
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

open DimCallCenters.Rationalized Filter Topology in
theorem solution (M : WaitModel) (F : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (Fh pih Gh : ℝ → ℝ → ℝ) (x z : ℝ → ℝ)
    (hx : ∀ lam : ℝ, 0 < lam → 0 < x lam ∧
      ∀ x' : ℝ, 0 < x' → Clam M F lam (x lam) ≤ Clam M F lam x')
    (hz : ∀ lam : ℝ, 0 < lam → 0 < z lam ∧
      ∀ z' : ℝ, 0 < z' →
        surrogate (Fh lam) (pih lam) (Gh lam) (z lam) ≤ surrogate (Fh lam) (pih lam) (Gh lam) z')
    (hxapprox : Tendsto (fun lam => Clam M F lam (x lam) /
      surrogate (Fh lam) (pih lam) (Gh lam) (x lam)) atTop (𝓝 1))
    (hzapprox : Tendsto (fun lam => Clam M F lam (z lam) /
      surrogate (Fh lam) (pih lam) (Gh lam) (z lam)) atTop (𝓝 1)) :
    Tendsto (fun lam => Clam M F lam (z lam) / Clam M F lam (x lam)) atTop (𝓝 1) := by
  have hinv := hxapprox.inv₀ one_ne_zero
  simp only [inv_div, inv_one] at hinv
  have hr := hzapprox.mul hinv
  rw [mul_one] at hr
  have hr0 : Tendsto (fun lam => |Clam M F lam (z lam) /
      surrogate (Fh lam) (pih lam) (Gh lam) (z lam) *
      (surrogate (Fh lam) (pih lam) (Gh lam) (x lam) / Clam M F lam (x lam)) - 1|) atTop (𝓝 0) := by
    have := (hr.sub_const 1).abs
    simpa using this
  have e1 := hxapprox.eventually (lt_mem_nhds (show (1:ℝ)/2 < 1 by norm_num))
  have e2 := hzapprox.eventually (lt_mem_nhds (show (1:ℝ)/2 < 1 by norm_num))
  have e3 : ∀ᶠ lam : ℝ in atTop, 0 < lam := eventually_gt_atTop 0
  have hmain : Tendsto (fun lam => Clam M F lam (z lam) / Clam M F lam (x lam) - 1) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hr0
    filter_upwards [e1, e2, e3] with lam h1 h2 hlam
    rw [Real.norm_eq_abs]
    exact lemma31_key_04b280d0 _ _ _ _ ((hx lam hlam).2 _ (hz lam hlam).1)
      ((hz lam hlam).2 _ (hx lam hlam).1) h1 h2
  simpa using hmain.add_const 1
