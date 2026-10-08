-- Prove2me | solution 1 for FreedmanTail.Bernstein.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:40:55.061912+00:00
-- url     : https://prove2.me/submissions/7516154d-7be5-4991-84d1-03dce9f94149

import Mathlib



namespace FreedmanTail.Bernstein

/-- `G x = (x-2) e^x + x + 2`, with `G' x = (x-1)e^x + 1 > 0` for `x ≠ 0`. -/
lemma fb_G_deriv (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y - 2) * Real.exp y + y + 2) ((x - 1) * Real.exp x + 1) x := by
  have h1 : HasDerivAt (fun y : ℝ => y - 2) 1 x := (hasDerivAt_id x).sub_const 2
  have h2 := (h1.mul (Real.hasDerivAt_exp x)).add (hasDerivAt_id x)
  have h3 := h2.add_const 2
  exact h3.congr_deriv (by ring)

lemma fb_Gp_pos (x : ℝ) (hx : x ≠ 0) : 0 < (x - 1) * Real.exp x + 1 := by
  have h := Real.add_one_lt_exp (neg_ne_zero.mpr hx)
  have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos x
  nlinarith

lemma fb_G_pos (x : ℝ) (hx : 0 < x) : 0 < (x - 2) * Real.exp x + x + 2 := by
  have hmono : StrictMonoOn (fun y : ℝ => (y - 2) * Real.exp y + y + 2) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact (continuous_id.sub continuous_const).mul Real.continuous_exp |>.add continuous_id
        |>.add continuous_const |>.continuousOn
    · intro y hy
      rw [interior_Ici] at hy
      rw [(fb_G_deriv y).deriv]
      exact fb_Gp_pos y (ne_of_gt hy)
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx.le) hx
  simpa using this

lemma fb_G_neg (x : ℝ) (hx : x < 0) : (x - 2) * Real.exp x + x + 2 < 0 := by
  have hmono : StrictMonoOn (fun y : ℝ => (y - 2) * Real.exp y + y + 2) (Set.Iic 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Iic 0)
    · exact (continuous_id.sub continuous_const).mul Real.continuous_exp |>.add continuous_id
        |>.add continuous_const |>.continuousOn
    · intro y hy
      rw [interior_Iic] at hy
      rw [(fb_G_deriv y).deriv]
      exact fb_Gp_pos y (ne_of_lt hy)
  have := hmono (Set.mem_Iic.mpr hx.le) (Set.mem_Iic.mpr le_rfl) hx
  simpa using this

/-- the quotient function -/
lemma fb_q_deriv (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => (Real.exp y - 1 - y) / y ^ 2)
      (((Real.exp x - 1) * x ^ 2 - (Real.exp x - 1 - x) * (2 * x)) / (x ^ 2) ^ 2) x := by
  have h1 : HasDerivAt (fun y : ℝ => Real.exp y - 1 - y) (Real.exp x - 1) x :=
    ((Real.hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id x)
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  exact h1.div h2 (pow_ne_zero 2 hx)

lemma fb_q_deriv_pos (x : ℝ) (hx : x ≠ 0) :
    0 < ((Real.exp x - 1) * x ^ 2 - (Real.exp x - 1 - x) * (2 * x)) / (x ^ 2) ^ 2 := by
  apply div_pos _ (by positivity)
  have : (Real.exp x - 1) * x ^ 2 - (Real.exp x - 1 - x) * (2 * x)
      = x * ((x - 2) * Real.exp x + x + 2) := by ring
  rw [this]
  rcases lt_or_gt_of_ne hx with h | h
  · exact mul_pos_of_neg_of_neg h (fb_G_neg x h)
  · exact mul_pos h (fb_G_pos x h)

noncomputable def fb_g (x : ℝ) : ℝ := if x = 0 then (1 / 2 : ℝ) else (Real.exp x - 1 - x) / x ^ 2

lemma fb_g_hasDerivAt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt fb_g
      (((Real.exp x - 1) * x ^ 2 - (Real.exp x - 1 - x) * (2 * x)) / (x ^ 2) ^ 2) x := by
  apply (fb_q_deriv x hx).congr_of_eventuallyEq
  have : {y : ℝ | y ≠ 0} ∈ nhds x := isOpen_ne.mem_nhds hx
  filter_upwards [this] with y hy
  simp [fb_g, hy]

lemma fb_g_mono_Ioi : StrictMonoOn fb_g (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro y hy
    exact (fb_g_hasDerivAt y (ne_of_gt hy)).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    rw [(fb_g_hasDerivAt y (ne_of_gt hy)).deriv]
    exact fb_q_deriv_pos y (ne_of_gt hy)

lemma fb_g_mono_Iio : StrictMonoOn fb_g (Set.Iio 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Iio 0)
  · intro y hy
    exact (fb_g_hasDerivAt y (ne_of_lt hy)).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Iio] at hy
    rw [(fb_g_hasDerivAt y (ne_of_lt hy)).deriv]
    exact fb_q_deriv_pos y (ne_of_lt hy)

/-- `h x = e^x - 1 - x - x^2/2` is strictly increasing, so has the sign of `x`. -/
lemma fb_h_deriv (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp y - 1 - y - y ^ 2 / 2) (Real.exp x - 1 - x) x := by
  have h1 : HasDerivAt (fun y : ℝ => Real.exp y - 1 - y) (Real.exp x - 1) x :=
    ((Real.hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id x)
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    simpa using (hasDerivAt_pow 2 x).div_const 2
  exact (h1.sub h2).congr_deriv (by ring)

lemma fb_h_cont : Continuous (fun y : ℝ => Real.exp y - 1 - y - y ^ 2 / 2) := by
  fun_prop

lemma fb_h_pos (x : ℝ) (hx : 0 < x) : 0 < Real.exp x - 1 - x - x ^ 2 / 2 := by
  have hmono : StrictMonoOn (fun y : ℝ => Real.exp y - 1 - y - y ^ 2 / 2) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) fb_h_cont.continuousOn
    intro y hy
    rw [interior_Ici] at hy
    rw [(fb_h_deriv y).deriv]
    have := Real.add_one_lt_exp (ne_of_gt (Set.mem_Ioi.mp hy))
    linarith
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx.le) hx
  simpa using this

lemma fb_h_neg (x : ℝ) (hx : x < 0) : Real.exp x - 1 - x - x ^ 2 / 2 < 0 := by
  have hmono : StrictMonoOn (fun y : ℝ => Real.exp y - 1 - y - y ^ 2 / 2) (Set.Iic 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Iic 0) fb_h_cont.continuousOn
    intro y hy
    rw [interior_Iic] at hy
    rw [(fb_h_deriv y).deriv]
    have := Real.add_one_lt_exp (ne_of_lt (Set.mem_Iio.mp hy))
    linarith
  have := hmono (Set.mem_Iic.mpr hx.le) (Set.mem_Iic.mpr le_rfl) hx
  simpa using this

lemma fb_g_gt_half (x : ℝ) (hx : 0 < x) : 1 / 2 < fb_g x := by
  simp only [fb_g, if_neg (ne_of_gt hx)]
  rw [lt_div_iff₀ (by positivity)]
  have := fb_h_pos x hx
  linarith

lemma fb_g_lt_half (x : ℝ) (hx : x < 0) : fb_g x < 1 / 2 := by
  simp only [fb_g, if_neg (ne_of_lt hx)]
  have hx2 : 0 < x ^ 2 := by nlinarith
  rw [div_lt_iff₀ hx2]
  have := fb_h_neg x hx
  linarith

lemma fb_g_strictMono : StrictMono fb_g := by
  intro x y hxy
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rcases lt_trichotomy y 0 with hy | hy | hy
    · exact fb_g_mono_Iio hx hy hxy
    · subst hy; have := fb_g_lt_half x hx; simpa [fb_g] using this
    · exact (fb_g_lt_half x hx).trans (fb_g_gt_half y hy)
  · subst hx
    have := fb_g_gt_half y hxy
    simpa [fb_g] using this
  · exact fb_g_mono_Ioi hx (hx.trans hxy) hxy

theorem lemma_3_1_core :
    StrictMono (fun x : ℝ => if x = 0 then (1 / 2 : ℝ) else (Real.exp x - 1 - x) / x ^ 2) :=
  fb_g_strictMono

end FreedmanTail.Bernstein

open FreedmanTail.Bernstein


theorem solution :
    StrictMono (fun x : ℝ => if x = 0 then (1 / 2 : ℝ) else (Real.exp x - 1 - x) / x ^ 2) := by
  exact lemma_3_1_core
