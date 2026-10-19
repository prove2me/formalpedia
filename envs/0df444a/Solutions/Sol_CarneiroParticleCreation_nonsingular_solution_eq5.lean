-- Prove2me | solution 1 for CarneiroParticleCreation.nonsingular_solution_eq5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:43:40.42214+00:00
-- url     : https://prove2.me/submissions/9c461360-ced2-4039-9b89-e11fe0677238

import Mathlib

open Filter Topology Set

namespace CarneiroAux

noncomputable def F (x : ℝ) : ℝ := Real.artanh x - 1 / x

lemma artanh_eq (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Real.artanh x = 1 / 2 * (Real.log (1 + x) - Real.log (1 - x)) := by
  rw [Real.artanh_eq_half_log ⟨hx.1.le, hx.2.le⟩, Real.log_div (by linarith [hx.1]) (by linarith [hx.2])]

lemma hasDerivAt_artanh (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
  have h1 : 0 < 1 + x := by linarith [hx.1]
  have h2 : 0 < 1 - x := by linarith [hx.2]
  have e : Real.artanh =ᶠ[𝓝 x] fun y => 1 / 2 * (Real.log (1 + y) - Real.log (1 - y)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using artanh_eq y hy
  have := ((((hasDerivAt_id x).const_add 1).log h1.ne').sub
    (((hasDerivAt_id x).const_sub 1).log h2.ne')).const_mul (1 / 2)
  refine (this.congr_deriv ?_).congr_of_eventuallyEq e
  simp only [id]
  rw [show (1 : ℝ) - x ^ 2 = (1 + x) * (1 - x) by ring]
  field_simp
  ring

lemma hasDerivAt_F (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt F (1 / (1 - x ^ 2) + 1 / x ^ 2) x := by
  have h := hasDerivAt_artanh x ⟨by linarith [hx.1], hx.2⟩
  have h2 := (hasDerivAt_inv hx.1.ne')
  have := h.sub h2
  unfold F
  simp only [one_div] at this ⊢
  refine this.congr_deriv ?_
  ring

lemma F'_pos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < 1 / (1 - x ^ 2) + 1 / x ^ 2 := by
  have : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have : 0 < x ^ 2 := by nlinarith [hx.1]
  positivity

lemma F_cont : ContinuousOn F (Ioo 0 1) := fun x hx =>
  (hasDerivAt_F x hx).continuousAt.continuousWithinAt

lemma F_mono : StrictMonoOn F (Ioo 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1) F_cont
  intro x hx
  rw [interior_Ioo] at hx
  rw [(hasDerivAt_F x hx).deriv]
  exact F'_pos x hx

lemma artanh_ge (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    1 / 2 * Real.log (1 / (1 - x)) ≤ Real.artanh x := by
  rw [artanh_eq x ⟨by linarith [hx.1], hx.2⟩]
  have h1 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith [hx.1])
  have : Real.log (1 / (1 - x)) = -Real.log (1 - x) := by rw [one_div, Real.log_inv]
  rw [this]
  linarith

lemma artanh_half_lt : Real.artanh (1 / 2) < 1 := by
  rw [artanh_eq _ ⟨by norm_num, by norm_num⟩]
  have : Real.log (1 + 1 / 2) - Real.log (1 - 1 / 2) = Real.log 3 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [this]
  have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 3) (by norm_num)
  linarith

lemma F_surj (y : ℝ) : ∃ x ∈ Ioo (0 : ℝ) 1, F x = y := by
  set M := |y| + 3 with hM
  have hM1 : 3 ≤ M := by have := abs_nonneg y; linarith
  -- small point a
  set a := 1 / (M + 2) with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 / 2 := by rw [ha, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hFa : F a ≤ y := by
    unfold F
    have h1 : Real.artanh a ≤ Real.artanh (1 / 2) :=
      Real.artanh_le_artanh (by linarith) (by norm_num) ha1
    have h2 : 1 / a = M + 2 := by rw [ha, one_div_one_div]
    rw [h2]
    have := artanh_half_lt
    have := le_abs_self y
    have := neg_abs_le y
    linarith
  -- point b close to 1
  set b := 1 - Real.exp (-(2 * M)) with hb
  have hE : Real.exp (-(2 * M)) ≤ Real.exp (-6) := Real.exp_le_exp.mpr (by linarith)
  have hE6 : Real.exp (-6) < 1 / 2 := by
    have := Real.exp_pos 6
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 6) (by norm_num)]
    have := Real.add_one_le_exp 6
    linarith
  have hb0 : 1 / 2 < b := by rw [hb]; linarith
  have hb1 : b < 1 := by rw [hb]; linarith [Real.exp_pos (-(2 * M))]
  have hab : a < b := by linarith
  have hFb : y ≤ F b := by
    unfold F
    have h1 := artanh_ge b ⟨by linarith, hb1⟩
    have h2 : 1 / (1 - b) = Real.exp (2 * M) := by
      rw [hb, sub_sub_cancel, one_div, ← Real.exp_neg, neg_neg]
    rw [h2, Real.log_exp] at h1
    have h3 : 1 / b ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    have := le_abs_self y
    linarith
  have hsub : Icc a b ⊆ Ioo 0 1 := fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩
  obtain ⟨x, hx, hFx⟩ := intermediate_value_Icc hab.le (F_cont.mono hsub) ⟨hFa, hFb⟩
  exact ⟨x, hsub hx, hFx⟩

noncomputable def Fsub : Ioo (0 : ℝ) 1 → ℝ := fun x => F x

lemma Fsub_mono : StrictMono Fsub := fun x y hxy => F_mono x.2 y.2 hxy

lemma Fsub_surj : Function.Surjective Fsub := fun y => by
  obtain ⟨x, hx, h⟩ := F_surj y
  exact ⟨⟨x, hx⟩, h⟩

noncomputable def e : Ioo (0 : ℝ) 1 ≃o ℝ := StrictMono.orderIsoOfSurjective Fsub Fsub_mono Fsub_surj

noncomputable def Hsol (t : ℝ) : ℝ := (e.symm (-2 * t) : ℝ)

lemma Hsol_mem (t : ℝ) : Hsol t ∈ Ioo (0 : ℝ) 1 := (e.symm (-2 * t)).2

lemma F_Hsol (t : ℝ) : F (Hsol t) = -2 * t := by
  have : e (e.symm (-2 * t)) = -2 * t := e.apply_symm_apply _
  exact this

lemma Hsol_cont : Continuous Hsol :=
  continuous_subtype_val.comp (e.symm.continuous.comp (continuous_const.mul continuous_id))

lemma Hsol_implicit (t : ℝ) : 2 * t = 1 / Hsol t - Real.artanh (Hsol t) := by
  have := F_Hsol t
  unfold F at this
  linarith

lemma Hsol_deriv (t : ℝ) : HasDerivAt Hsol (-2 * Hsol t ^ 2 + 2 * Hsol t ^ 4) t := by
  have hm := Hsol_mem t
  have hf : HasDerivAt (fun x => -(F x) / 2) (-(1 / (1 - Hsol t ^ 2) + 1 / Hsol t ^ 2) / 2) (Hsol t) :=
    (hasDerivAt_F _ hm).neg.div_const 2
  have hne : -(1 / (1 - Hsol t ^ 2) + 1 / Hsol t ^ 2) / 2 ≠ 0 := by
    have := F'_pos _ hm; intro h; linarith
  have := HasDerivAt.of_local_left_inverse Hsol_cont.continuousAt hf hne
    (Eventually.of_forall fun y => by simp only [F_Hsol]; ring)
  refine this.congr_deriv ?_
  have h1 : 0 < 1 - Hsol t ^ 2 := by nlinarith [hm.1, hm.2]
  have h2 : 0 < Hsol t := hm.1
  field_simp
  ring

/-- for `x ∈ (0,1)`: `x < Hsol t ↔ t < -F x / 2` -/
lemma lt_Hsol (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (t : ℝ) : x < Hsol t ↔ F x < -2 * t := by
  have := e.lt_symm_apply (x := ⟨x, hx⟩) (y := -2 * t)
  exact this

lemma Hsol_lt (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (t : ℝ) : Hsol t < x ↔ -2 * t < F x := by
  have := e.symm_apply_lt (x := ⟨x, hx⟩) (y := -2 * t)
  exact this

lemma Hsol_atBot : Tendsto Hsol atBot (𝓝 1) := by
  rw [tendsto_order]
  refine ⟨fun a' ha' => ?_, fun a' ha' => Eventually.of_forall fun t => by linarith [(Hsol_mem t).2]⟩
  set x := max a' (1 / 2)
  have hx : x ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, max_lt ha' (by norm_num)⟩
  filter_upwards [eventually_lt_atBot (-(F x) / 2)] with t ht
  have := (lt_Hsol x hx t).mpr (by linarith)
  exact lt_of_le_of_lt (le_max_left _ _) this

lemma Hsol_atTop : Tendsto Hsol atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a' ha' => Eventually.of_forall fun t => by linarith [(Hsol_mem t).1], fun a' ha' => ?_⟩
  set x := min a' (1 / 2)
  have hx : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_min ha' (by norm_num), by
    have := min_le_right a' (1 / 2 : ℝ); linarith⟩
  filter_upwards [eventually_gt_atTop (-(F x) / 2)] with t ht
  have := (Hsol_lt x hx t).mpr (by linarith)
  exact lt_of_lt_of_le this (min_le_left _ _)

lemma artanh_tendsto_zero : Tendsto Real.artanh (𝓝 0) (𝓝 0) := by
  have := (hasDerivAt_artanh 0 ⟨by norm_num, by norm_num⟩).continuousAt
  rw [ContinuousAt, Real.artanh_zero] at this
  exact this

lemma Hsol_mul_t : Tendsto (fun t => Hsol t * t) atTop (𝓝 (1 / 2)) := by
  have heq : ∀ t, Hsol t * t = (1 - Hsol t * Real.artanh (Hsol t)) / 2 := by
    intro t
    have := Hsol_implicit t
    have h0 := (Hsol_mem t).1.ne'
    field_simp at this ⊢
    linarith
  simp_rw [heq]
  have h1 : Tendsto (fun t => Real.artanh (Hsol t)) atTop (𝓝 0) :=
    artanh_tendsto_zero.comp Hsol_atTop
  have := ((tendsto_const_nhds (x := (1:ℝ))).sub (Hsol_atTop.mul h1)).div_const 2
  simpa using this

end CarneiroAux

open CarneiroAux in
theorem solution :
    ∃ H : ℝ → ℝ, (∀ t, 0 < H t ∧ H t < 1) ∧
      (∀ t, 2 * t = 1 / H t - Real.artanh (H t)) ∧
      (∀ t, HasDerivAt H (-2 * H t ^ 2 + 2 * H t ^ 4) t) ∧
      Tendsto H atBot (𝓝 1) ∧
      Tendsto (fun t => H t * t) atTop (𝓝 (1 / 2)) :=
  ⟨Hsol, fun t => Hsol_mem t, Hsol_implicit, Hsol_deriv, Hsol_atBot, Hsol_mul_t⟩
