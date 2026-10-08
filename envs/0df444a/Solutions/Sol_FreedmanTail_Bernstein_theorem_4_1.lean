-- Prove2me | solution 1 for FreedmanTail.Bernstein.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:58:37.645988+00:00
-- url     : https://prove2.me/submissions/6fe3db3f-4953-428f-aaa0-e03ee1d9d53f

import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_Exponents
import Definitions.Def_FreedmanTail_Bernstein_PartialSums

open MeasureTheory ProbabilityTheory


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


lemma fb_g_id (t : ℝ) : Real.exp t - 1 - t = t ^ 2 * fb_g t := by
  by_cases ht : t = 0
  · subst ht; simp [fb_g]
  · simp only [fb_g, if_neg ht]
    field_simp

theorem corollary_3_2_core (lam x : ℝ) (hlam : 0 ≤ lam) (hx : x ≤ 1) :
    Real.exp (lam * x) ≤ 1 + lam * x + x ^ 2 * e lam := by
  have h1 := fb_g_id (lam * x)
  have h2 := fb_g_id lam
  have hmono : fb_g (lam * x) ≤ fb_g lam :=
    fb_g_strictMono.monotone (by nlinarith)
  have hsq : 0 ≤ (lam * x) ^ 2 := sq_nonneg _
  unfold e
  have : (lam * x) ^ 2 * fb_g (lam * x) ≤ (lam * x) ^ 2 * fb_g lam :=
    mul_le_mul_of_nonneg_left hmono hsq
  nlinarith

theorem minimizing_lambda_core (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ Real.log ((a + b) / b) ∧
      (∀ lam : ℝ, 0 ≤ lam →
        Real.exp (-Real.log ((a + b) / b) * a + e (Real.log ((a + b) / b)) * b)
          ≤ Real.exp (-lam * a + e lam * b)) ∧
      Real.exp (-Real.log ((a + b) / b) * a + e (Real.log ((a + b) / b)) * b)
        = (b / (a + b)) ^ (a + b) * Real.exp a := by
  set L := Real.log ((a + b) / b) with hL
  have hpos : 0 < (a + b) / b := by positivity
  have hexpL : Real.exp L = (a + b) / b := Real.exp_log hpos
  have hL0 : 0 ≤ L := Real.log_nonneg ((one_le_div hb).mpr (by linarith))
  refine ⟨hL0, ?_, ?_⟩
  · intro lam _
    apply Real.exp_le_exp.mpr
    unfold e
    have h1 : Real.exp lam = Real.exp L * Real.exp (lam - L) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 := Real.add_one_le_exp (lam - L)
    have h3 : Real.exp L * (lam - L + 1) ≤ Real.exp L * Real.exp (lam - L) :=
      mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    rw [hexpL] at h3 h1
    have h4 : (a + b) / b * b = a + b := by field_simp
    nlinarith
  · unfold e
    rw [hexpL]
    have hlog : Real.log (b / (a + b)) = -L := by
      rw [hL, ← Real.log_inv, inv_div]
    rw [Real.rpow_def_of_pos (by positivity), hlog, ← Real.exp_add]
    congr 1
    field_simp
    ring

/-- the key comparison for the non-centered Bernstein bound -/
lemma fb_F_deriv (lam m : ℝ) :
    HasDerivAt (fun y : ℝ => (1 + y) ^ 2 * (Real.exp lam - 1 - lam) - Real.exp lam
        + Real.exp (-lam * y) * (1 + lam + lam * y))
      ((1 + m) * (2 * (Real.exp lam - 1 - lam) - lam ^ 2 * Real.exp (-lam * m))) m := by
  have h1 : HasDerivAt (fun y : ℝ => (1 + y) ^ 2) (2 * (1 + m)) m := by
    have := ((hasDerivAt_id m).const_add 1).mul ((hasDerivAt_id m).const_add 1)
    have h' : (fun y : ℝ => (1 + y) ^ 2) = fun y => (1 + y) * (1 + y) := by
      funext y; ring
    rw [h']
    exact this.congr_deriv (by simp; ring)
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-lam * y)) (Real.exp (-lam * m) * (-lam)) m := by
    have hl : HasDerivAt (fun y : ℝ => -lam * y) (-lam) m := by
      simpa using (hasDerivAt_id m).const_mul (-lam)
    exact (Real.hasDerivAt_exp _).comp m hl
  have h3 : HasDerivAt (fun y : ℝ => 1 + lam + lam * y) lam m := by
    simpa using ((hasDerivAt_id m).const_mul lam).const_add (1 + lam)
  have := ((h1.mul_const (Real.exp lam - 1 - lam)).sub_const (Real.exp lam)).add (h2.mul h3)
  exact this.congr_deriv (by ring)

lemma fb_F_nonneg (lam m : ℝ) (hlam : 0 ≤ lam) (hm : 0 ≤ m) :
    Real.exp (-lam * m) * (Real.exp (lam * (1 + m)) - 1 - lam * (1 + m))
      ≤ (1 + m) ^ 2 * (Real.exp lam - 1 - lam) := by
  set F : ℝ → ℝ := fun y => (1 + y) ^ 2 * (Real.exp lam - 1 - lam) - Real.exp lam
        + Real.exp (-lam * y) * (1 + lam + lam * y) with hF
  have hmono : MonotoneOn F (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun y _ => (fb_F_deriv lam y).continuousAt.continuousWithinAt
    · exact fun y _ => (fb_F_deriv lam y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(fb_F_deriv lam y).deriv]
      have hy0 : 0 < y := hy
      have hq := Real.quadratic_le_exp_of_nonneg hlam
      have he : Real.exp (-lam * y) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith
      have : lam ^ 2 * Real.exp (-lam * y) ≤ lam ^ 2 := by
        have := mul_le_mul_of_nonneg_left he (sq_nonneg lam); simpa using this
      apply mul_nonneg (by linarith)
      linarith
  have h0 : F 0 = 0 := by simp [hF]; ring
  have hm' := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hm) hm
  rw [h0] at hm'
  simp only [hF] at hm'
  have hprod : Real.exp (-lam * m) * Real.exp (lam * (1 + m)) = Real.exp lam := by
    rw [← Real.exp_add]; congr 1; ring
  nlinarith

/-- `log(1-t) ≤ -t - t²/2` for `0 ≤ t < 1`. -/
lemma fb_phi_deriv (t : ℝ) (ht : t < 1) :
    HasDerivAt (fun y : ℝ => -Real.log (1 - y) - y - y ^ 2 / 2)
      (t ^ 2 / (1 - t)) t := by
  have hne : (1 - t) ≠ 0 := by linarith
  have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) t := (hasDerivAt_id t).const_sub 1
  have h2 := (Real.hasDerivAt_log hne).comp t h1
  have h3 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) t t := by
    simpa using (hasDerivAt_pow 2 t).div_const 2
  have := (h2.neg.sub (hasDerivAt_id t)).sub h3
  apply this.congr_deriv
  field_simp
  ring

lemma fb_log_bound (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Real.log (1 - t) ≤ -t - t ^ 2 / 2 := by
  set φ : ℝ → ℝ := fun y => -Real.log (1 - y) - y - y ^ 2 / 2 with hφ
  have hmono : MonotoneOn φ (Set.Ico 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · exact fun y hy => (fb_phi_deriv y hy.2).continuousAt.continuousWithinAt
    · exact fun y hy => (fb_phi_deriv y (interior_subset hy).2).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ico] at hy
      rw [(fb_phi_deriv y hy.2).deriv]
      apply div_nonneg (sq_nonneg _); linarith [hy.2]
  have h0 : φ 0 = 0 := by simp [hφ]
  have := hmono (Set.mem_Ico.mpr ⟨le_rfl, one_pos⟩) (Set.mem_Ico.mpr ⟨ht0, ht1⟩) ht0
  rw [h0] at this
  simp only [hφ] at this
  linarith

lemma fb_second_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (b / (a + b)) ^ (a + b) * Real.exp a ≤ Real.exp (-(a ^ 2) / (2 * (a + b))) := by
  have hab : 0 < a + b := by linarith
  have ht0 : 0 ≤ a / (a + b) := by positivity
  have ht1 : a / (a + b) < 1 := (div_lt_one hab).mpr (by linarith)
  have hlog := fb_log_bound (a / (a + b)) ht0 ht1
  have h1 : 1 - a / (a + b) = b / (a + b) := by field_simp; ring
  rw [h1] at hlog
  rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h2 : Real.log (b / (a + b)) * (a + b) ≤ (-(a / (a + b)) - (a / (a + b)) ^ 2 / 2) * (a + b) :=
    mul_le_mul_of_nonneg_right hlog hab.le
  have h3 : (-(a / (a + b)) - (a / (a + b)) ^ 2 / 2) * (a + b) + a = -(a ^ 2) / (2 * (a + b)) := by
    field_simp
    ring
  linarith


lemma fb_e_nonneg (t : ℝ) : 0 ≤ e t := by
  unfold e; have := Real.add_one_le_exp t; linarith

/-- pointwise bound with a shift `m ≥ 0` -/
lemma fb_pw (lam x m μ : ℝ) (hlam : 0 ≤ lam) (hx : x ≤ 1) (hm : 0 ≤ m) (hμ : μ = -m) :
    Real.exp (lam * x) ≤ Real.exp (-lam * m) * (1 + lam * m)
      + (Real.exp (-lam * m) * lam) * x
      + Real.exp (-lam * m) * (e (lam * (1 + m)) / (1 + m) ^ 2) * (x - μ) ^ 2 := by
  have hM0 : 0 < 1 + m := by linarith
  have hcor := corollary_3_2_core (lam * (1 + m)) ((x + m) / (1 + m)) (by positivity)
    (by rw [div_le_one hM0]; linarith)
  have h1 : lam * (1 + m) * ((x + m) / (1 + m)) = lam * (x + m) := by field_simp
  rw [h1] at hcor
  have h2 : Real.exp (lam * x) = Real.exp (-lam * m) * Real.exp (lam * (x + m)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h2]
  have h3 : ((x + m) / (1 + m)) ^ 2 = (x - μ) ^ 2 / (1 + m) ^ 2 := by
    rw [div_pow, hμ]; ring
  rw [h3] at hcor
  have hE := Real.exp_pos (-lam * m)
  have := mul_le_mul_of_nonneg_left hcor hE.le
  have h4 : Real.exp (-lam * m) * (1 + lam * (x + m) + (x - μ) ^ 2 / (1 + m) ^ 2 * e (lam * (1 + m)))
      = Real.exp (-lam * m) * (1 + lam * m) + (Real.exp (-lam * m) * lam) * x
        + Real.exp (-lam * m) * (e (lam * (1 + m)) / (1 + m) ^ 2) * (x - μ) ^ 2 := by ring
  linarith

lemma fb_coefA_bound (lam m : ℝ) (hlam : 0 ≤ lam) (hm : 0 ≤ m) :
    0 ≤ Real.exp (-lam * m) * (1 + lam * m) ∧ Real.exp (-lam * m) * (1 + lam * m) ≤ 1 := by
  have hE := Real.exp_pos (-lam * m)
  constructor
  · exact mul_nonneg hE.le (by nlinarith)
  · have h := Real.add_one_le_exp (lam * m)
    have h2 : Real.exp (-lam * m) * Real.exp (lam * m) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith

lemma fb_coefC_bound (lam m : ℝ) (hlam : 0 ≤ lam) (hm : 0 ≤ m) :
    0 ≤ Real.exp (-lam * m) * (e (lam * (1 + m)) / (1 + m) ^ 2) ∧
      Real.exp (-lam * m) * (e (lam * (1 + m)) / (1 + m) ^ 2) ≤ e lam := by
  have hM0 : 0 < 1 + m := by linarith
  constructor
  · exact mul_nonneg (Real.exp_pos _).le (div_nonneg (fb_e_nonneg _) (by positivity))
  · rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have hF := fb_F_nonneg lam m hlam hm
    unfold e
    linarith

/-- Conditional version of (3.5): `E[exp(λX) | m] ≤ exp(e(λ) Var[X | m])`. -/
theorem fb_cond_ineq {Ω : Type*} {m m0 : MeasurableSpace Ω} (hm : m ≤ m0)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hX2 : MemLp X 2 P) (hX1 : X ≤ᵐ[P] 1) (hmean : P[X | m] ≤ᵐ[P] 0) :
    P[fun ω => Real.exp (lam * X ω) | m] ≤ᵐ[P]
      fun ω => Real.exp (e lam * condVar m X P ω) := by
  have hXae : AEStronglyMeasurable X P := hX2.aestronglyMeasurable
  have hXint : Integrable X P := hX2.integrable one_le_two
  set μ' : Ω → ℝ := P[X | m] with hμ'
  have hμ'sm : StronglyMeasurable[m] μ' := stronglyMeasurable_condExp
  have hμ'2 : MemLp μ' 2 P := hX2.condExp one_le_two
  set mh : Ω → ℝ := fun ω => max 0 (-μ' ω) with hmh
  have hmh0 : ∀ ω, 0 ≤ mh ω := fun ω => le_max_left _ _
  have hmh_ae : ∀ᵐ ω ∂P, μ' ω = -mh ω := by
    filter_upwards [hmean] with ω hω
    have : μ' ω ≤ 0 := hω
    simp only [hmh]
    rw [max_eq_right (by linarith)]; ring
  have hmh_meas : Measurable[m] mh := by
    simp only [hmh]
    exact measurable_const.max hμ'sm.measurable.neg
  set A : Ω → ℝ := fun ω => Real.exp (-lam * mh ω) * (1 + lam * mh ω) with hA
  set B : Ω → ℝ := fun ω => Real.exp (-lam * mh ω) * lam with hB
  set C : Ω → ℝ := fun ω => Real.exp (-lam * mh ω) * (e (lam * (1 + mh ω)) / (1 + mh ω) ^ 2)
    with hC
  have hexp_meas : Measurable[m] (fun ω => Real.exp (-lam * mh ω)) :=
    Real.measurable_exp.comp (hmh_meas.const_mul _)
  have hA_meas : StronglyMeasurable[m] A := by
    simp only [hA]
    exact (hexp_meas.mul ((hmh_meas.const_mul lam).const_add 1)).stronglyMeasurable
  have hB_meas : StronglyMeasurable[m] B := by
    simp only [hB]
    exact (hexp_meas.mul_const lam).stronglyMeasurable
  have hC_meas : StronglyMeasurable[m] C := by
    simp only [hC]
    refine (hexp_meas.mul ?_).stronglyMeasurable
    refine Measurable.div ?_ ((hmh_meas.const_add 1).pow_const 2)
    unfold e
    have h1 : Measurable[m] (fun ω => lam * (1 + mh ω)) := (hmh_meas.const_add 1).const_mul lam
    exact (Real.measurable_exp.comp h1 |>.sub_const 1).sub h1
  have hA_bd : ∀ ω, ‖A ω‖ ≤ 1 := fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (fb_coefA_bound lam _ hlam (hmh0 ω)).1]
    exact (fb_coefA_bound lam _ hlam (hmh0 ω)).2
  have hB_bd : ∀ ω, ‖B ω‖ ≤ lam := fun ω => by
    rw [Real.norm_eq_abs, hB]
    simp only
    rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hlam)]
    have : Real.exp (-lam * mh ω) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [hmh0 ω]
    nlinarith
  have hC_bd : ∀ ω, ‖C ω‖ ≤ e lam := fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (fb_coefC_bound lam _ hlam (hmh0 ω)).1]
    exact (fb_coefC_bound lam _ hlam (hmh0 ω)).2
  have hA_int : Integrable A P :=
    Integrable.of_bound (hA_meas.mono hm).aestronglyMeasurable 1 (Filter.Eventually.of_forall hA_bd)
  have hBX_int : Integrable (B * X) P :=
    hXint.bdd_mul (hB_meas.mono hm).aestronglyMeasurable (Filter.Eventually.of_forall hB_bd)
  have hsq_int : Integrable ((X - μ') ^ 2) P := (hX2.sub hμ'2).integrable_sq
  have hCsq_int : Integrable (C * (X - μ') ^ 2) P :=
    hsq_int.bdd_mul (hC_meas.mono hm).aestronglyMeasurable (Filter.Eventually.of_forall hC_bd)
  have hL_int : Integrable (fun ω => Real.exp (lam * X ω)) P := by
    refine Integrable.of_bound
      (Real.continuous_exp.comp_aestronglyMeasurable (hXae.const_mul lam)) (Real.exp lam) ?_
    filter_upwards [hX1] with ω hω
    have hω' : X ω ≤ 1 := hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hpw : (fun ω => Real.exp (lam * X ω)) ≤ᵐ[P] A + B * X + C * (X - μ') ^ 2 := by
    filter_upwards [hX1, hmh_ae] with ω hω hμω
    have hω' : X ω ≤ 1 := hω
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, hA, hB, hC]
    exact fb_pw lam (X ω) (mh ω) (μ' ω) hlam hω' (hmh0 ω) hμω
  have hR_int : Integrable (A + B * X + C * (X - μ') ^ 2) P := (hA_int.add hBX_int).add hCsq_int
  have h1 := condExp_mono (m := m) hL_int hR_int hpw
  have h2 := condExp_add (m := m) (hA_int.add hBX_int) hCsq_int
  have h3 := condExp_add (m := m) hA_int hBX_int
  have h4 : P[A | m] = A := condExp_of_stronglyMeasurable hm hA_meas hA_int
  have h5 := condExp_mul_of_stronglyMeasurable_left (μ := P) hB_meas hBX_int hXint
  have h6 := condExp_mul_of_stronglyMeasurable_left (μ := P) hC_meas hCsq_int hsq_int
  have hV_nonneg : 0 ≤ᵐ[P] condVar m X P :=
    condExp_nonneg (Filter.Eventually.of_forall fun ω => by simp [sq_nonneg])
  filter_upwards [h1, h2, h3, h5, h6, hmh_ae, hV_nonneg] with ω hω1 hω2 hω3 hω5 hω6 hμω hVω
  have hcv : condVar m X P ω = (P[(X - μ') ^ 2 | m]) ω := rfl
  rw [hcv]
  simp only [Pi.add_apply, Pi.mul_apply] at hω2 hω3 hω5 hω6
  rw [hω2, hω3, h4, hω5, hω6] at hω1
  have hAB : A ω + B ω * μ' ω = Real.exp (-lam * mh ω) := by
    simp only [hA, hB]; rw [hμω]; ring
  have hexp1 : Real.exp (-lam * mh ω) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [hmh0 ω]
  have hC' := (fb_coefC_bound lam _ hlam (hmh0 ω)).2
  have hCle : C ω * (P[(X - μ') ^ 2 | m]) ω ≤ e lam * (P[(X - μ') ^ 2 | m]) ω :=
    mul_le_mul_of_nonneg_right hC' hVω
  have hfin := Real.add_one_le_exp (e lam * (P[(X - μ') ^ 2 | m]) ω)
  linarith


lemma S_succ {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    S X (n + 1) ω = S X n ω + X (n + 1) ω := by
  unfold S; rw [Finset.sum_Icc_succ_top (by omega)]

lemma T_succ {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (P : Measure Ω) (n : ℕ) (ω : Ω) :
    T ℱ X P (n + 1) ω = T ℱ X P n ω + V ℱ X P (n + 1) ω := by
  unfold T; rw [Finset.sum_Icc_succ_top (by omega)]

theorem supermartingale_Q_core {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hmeas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hL2 : ∀ n, 1 ≤ n → MemLp (X n) 2 P)
    (hle : ∀ n, 1 ≤ n → X n ≤ᵐ[P] 1)
    (hdrift : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] ≤ᵐ[P] 0)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    Supermartingale (fun n ω => Q lam (T ℱ X P n ω) (S X n ω)) ℱ P := by
  have he0 : 0 ≤ e lam := fb_e_nonneg lam
  have hS_meas : ∀ n, Measurable[ℱ n] (S X n) := fun n => by
    unfold S
    refine Finset.measurable_sum _ (fun i hi => ?_)
    rw [Finset.mem_Icc] at hi
    exact (hmeas i hi.1).measurable.mono (ℱ.mono hi.2) le_rfl
  have hV_meas : ∀ i, StronglyMeasurable[ℱ (i - 1)] (V ℱ X P i) := fun i =>
    stronglyMeasurable_condVar
  have hT_meas : ∀ n, Measurable[ℱ n] (T ℱ X P n) := fun n => by
    unfold T
    refine Finset.measurable_sum _ (fun i hi => ?_)
    rw [Finset.mem_Icc] at hi
    exact (hV_meas i).measurable.mono (ℱ.mono (by omega)) le_rfl
  have hf_meas : ∀ n, Measurable[ℱ n] (fun ω => Q lam (T ℱ X P n ω) (S X n ω)) := fun n => by
    unfold Q
    exact Real.measurable_exp.comp
      (((hS_meas n).const_mul lam).sub ((hT_meas n).const_mul (e lam)))
  have hX_ae : ∀ᵐ ω ∂P, ∀ i, X (i + 1) ω ≤ 1 := by
    rw [ae_all_iff]; intro i; exact hle (i + 1) (by omega)
  have hV_ae : ∀ᵐ ω ∂P, ∀ i, 0 ≤ V ℱ X P i ω := by
    rw [ae_all_iff]; intro i
    exact condExp_nonneg (Filter.Eventually.of_forall fun ω => by simp [sq_nonneg])
  have hS_le : ∀ᵐ ω ∂P, ∀ n, S X n ω ≤ n := by
    filter_upwards [hX_ae] with ω hω n
    unfold S
    calc ∑ i ∈ Finset.Icc 1 n, X i ω ≤ ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) := by
          apply Finset.sum_le_sum; intro i hi
          rw [Finset.mem_Icc] at hi
          have := hω (i - 1); rwa [Nat.sub_add_cancel hi.1] at this
      _ = n := by simp
  have hT_nn : ∀ᵐ ω ∂P, ∀ n, 0 ≤ T ℱ X P n ω := by
    filter_upwards [hV_ae] with ω hω n
    exact Finset.sum_nonneg (fun i _ => hω i)
  have hf_bd : ∀ n, ∀ᵐ ω ∂P, ‖Q lam (T ℱ X P n ω) (S X n ω)‖ ≤ Real.exp (lam * n) := fun n => by
    filter_upwards [hS_le, hT_nn] with ω h1 h2
    unfold Q
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (h1 n) hlam, mul_nonneg he0 (h2 n)]
  have hf_int : ∀ n, Integrable (fun ω => Q lam (T ℱ X P n ω) (S X n ω)) P := fun n =>
    Integrable.of_bound ((hf_meas n).mono (ℱ.le n) le_rfl).aestronglyMeasurable _ (hf_bd n)
  refine supermartingale_nat (fun n => (hf_meas n).stronglyMeasurable) hf_int (fun n => ?_)
  set Y : Ω → ℝ := fun ω =>
    Real.exp (lam * S X n ω - e lam * T ℱ X P n ω - e lam * V ℱ X P (n + 1) ω) with hY
  set g : Ω → ℝ := fun ω => Real.exp (lam * X (n + 1) ω) with hg
  have hV1 : V ℱ X P (n + 1) = condVar (ℱ n) (X (n + 1)) P := rfl
  have hY_meas : StronglyMeasurable[ℱ n] Y := by
    refine Measurable.stronglyMeasurable ?_
    simp only [hY]
    refine Real.measurable_exp.comp ?_
    refine (((hS_meas n).const_mul lam).sub ((hT_meas n).const_mul (e lam))).sub ?_
    rw [hV1]
    exact (stronglyMeasurable_condVar).measurable.const_mul _
  have hY_bd : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ Real.exp (lam * n) := by
    filter_upwards [hS_le, hT_nn, hV_ae] with ω h1 h2 h3
    simp only [hY]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (h1 n) hlam, mul_nonneg he0 (h2 n),
      mul_nonneg he0 (h3 (n + 1))]
  have hY_ae : AEStronglyMeasurable Y P := (hY_meas.mono (ℱ.le n)).aestronglyMeasurable
  have hg_int : Integrable g P := by
    refine Integrable.of_bound ?_ (Real.exp lam) ?_
    · exact Real.continuous_exp.comp_aestronglyMeasurable
        ((hL2 (n + 1) (by omega)).aestronglyMeasurable.const_mul lam)
    · filter_upwards [hle (n + 1) (by omega)] with ω hω
      have hω' : X (n + 1) ω ≤ 1 := hω
      simp only [hg]
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by nlinarith)
  have hYg_int : Integrable (Y * g) P := hg_int.bdd_mul hY_ae hY_bd
  have hfun : (fun ω => Q lam (T ℱ X P (n + 1) ω) (S X (n + 1) ω)) = Y * g := by
    funext ω
    simp only [Pi.mul_apply, hY, hg, Q]
    rw [← Real.exp_add, S_succ, T_succ]
    congr 1; ring
  have hdr : P[X (n + 1) | ℱ n] ≤ᵐ[P] 0 := by
    have := hdrift (n + 1) (by omega)
    simpa using this
  have hci := fb_cond_ineq (ℱ.le n) P (X (n + 1)) lam hlam (hL2 (n + 1) (by omega))
    (hle (n + 1) (by omega)) hdr
  have hpull := condExp_mul_of_stronglyMeasurable_left (μ := P) hY_meas hYg_int hg_int
  rw [hfun]
  filter_upwards [hpull, hci, hV_ae] with ω h1 h2 h3
  rw [h1]
  simp only [Pi.mul_apply]
  have hYpos : 0 < Y ω := Real.exp_pos _
  calc Y ω * (P[g | ℱ n]) ω
      ≤ Y ω * Real.exp (e lam * condVar (ℱ n) (X (n + 1)) P ω) :=
        mul_le_mul_of_nonneg_left h2 hYpos.le
    _ = Q lam (T ℱ X P n ω) (S X n ω) := by
        simp only [hY, Q]; rw [← Real.exp_add, ← hV1]; congr 1; ring


lemma Q_zero {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (P : Measure Ω) (lam : ℝ) (ω : Ω) : Q lam (T ℱ X P 0 ω) (S X 0 ω) = 1 := by
  simp [Q, S, T]

lemma fb_stoppedValue_le_one {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (f : ℕ → Ω → ℝ)
    (hf : Supermartingale f ℱ P) (hf0 : ∀ ω, f 0 ω = 1)
    (σ : Ω → WithTop ℕ) (hσ : IsStoppingTime ℱ σ) (N : ℕ) :
    ∫ ω, stoppedValue f (fun ω => min (σ ω) N) ω ∂P ≤ 1 := by
  have hsub := hf.neg
  have hτ0 : IsStoppingTime ℱ (fun _ => ((0 : ℕ) : WithTop ℕ)) := isStoppingTime_const ℱ 0
  have hπ : IsStoppingTime ℱ (fun ω => min (σ ω) N) := hσ.min_const N
  have hle : (fun _ => ((0 : ℕ) : WithTop ℕ)) ≤ fun ω => min (σ ω) N := fun ω => by simp
  have hbdd : ∀ ω, min (σ ω) (N : WithTop ℕ) ≤ N := fun ω => min_le_right _ _
  have h := hsub.expected_stoppedValue_mono hτ0 hπ hle hbdd
  have h' : ∫ ω, stoppedValue f (fun ω => min (σ ω) N) ω ∂P
      ≤ ∫ ω, stoppedValue f (fun _ => ((0 : ℕ) : WithTop ℕ)) ω ∂P := by
    have e1 : ∫ x, (-stoppedValue f fun _ => ((0 : ℕ) : WithTop ℕ)) x ∂P
        = -∫ ω, stoppedValue f (fun _ => ((0 : ℕ) : WithTop ℕ)) ω ∂P := integral_neg _
    have e2 : ∫ x, (-stoppedValue f fun ω => min (σ ω) N) x ∂P
        = -∫ ω, stoppedValue f (fun ω => min (σ ω) N) ω ∂P := integral_neg _
    rw [stoppedValue_neg, stoppedValue_neg, e1, e2] at h
    linarith
  calc ∫ ω, stoppedValue f (fun ω => min (σ ω) N) ω ∂P
      ≤ ∫ ω, stoppedValue f (fun _ => ((0 : ℕ) : WithTop ℕ)) ω ∂P := h'
    _ = ∫ ω, f 0 ω ∂P := by rfl
    _ = 1 := by simp [hf0]

theorem proposition_3_3_core {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hmeas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hL2 : ∀ n, 1 ≤ n → MemLp (X n) 2 P)
    (hle : ∀ n, 1 ≤ n → X n ≤ᵐ[P] 1)
    (hdrift : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] ≤ᵐ[P] 0)
    (lam : ℝ) (hlam : 0 ≤ lam) (σ : Ω → WithTop ℕ) (hσ : IsStoppingTime ℱ σ) :
    ∫⁻ ω in {ω | σ ω ≠ ⊤},
        ENNReal.ofReal (stoppedValue (fun n ω => Q lam (T ℱ X P n ω) (S X n ω)) σ ω) ∂P ≤ 1 := by
  set f : ℕ → Ω → ℝ := fun n ω => Q lam (T ℱ X P n ω) (S X n ω) with hf
  have hsup : Supermartingale f ℱ P := supermartingale_Q_core P ℱ X hmeas hL2 hle hdrift lam hlam
  have hf0 : ∀ ω, f 0 ω = 1 := fun ω => Q_zero ℱ X P lam ω
  have hfpos : ∀ n ω, 0 ≤ f n ω := fun n ω => (Real.exp_pos _).le
  have hset : {ω | σ ω ≠ ⊤} = ⋃ N : ℕ, {ω | σ ω ≤ N} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      lift σ ω to ℕ using h with k hk
      exact ⟨k, le_rfl⟩
    · rintro ⟨N, hN⟩ h
      rw [h] at hN
      exact absurd hN (by simp)
  have hdir : Directed (· ⊆ ·) (fun N : ℕ => {ω | σ ω ≤ N}) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · intro ω hω
      have hω' : σ ω ≤ i := hω
      show σ ω ≤ ((max i j : ℕ) : WithTop ℕ)
      exact le_trans hω' (by exact_mod_cast le_max_left i j)
    · intro ω hω
      have hω' : σ ω ≤ j := hω
      show σ ω ≤ ((max i j : ℕ) : WithTop ℕ)
      exact le_trans hω' (by exact_mod_cast le_max_right i j)
  rw [hset, setLIntegral_iUnion_of_directed _ hdir]
  refine iSup_le fun N => ?_
  have hmeasN : MeasurableSet {ω | σ ω ≤ N} := ℱ.le N _ (hσ.measurableSet_le N)
  have hcongr : ∫⁻ ω in {ω | σ ω ≤ N}, ENNReal.ofReal (stoppedValue f σ ω) ∂P
      = ∫⁻ ω in {ω | σ ω ≤ N},
          ENNReal.ofReal (stoppedValue f (fun ω => min (σ ω) N) ω) ∂P := by
    refine setLIntegral_congr_fun hmeasN (fun ω hω => ?_)
    have hω' : σ ω ≤ N := hω
    simp only [stoppedValue, min_eq_left hω']
  rw [hcongr]
  have hint : Integrable (stoppedValue f (fun ω => min (σ ω) N)) P :=
    integrable_stoppedValue ℕ (hσ.min_const N) hsup.integrable (fun ω => min_le_right _ _)
  calc ∫⁻ ω in {ω | σ ω ≤ N}, ENNReal.ofReal (stoppedValue f (fun ω => min (σ ω) N) ω) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (stoppedValue f (fun ω => min (σ ω) N) ω) ∂P :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ENNReal.ofReal (∫ ω, stoppedValue f (fun ω => min (σ ω) N) ω ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun ω => hfpos _ _)).symm
    _ ≤ ENNReal.ofReal 1 :=
        ENNReal.ofReal_le_ofReal (fb_stoppedValue_le_one P ℱ f hsup hf0 σ hσ N)
    _ = 1 := ENNReal.ofReal_one

theorem tail_le_exp_core {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hmeas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hL2 : ∀ n, 1 ≤ n → MemLp (X n) 2 P)
    (hle : ∀ n, 1 ≤ n → X n ≤ᵐ[P] 1)
    (hdrift : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] ≤ᵐ[P] 0)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (lam : ℝ) (hlam : 0 ≤ lam) :
    P {ω | ∃ n, 1 ≤ n ∧ a ≤ S X n ω ∧ T ℱ X P n ω ≤ b}
      ≤ ENNReal.ofReal (Real.exp (-lam * a + e lam * b)) := by
  classical
  have hS_meas : ∀ n, Measurable[ℱ n] (S X n) := fun n => by
    unfold S
    refine Finset.measurable_sum _ (fun i hi => ?_)
    rw [Finset.mem_Icc] at hi
    exact (hmeas i hi.1).measurable.mono (ℱ.mono hi.2) le_rfl
  have hT_meas : ∀ n, Measurable[ℱ n] (T ℱ X P n) := fun n => by
    unfold T
    refine Finset.measurable_sum _ (fun i hi => ?_)
    rw [Finset.mem_Icc] at hi
    exact (stronglyMeasurable_condVar (m := ℱ (i - 1))).measurable.mono
      (ℱ.mono (by omega)) le_rfl
  set u : ℕ → Ω → ℝ × ℝ := fun n ω => (S X n ω, T ℱ X P n ω) with hu
  set s : Set (ℝ × ℝ) := {p | a ≤ p.1 ∧ p.2 ≤ b} with hs
  have hu_adapted : Adapted ℱ u := fun n => (hS_meas n).prodMk (hT_meas n)
  have hs_meas : MeasurableSet s :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_snd measurable_const)
  set σ : Ω → WithTop ℕ := hittingAfter u s 1 with hσdef
  have hσ : IsStoppingTime ℱ σ := hu_adapted.isStoppingTime_hittingAfter hs_meas
  have hA : {ω | ∃ n, 1 ≤ n ∧ a ≤ S X n ω ∧ T ℱ X P n ω ≤ b} = {ω | σ ω ≠ ⊤} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hσdef, ne_eq, hittingAfter_eq_top_iff, not_forall, not_not,
      hu, hs, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, h1, h2, h3⟩; exact ⟨n, h1, h2, h3⟩
    · rintro ⟨n, h1, h2, h3⟩; exact ⟨n, h1, h2, h3⟩
  rw [hA]
  set f : ℕ → Ω → ℝ := fun n ω => Q lam (T ℱ X P n ω) (S X n ω) with hf
  have hprop := proposition_3_3_core P ℱ X hmeas hL2 hle hdrift lam hlam σ hσ
  have hAmeas : MeasurableSet {ω | σ ω ≠ ⊤} := by
    exact hσ.measurableSet_eq_top.compl
  set c : ENNReal := ENNReal.ofReal (Real.exp (lam * a - e lam * b)) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hlow : ∀ ω ∈ {ω | σ ω ≠ ⊤}, c ≤ ENNReal.ofReal (stoppedValue f σ ω) := by
    intro ω hω
    have hω' : σ ω ≠ ⊤ := hω
    have hmem := hittingAfter_mem_set_of_ne_top (u := u) (s := s) (n := 1) (ω := ω) hω'
    simp only [hu, hs, Set.mem_ofPred_eq] at hmem
    rw [hc]
    apply ENNReal.ofReal_le_ofReal
    simp only [stoppedValue, hf, Q]
    apply Real.exp_le_exp.mpr
    have he0 : 0 ≤ e lam := fb_e_nonneg lam
    nlinarith [mul_le_mul_of_nonneg_left hmem.1 hlam, mul_le_mul_of_nonneg_left hmem.2 he0]
  have h1 : c * P {ω | σ ω ≠ ⊤} ≤ 1 := by
    calc c * P {ω | σ ω ≠ ⊤} = ∫⁻ ω in {ω | σ ω ≠ ⊤}, c ∂P := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ ω in {ω | σ ω ≠ ⊤}, ENNReal.ofReal (stoppedValue f σ ω) ∂P :=
          setLIntegral_mono' hAmeas hlow
      _ ≤ 1 := hprop
  have h2 : P {ω | σ ω ≠ ⊤} ≤ c⁻¹ := by
    calc P {ω | σ ω ≠ ⊤} = c⁻¹ * (c * P {ω | σ ω ≠ ⊤}) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
      _ ≤ c⁻¹ * 1 := by gcongr
      _ = c⁻¹ := mul_one _
  have h3 : c⁻¹ = ENNReal.ofReal (Real.exp (-lam * a + e lam * b)) := by
    rw [hc, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
    congr 2; ring
  rwa [h3] at h2

theorem theorem_4_1_core {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hmeas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hL2 : ∀ n, 1 ≤ n → MemLp (X n) 2 P)
    (hle : ∀ n, 1 ≤ n → X n ≤ᵐ[P] 1)
    (hdrift : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] ≤ᵐ[P] 0)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    P {ω | ∃ n, 1 ≤ n ∧ a ≤ S X n ω ∧ T ℱ X P n ω ≤ b}
        ≤ ENNReal.ofReal ((b / (a + b)) ^ (a + b) * Real.exp a) ∧
      (b / (a + b)) ^ (a + b) * Real.exp a ≤ Real.exp (-(a ^ 2) / (2 * (a + b))) := by
  obtain ⟨hL0, _, hval⟩ := minimizing_lambda_core a b ha hb
  refine ⟨?_, fb_second_bound a b ha hb⟩
  rw [← hval]
  exact tail_le_exp_core P ℱ X hmeas hL2 hle hdrift a b ha hb _ hL0

end FreedmanTail.Bernstein

open FreedmanTail.Bernstein


theorem solution {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hmeas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hL2 : ∀ n, 1 ≤ n → MemLp (X n) 2 P)
    (hle : ∀ n, 1 ≤ n → X n ≤ᵐ[P] 1)
    (hdrift : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] ≤ᵐ[P] 0)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    P {ω | ∃ n, 1 ≤ n ∧ a ≤ S X n ω ∧ T ℱ X P n ω ≤ b}
        ≤ ENNReal.ofReal ((b / (a + b)) ^ (a + b) * Real.exp a) ∧
      (b / (a + b)) ^ (a + b) * Real.exp a ≤ Real.exp (-(a ^ 2) / (2 * (a + b))) := by
  exact theorem_4_1_core P ℱ X hmeas hL2 hle hdrift a b ha hb
