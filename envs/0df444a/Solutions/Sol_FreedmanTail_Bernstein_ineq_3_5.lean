-- Prove2me | solution 1 for FreedmanTail.Bernstein.ineq_3_5
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:47:05.063319+00:00
-- url     : https://prove2.me/submissions/23abfce6-16a3-4bb1-a030-02cfb5d4c447

import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_Exponents

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


theorem ineq_3_5_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hX2 : MemLp X 2 P) (hX1 : X ≤ᵐ[P] 1) (hmean : ∫ ω, X ω ∂P ≤ 0) :
    ∫ ω, Real.exp (lam * X ω) ∂P ≤ 1 + e lam * variance X P ∧
      1 + e lam * variance X P ≤ Real.exp (e lam * variance X P) := by
  have hXae : AEStronglyMeasurable X P := hX2.aestronglyMeasurable
  have hXint : Integrable X P := hX2.integrable one_le_two
  set μ := ∫ ω, X ω ∂P with hμ
  set m := -μ with hm
  have hm0 : 0 ≤ m := by linarith
  set M := 1 + m with hM
  have hM0 : 0 < M := by linarith
  have hvar : variance X P = ∫ ω, (X ω - μ) ^ 2 ∂P := variance_eq_integral hXae.aemeasurable
  have hsqint : Integrable (fun ω => (X ω - μ) ^ 2) P := by
    have := (hX2.sub (memLp_const μ)).integrable_sq
    simpa using this
  set c := Real.exp (-lam * m) * (e (lam * M) / M ^ 2) with hc
  have hpw : ∀ᵐ ω ∂P, Real.exp (lam * X ω) ≤ Real.exp (-lam * m) * (1 + lam * m)
      + (Real.exp (-lam * m) * lam) * X ω + c * (X ω - μ) ^ 2 := by
    filter_upwards [hX1] with ω hω
    have hω' : X ω ≤ 1 := hω
    have hcor := corollary_3_2_core (lam * M) ((X ω + m) / M) (by positivity)
      (by rw [div_le_one hM0]; linarith)
    have h1 : lam * M * ((X ω + m) / M) = lam * (X ω + m) := by field_simp
    rw [h1] at hcor
    have h2 : Real.exp (lam * X ω) = Real.exp (-lam * m) * Real.exp (lam * (X ω + m)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h2]
    have h3 : ((X ω + m) / M) ^ 2 = (X ω - μ) ^ 2 / M ^ 2 := by
      rw [div_pow]; congr 1
    rw [h3] at hcor
    have hE := Real.exp_pos (-lam * m)
    have := mul_le_mul_of_nonneg_left hcor hE.le
    have h4 : Real.exp (-lam * m) * (1 + lam * (X ω + m) + (X ω - μ) ^ 2 / M ^ 2 * e (lam * M))
        = Real.exp (-lam * m) * (1 + lam * m) + (Real.exp (-lam * m) * lam) * X ω
          + Real.exp (-lam * m) * (e (lam * M) / M ^ 2) * (X ω - μ) ^ 2 := by ring
    rw [hc]
    linarith
  have hLint : Integrable (fun ω => Real.exp (lam * X ω)) P := by
    refine Integrable.of_bound
      (Real.continuous_exp.comp_aestronglyMeasurable (hXae.const_mul lam)) (Real.exp lam) ?_
    filter_upwards [hX1] with ω hω
    have hω' : X ω ≤ 1 := hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hi1 : Integrable (fun ω => Real.exp (-lam * m) * (1 + lam * m)
      + (Real.exp (-lam * m) * lam) * X ω) P :=
    (integrable_const _).add (hXint.const_mul _)
  have hRint : Integrable (fun ω => Real.exp (-lam * m) * (1 + lam * m)
      + (Real.exp (-lam * m) * lam) * X ω + c * (X ω - μ) ^ 2) P :=
    hi1.add (hsqint.const_mul c)
  have hint_le := integral_mono_ae hLint hRint hpw
  rw [integral_add hi1 (hsqint.const_mul c), integral_add (integrable_const _) (hXint.const_mul _),
    integral_const, integral_const_mul, integral_const_mul, ← hvar] at hint_le
  simp only [probReal_univ, one_smul] at hint_le
  have hF := fb_F_nonneg lam m hlam hm0
  have hc_le : c ≤ e lam := by
    rw [hc, mul_div_assoc', div_le_iff₀ (by positivity), hM]
    unfold e
    linarith
  have hvar0 := variance_nonneg X P
  have hexp1 : Real.exp (-lam * m) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  constructor
  · calc ∫ ω, Real.exp (lam * X ω) ∂P
        ≤ Real.exp (-lam * m) * (1 + lam * m) + Real.exp (-lam * m) * lam * μ
          + c * variance X P := hint_le
      _ = Real.exp (-lam * m) + c * variance X P := by rw [hm]; ring
      _ ≤ 1 + e lam * variance X P := by
          nlinarith [mul_le_mul_of_nonneg_right hc_le hvar0]
  · have := Real.add_one_le_exp (e lam * variance X P); linarith

end FreedmanTail.Bernstein

open FreedmanTail.Bernstein


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hX2 : MemLp X 2 P) (hX1 : X ≤ᵐ[P] 1) (hmean : ∫ ω, X ω ∂P ≤ 0) :
    ∫ ω, Real.exp (lam * X ω) ∂P ≤ 1 + e lam * variance X P ∧
      1 + e lam * variance X P ≤ Real.exp (e lam * variance X P) := by
  exact ineq_3_5_core P X lam hlam hX2 hX1 hmean
