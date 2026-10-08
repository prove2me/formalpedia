-- Prove2me | solution 1 for GKP1998.massive_radial_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T15:33:23.187038+00:00
-- url     : https://prove2.me/submissions/825dcbf3-f997-4424-964c-2cbeb4e27b0d

import Mathlib
import Definitions.Def_GKP1998_Defs

set_option autoImplicit false

open Filter Topology Asymptotics

namespace GKP1998Aux_db807afc
open Real MeasureTheory Set

noncomputable def F (ν : ℝ) (j : ℕ) (x t : ℝ) : ℝ :=
  Real.cosh t ^ j * Real.exp (-x * Real.cosh t) * Real.cosh (ν * t)

noncomputable def KK (ν : ℝ) (j : ℕ) (x : ℝ) : ℝ := ∫ t in Ioi (0:ℝ), F ν j x t

lemma cosh_le_exp_of_nonneg {t : ℝ} (ht : 0 ≤ t) : Real.cosh t ≤ Real.exp t := by
  rw [Real.cosh_eq]
  have : Real.exp (-t) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
  linarith

lemma cosh_le_exp_abs' (y : ℝ) : Real.cosh y ≤ Real.exp |y| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp y ≤ Real.exp |y| := Real.exp_le_exp.mpr (le_abs_self y)
  have h2 : Real.exp (-y) ≤ Real.exp |y| := Real.exp_le_exp.mpr (neg_le_abs y)
  linarith

lemma abs_sinh_le_cosh' (y : ℝ) : |Real.sinh y| ≤ Real.cosh y := by
  rw [Real.sinh_eq, Real.cosh_eq, abs_le]
  constructor <;> linarith [Real.exp_pos y, Real.exp_pos (-y)]

lemma sq_div_four_le_cosh {t : ℝ} (ht : 0 ≤ t) : t ^ 2 / 4 ≤ Real.cosh t := by
  have h1 := Real.quadratic_le_exp_of_nonneg ht
  have h2 : Real.exp t / 2 ≤ Real.cosh t := by
    rw [Real.cosh_eq]; have := Real.exp_pos (-t); linarith
  nlinarith

lemma F_nonneg (ν : ℝ) (j : ℕ) (x t : ℝ) : 0 ≤ F ν j x t := by
  unfold F
  have := Real.cosh_pos t
  have := Real.cosh_pos (ν * t)
  positivity

lemma F_cont (ν : ℝ) (j : ℕ) (x : ℝ) : Continuous (F ν j x) := by
  unfold F; fun_prop

lemma F_bound (ν : ℝ) (j : ℕ) {a x t : ℝ} (ha : 0 < a) (hx : a ≤ x) (ht : 0 ≤ t) :
    F ν j x t ≤ Real.exp (((j:ℝ) + |ν| + 1) ^ 2 / a) * Real.exp (-t) := by
  have hc := Real.cosh_pos t
  have h1 : Real.cosh t ^ j ≤ Real.exp ((j:ℝ) * t) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hc.le (cosh_le_exp_of_nonneg ht) j
  have h2 : Real.cosh (ν * t) ≤ Real.exp (|ν| * t) := by
    have := cosh_le_exp_abs' (ν * t)
    rwa [abs_mul, abs_of_nonneg ht] at this
  have h3 : Real.exp (-x * Real.cosh t) ≤ Real.exp (-a * Real.cosh t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hq := sq_div_four_le_cosh ht
  have key : ((j:ℝ) + |ν| + 1) * t - a * t ^ 2 / 4 ≤ ((j:ℝ) + |ν| + 1) ^ 2 / a := by
    rw [le_div_iff₀ ha]
    nlinarith [sq_nonneg (((j:ℝ) + |ν| + 1) - a * t / 2)]
  have h4 : (j:ℝ) * t + (-a * Real.cosh t) + |ν| * t ≤ ((j:ℝ) + |ν| + 1) ^ 2 / a + -t := by
    have : a * (t ^ 2 / 4) ≤ a * Real.cosh t := mul_le_mul_of_nonneg_left hq ha.le
    nlinarith
  calc F ν j x t
      ≤ Real.exp ((j:ℝ) * t) * Real.exp (-a * Real.cosh t) * Real.exp (|ν| * t) := by
        unfold F
        exact mul_le_mul (mul_le_mul h1 h3 (Real.exp_pos _).le (Real.exp_pos _).le) h2
          (Real.cosh_pos _).le (by positivity)
    _ = Real.exp ((j:ℝ) * t + (-a * Real.cosh t) + |ν| * t) := by
        rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (((j:ℝ) + |ν| + 1) ^ 2 / a + -t) := Real.exp_le_exp.mpr h4
    _ = _ := by rw [Real.exp_add]

lemma bound_int (c : ℝ) : IntegrableOn (fun t : ℝ => Real.exp c * Real.exp (-t)) (Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ => Real.exp (-1 * t)) (Ioi 0) := exp_neg_integrableOn_Ioi 0 one_pos
  simp only [neg_mul, one_mul] at h
  exact h.const_mul _

lemma F_integrable (ν : ℝ) (j : ℕ) {x : ℝ} (hx : 0 < x) : IntegrableOn (F ν j x) (Ioi 0) := by
  refine Integrable.mono' (bound_int (((j:ℝ) + |ν| + 1) ^ 2 / x)) (F_cont ν j x).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_of_nonneg (F_nonneg ν j x t)]
  exact F_bound ν j hx le_rfl (le_of_lt ht)

lemma KK_hasDerivAt (ν : ℝ) (j : ℕ) {x0 : ℝ} (hx0 : 0 < x0) :
    HasDerivAt (KK ν j) (-KK ν (j + 1) x0) x0 := by
  have hε : 0 < x0 / 2 := by linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ))) (x₀ := x0) (s := Ioi (x0 / 2))
    (F := fun x t => F ν j x t) (F' := fun x t => -F ν (j + 1) x t)
    (bound := fun t => Real.exp ((((j + 1 : ℕ) : ℝ) + |ν| + 1) ^ 2 / (x0 / 2)) * Real.exp (-t))
    (Ioi_mem_nhds (by linarith))
    (Eventually.of_forall fun x => (F_cont ν j x).aestronglyMeasurable)
    (F_integrable ν j hx0) ((F_cont ν (j + 1) x0).neg.aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht x hx
      rw [norm_neg, Real.norm_of_nonneg (F_nonneg _ _ _ _)]
      exact F_bound ν (j + 1) hε (le_of_lt hx) (le_of_lt ht))
    (bound_int _)
    (by
      filter_upwards with t x _
      have hlin : HasDerivAt (fun y : ℝ => -y * Real.cosh t) (-1 * Real.cosh t) x :=
        (hasDerivAt_id' x).neg.mul_const (Real.cosh t)
      have := ((hlin.exp).const_mul (Real.cosh t ^ j)).mul_const (Real.cosh (ν * t))
      refine this.congr_deriv ?_
      simp only [F]
      ring)
  have e : KK ν j = fun x => ∫ t in Ioi (0:ℝ), F ν j x t := rfl
  rw [e]
  have h2 := key.2
  rw [integral_neg] at h2
  exact h2

lemma bessel_ode (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    x ^ 2 * KK ν 2 x - x * KK ν 1 x - (x ^ 2 + ν ^ 2) * KK ν 0 x = 0 := by
  set G : ℝ → ℝ := fun t =>
    Real.exp (-x * Real.cosh t) * (-x * Real.sinh t * Real.cosh (ν * t) - ν * Real.sinh (ν * t))
    with hGdef
  set G' : ℝ → ℝ := fun t =>
    x ^ 2 * F ν 2 x t - x * F ν 1 x t - (x ^ 2 + ν ^ 2) * F ν 0 x t with hG'def
  have hG : ∀ t, HasDerivAt G (G' t) t := by
    intro t
    have e1 : HasDerivAt (fun y => Real.exp (-x * Real.cosh y))
        (Real.exp (-x * Real.cosh t) * (-x * Real.sinh t)) t :=
      ((Real.hasDerivAt_cosh t).const_mul (-x)).exp
    have hl : HasDerivAt (fun y : ℝ => ν * y) (ν * 1) t := (hasDerivAt_id' t).const_mul ν
    have e2 := (((Real.hasDerivAt_sinh t).const_mul (-x)).mul hl.cosh).sub (hl.sinh.const_mul ν)
    refine (e1.mul e2).congr_deriv ?_
    simp only [hG'def, F, Pi.mul_apply, Pi.sub_apply]
    linear_combination (-(x ^ 2) * Real.exp (-x * Real.cosh t) * Real.cosh (ν * t)) *
      Real.cosh_sq t
  have i0 := F_integrable ν 0 hx
  have i1 := F_integrable ν 1 hx
  have i2 := F_integrable ν 2 hx
  have hG'int : IntegrableOn G' (Ioi 0) :=
    ((i2.const_mul (x ^ 2)).sub (i1.const_mul x)).sub (i0.const_mul (x ^ 2 + ν ^ 2))
  have hlim : Tendsto G atTop (𝓝 0) := by
    have hb : Tendsto (fun t : ℝ => (x + |ν|) * Real.exp ((((1:ℕ):ℝ) + |ν| + 1) ^ 2 / x)
        * Real.exp (-t)) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul
        ((x + |ν|) * Real.exp ((((1:ℕ):ℝ) + |ν| + 1) ^ 2 / x))
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    have s1 := abs_sinh_le_cosh' t
    have s2 := abs_sinh_le_cosh' (ν * t)
    have c1 := Real.one_le_cosh t
    have c2 := Real.cosh_pos (ν * t)
    have hFb := F_bound ν 1 hx le_rfl ht
    have hA : |(-x * Real.sinh t * Real.cosh (ν * t) - ν * Real.sinh (ν * t))|
        ≤ (x + |ν|) * (Real.cosh t * Real.cosh (ν * t)) := by
      have a1 : |(-x * Real.sinh t * Real.cosh (ν * t))| ≤ x * Real.cosh t * Real.cosh (ν * t) := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos hx, abs_of_pos c2]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left s1 hx.le) c2.le
      have a2 : |ν * Real.sinh (ν * t)| ≤ |ν| * (Real.cosh t * Real.cosh (ν * t)) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (s2.trans (le_mul_of_one_le_left c2.le c1)) (abs_nonneg ν)
      rw [abs_le] at a1 a2 ⊢
      constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2]
    rw [Real.norm_eq_abs, hGdef, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hF1 : F ν 1 x t = Real.cosh t * Real.exp (-x * Real.cosh t) * Real.cosh (ν * t) := by
      simp [F]
    calc Real.exp (-x * Real.cosh t) *
          |(-x * Real.sinh t * Real.cosh (ν * t) - ν * Real.sinh (ν * t))|
        ≤ Real.exp (-x * Real.cosh t) * ((x + |ν|) * (Real.cosh t * Real.cosh (ν * t))) :=
          mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le
      _ = (x + |ν|) * F ν 1 x t := by rw [hF1]; ring
      _ ≤ (x + |ν|) * (Real.exp ((((1:ℕ):ℝ) + |ν| + 1) ^ 2 / x) * Real.exp (-t)) :=
          mul_le_mul_of_nonneg_left hFb (by positivity)
      _ = _ := by ring
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto (f := G) (f' := G') (a := 0) (m := 0)
    (hG 0).continuousAt.continuousWithinAt (fun t _ => hG t) hG'int hlim
  have hG0 : G 0 = 0 := by simp [hGdef]
  rw [hG0, sub_zero] at hftc
  have hsplit : ∫ t in Ioi (0:ℝ), G' t
      = x ^ 2 * KK ν 2 x - x * KK ν 1 x - (x ^ 2 + ν ^ 2) * KK ν 0 x := by
    have h2' : Integrable (fun t => x ^ 2 * F ν 2 x t) (volume.restrict (Ioi 0)) :=
      i2.const_mul _
    have h1' : Integrable (fun t => x * F ν 1 x t) (volume.restrict (Ioi 0)) :=
      i1.const_mul _
    have h0' : Integrable (fun t => (x ^ 2 + ν ^ 2) * F ν 0 x t) (volume.restrict (Ioi 0)) :=
      i0.const_mul _
    have h12 : Integrable (fun t => x ^ 2 * F ν 2 x t - x * F ν 1 x t)
        (volume.restrict (Ioi 0)) := h2'.sub h1'
    simp only [hG'def]
    rw [integral_sub h12 h0', integral_sub h2' h1', integral_const_mul, integral_const_mul,
      integral_const_mul]
    rfl
  rw [← hsplit, hftc]

end GKP1998Aux_db807afc

open GKP1998Aux_db807afc in
open GKP1998 in
theorem solution (m R k z : ℝ) (hm : 0 < m) (hR : 0 < R) (hk : 0 < k)
    (hz : 0 < z) :
    throatOperator k ((m * R) ^ 2) (fun w => w ^ 2 * besselK (massiveOrder m R) (k * w)) z
      = 0 := by
  set ν := massiveOrder m R with hνdef
  have hν2 : ν ^ 2 = 4 + (m * R) ^ 2 := Real.sq_sqrt (by positivity)
  have hB : besselK ν = KK ν 0 := by
    funext x
    simp [besselK, KK, F]
  have kz : 0 < k * z := by positivity
  have hf : ∀ w, 0 < w → HasDerivAt (fun w => w ^ 2 * besselK ν (k * w))
      (2 * w * KK ν 0 (k * w) + w ^ 2 * (-KK ν 1 (k * w) * k)) w := by
    intro w hw
    rw [hB]
    have hkw : 0 < k * w := by positivity
    have hc := (KK_hasDerivAt ν 0 hkw).comp w ((hasDerivAt_id' w).const_mul k)
    have hp : HasDerivAt (fun w : ℝ => w ^ 2) (2 * w) w := by
      simpa using hasDerivAt_pow 2 w
    refine (hp.mul hc).congr_deriv ?_
    simp only [Function.comp_apply]
    ring
  have heq : (fun w => deriv (fun w => w ^ 2 * besselK ν (k * w)) w / w ^ 3) =ᶠ[𝓝 z]
      (fun w => (2 * w * KK ν 0 (k * w) + w ^ 2 * (-KK ν 1 (k * w) * k)) / w ^ 3) := by
    filter_upwards [Ioi_mem_nhds hz] with w hw
    rw [(hf w hw).deriv]
  unfold throatOperator
  rw [heq.deriv_eq]
  have hl : HasDerivAt (fun w : ℝ => k * w) (k * 1) z := (hasDerivAt_id' z).const_mul k
  have hd0 := (KK_hasDerivAt ν 0 kz).comp z hl
  have hd1 := (KK_hasDerivAt ν 1 kz).comp z hl
  have hp2 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have hp3 : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by
    simpa using hasDerivAt_pow 3 z
  have hN := (((hasDerivAt_id' z).const_mul 2).mul hd0).add (hp2.mul (hd1.neg.mul_const k))
  have hH := hN.div hp3 (by positivity)
  have hH' : HasDerivAt
      (fun w => (2 * w * KK ν 0 (k * w) + w ^ 2 * (-KK ν 1 (k * w) * k)) / w ^ 3)
      (((2 * KK ν 0 (k * z) - 4 * k * z * KK ν 1 (k * z) + k ^ 2 * z ^ 2 * KK ν 2 (k * z)) * z ^ 3
        - (2 * z * KK ν 0 (k * z) + z ^ 2 * (-KK ν 1 (k * z) * k)) * (3 * z ^ 2)) / (z ^ 3) ^ 2) z := by
    refine hH.congr_deriv ?_
    simp only [Function.comp_apply, Pi.mul_apply, Pi.add_apply, Pi.neg_apply]
    ring
  rw [hH'.deriv, hB]
  have ode := bessel_ode ν kz
  have hzne : z ≠ 0 := hz.ne'
  have hfin : z ^ 3 * (((2 * KK ν 0 (k * z) - 4 * k * z * KK ν 1 (k * z)
        + k ^ 2 * z ^ 2 * KK ν 2 (k * z)) * z ^ 3
        - (2 * z * KK ν 0 (k * z) + z ^ 2 * (-KK ν 1 (k * z) * k)) * (3 * z ^ 2)) / (z ^ 3) ^ 2)
      - k ^ 2 * (z ^ 2 * KK ν 0 (k * z)) - (m * R) ^ 2 / z ^ 2 * (z ^ 2 * KK ν 0 (k * z))
      = (k * z) ^ 2 * KK ν 2 (k * z) - k * z * KK ν 1 (k * z)
        - ((k * z) ^ 2 + ν ^ 2) * KK ν 0 (k * z) := by
    rw [hν2]
    field_simp
    ring
  rw [hfin, ode]
