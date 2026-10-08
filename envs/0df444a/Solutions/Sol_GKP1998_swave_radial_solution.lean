-- Prove2me | solution 1 for GKP1998.swave_radial_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T20:53:39.275129+00:00
-- url     : https://prove2.me/submissions/79d864b4-6a16-4392-8d45-530da7809cda

import Mathlib
import Definitions.Def_GKP1998_Defs

set_option autoImplicit false

open Filter Topology Asymptotics MeasureTheory Set

namespace GKP1998Aux

/-- The integrand family `cosh t ^ n * exp (-x cosh t) * cosh (ν t)`. -/
noncomputable def G (ν : ℝ) (n : ℕ) (x t : ℝ) : ℝ :=
  Real.cosh t ^ n * Real.exp (-x * Real.cosh t) * Real.cosh (ν * t)

/-- `F ν n x = ∫₀^∞ cosh t ^ n * exp (-x cosh t) * cosh (ν t) dt`. -/
noncomputable def F (ν : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), G ν n x t

lemma cosh_le_exp_of_nonneg {t : ℝ} (ht : 0 ≤ t) : Real.cosh t ≤ Real.exp t := by
  rw [Real.cosh_eq]
  have := Real.exp_le_exp.2 (show -t ≤ t by linarith)
  linarith

lemma cosh_mul_le (ν t : ℝ) (ht : 0 ≤ t) : Real.cosh (ν * t) ≤ Real.exp (|ν| * t) := by
  rw [← Real.cosh_abs, abs_mul, abs_of_nonneg ht]
  exact cosh_le_exp_of_nonneg (by positivity)

lemma sq_le_cosh {t : ℝ} (ht : 0 ≤ t) : t ^ 2 / 4 ≤ Real.cosh t := by
  rw [Real.cosh_eq]
  have h1 := Real.quadratic_le_exp_of_nonneg ht
  have h2 := Real.exp_pos (-t)
  nlinarith

lemma G_nonneg (ν : ℝ) (n : ℕ) (x t : ℝ) : 0 ≤ G ν n x t := by
  unfold G
  have := Real.cosh_pos t
  have := Real.cosh_pos (ν * t)
  positivity

lemma G_bound (ν : ℝ) (n : ℕ) {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) {t : ℝ} (ht : 0 ≤ t) :
    G ν n x t ≤ Real.exp (((n : ℝ) + |ν| + 1) ^ 2 / a) * Real.exp (-t) := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (n : ℝ) + |ν| + 1 := ⟨_, rfl⟩
  rw [← hM]
  unfold G
  have hc := Real.cosh_pos t
  have h1 : Real.cosh t ^ n ≤ Real.exp ((n : ℝ) * t) := by
    calc Real.cosh t ^ n ≤ Real.exp t ^ n :=
          pow_le_pow_left₀ hc.le (cosh_le_exp_of_nonneg ht) n
      _ = Real.exp ((n : ℝ) * t) := by rw [← Real.exp_nat_mul]
  have h2 : Real.exp (-x * Real.cosh t) ≤ Real.exp (-a * Real.cosh t) := by
    apply Real.exp_le_exp.2
    nlinarith
  have h3 := cosh_mul_le ν t ht
  have hq := sq_le_cosh ht
  have key0 : M * t - a * Real.cosh t ≤ M ^ 2 / a := by
    rw [le_div_iff₀ ha]
    nlinarith [sq_nonneg (M - a * t / 2), mul_le_mul_of_nonneg_left hq (mul_nonneg ha.le ha.le)]
  have hMt : M * t = (n : ℝ) * t + |ν| * t + t := by rw [hM]; ring
  have key : (n : ℝ) * t + -a * Real.cosh t + |ν| * t ≤ M ^ 2 / a + -t := by
    have : -a * Real.cosh t = -(a * Real.cosh t) := by ring
    rw [this]
    linarith
  calc Real.cosh t ^ n * Real.exp (-x * Real.cosh t) * Real.cosh (ν * t)
      ≤ Real.exp ((n : ℝ) * t) * Real.exp (-a * Real.cosh t) * Real.exp (|ν| * t) :=
        mul_le_mul (mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le) h3
          (Real.cosh_pos _).le (by positivity)
    _ = Real.exp ((n : ℝ) * t + -a * Real.cosh t + |ν| * t) := by
        rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (M ^ 2 / a + -t) := Real.exp_le_exp.2 key
    _ = Real.exp (M ^ 2 / a) * Real.exp (-t) := by rw [Real.exp_add]

lemma G_continuous (ν : ℝ) (n : ℕ) (x : ℝ) : Continuous (G ν n x) := by
  unfold G; fun_prop

lemma expneg_int (C : ℝ) : IntegrableOn (fun t : ℝ => C * Real.exp (-t)) (Ioi 0) := by
  have := (exp_neg_integrableOn_Ioi 0 one_pos).const_mul C
  simp only [neg_mul, one_mul] at this
  exact this

lemma G_integrable (ν : ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (G ν n x) (Ioi 0) := by
  refine Integrable.mono' (expneg_int (Real.exp (((n : ℝ) + |ν| + 1) ^ 2 / x)))
    (G_continuous ν n x).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (G_nonneg ν n x t)]
  exact G_bound ν n hx le_rfl (le_of_lt ht)

lemma F_hasDerivAt (ν : ℝ) (n : ℕ) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    HasDerivAt (F ν n) (-F ν (n + 1) x₀) x₀ := by
  have hs : Ioi (x₀ / 2) ∈ 𝓝 x₀ := Ioi_mem_nhds (by linarith)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun x t => G ν n x t) (F' := fun x t => -G ν (n + 1) x t)
    (bound := fun t => Real.exp ((((n + 1 : ℕ) : ℝ) + |ν| + 1) ^ 2 / (x₀ / 2)) * Real.exp (-t))
    hs (Eventually.of_forall (fun x => (G_continuous ν n x).aestronglyMeasurable))
    (G_integrable ν n hx₀) ((G_continuous ν (n + 1) x₀).neg.aestronglyMeasurable) ?_
    (expneg_int _) ?_
  · have h := key.2
    unfold F
    rw [integral_neg] at h
    exact h
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht x hx => ?_)
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (G_nonneg _ _ _ _)]
    exact G_bound ν (n + 1) (by linarith) (le_of_lt hx) (le_of_lt ht)
  · refine Eventually.of_forall (fun t x _ => ?_)
    show HasDerivAt (fun y => G ν n y t) (-G ν (n + 1) x t) x
    have h1 : HasDerivAt (fun y : ℝ => -y * Real.cosh t) (-Real.cosh t) x :=
      ((hasDerivAt_id' x).neg.mul_const (Real.cosh t)).congr_deriv (by ring)
    have h2 := (h1.exp.const_mul (Real.cosh t ^ n)).mul_const (Real.cosh (ν * t))
    refine h2.congr_deriv ?_
    simp only [G, pow_succ]
    ring

lemma F_zero (ν x : ℝ) : GKP1998.besselK ν x = F ν 0 x := by
  simp [GKP1998.besselK, F, G]

/-- The modified Bessel equation in the form `x² F₂ - x F₁ - (x² + ν²) F₀ = 0`. -/
lemma bessel_ode (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    x ^ 2 * F ν 2 x - x * F ν 1 x - (x ^ 2 + ν ^ 2) * F ν 0 x = 0 := by
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun t => -(Real.exp (-x * Real.cosh t) *
      (x * Real.sinh t * Real.cosh (ν * t) + ν * Real.sinh (ν * t))))
      (x ^ 2 * G ν 2 x t - x * G ν 1 x t - (x ^ 2 + ν ^ 2) * G ν 0 x t) t := by
    intro t _
    have e1 := ((Real.hasDerivAt_cosh t).const_mul (-x)).exp
    have e2 : HasDerivAt (fun y : ℝ => ν * y) ν t :=
      ((hasDerivAt_id' t).const_mul ν).congr_deriv (mul_one ν)
    have e5 := ((Real.hasDerivAt_sinh t).const_mul x).mul e2.cosh
    have e6 := e2.sinh.const_mul ν
    have e7 := (e1.mul (e5.add e6)).neg
    refine e7.congr_deriv ?_
    simp only [G, pow_zero, pow_one, one_mul, Pi.mul_apply, Pi.add_apply]
    linear_combination (-(x ^ 2 * Real.exp (-x * Real.cosh t) * Real.cosh (ν * t))) * Real.cosh_sq t
  have hint : IntegrableOn
      (fun t => x ^ 2 * G ν 2 x t - x * G ν 1 x t - (x ^ 2 + ν ^ 2) * G ν 0 x t) (Ioi 0) :=
    (((G_integrable ν 2 hx).const_mul _).sub ((G_integrable ν 1 hx).const_mul _)).sub
      ((G_integrable ν 0 hx).const_mul _)
  have htend : Tendsto (fun t => -(Real.exp (-x * Real.cosh t) *
      (x * Real.sinh t * Real.cosh (ν * t) + ν * Real.sinh (ν * t)))) atTop (𝓝 0) := by
    have hlim : Tendsto (fun t : ℝ =>
        (x * Real.exp ((((1 : ℕ) : ℝ) + |ν| + 1) ^ 2 / x)
          + |ν| * Real.exp ((((0 : ℕ) : ℝ) + |ν| + 1) ^ 2 / x)) * Real.exp (-t)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul
        (x * Real.exp ((((1 : ℕ) : ℝ) + |ν| + 1) ^ 2 / x)
          + |ν| * Real.exp ((((0 : ℕ) : ℝ) + |ν| + 1) ^ 2 / x))
      rw [mul_zero] at this
      exact this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have b1 := G_bound ν 1 hx le_rfl ht
    have b0 := G_bound ν 0 hx le_rfl ht
    have hsinh : 0 ≤ Real.sinh t := Real.sinh_nonneg_iff.2 ht
    have hsc : Real.sinh t ≤ Real.cosh t := (Real.sinh_lt_cosh t).le
    have hs2 : |Real.sinh (ν * t)| ≤ Real.cosh (ν * t) := by
      rw [Real.abs_sinh, ← Real.cosh_abs (ν * t)]
      exact (Real.sinh_lt_cosh _).le
    have hcν := Real.cosh_pos (ν * t)
    have hE := Real.exp_pos (-x * Real.cosh t)
    have hG1 : G ν 1 x t = Real.cosh t * Real.exp (-x * Real.cosh t) * Real.cosh (ν * t) := by
      simp only [G, pow_one]
    have hG0 : G ν 0 x t = Real.exp (-x * Real.cosh t) * Real.cosh (ν * t) := by
      simp only [G, pow_zero, one_mul]
    rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos hE]
    have habs : |x * Real.sinh t * Real.cosh (ν * t) + ν * Real.sinh (ν * t)|
        ≤ x * Real.cosh t * Real.cosh (ν * t) + |ν| * Real.cosh (ν * t) := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsc hx.le) hcν.le
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hs2 (abs_nonneg _)
    calc Real.exp (-x * Real.cosh t) * |x * Real.sinh t * Real.cosh (ν * t) + ν * Real.sinh (ν * t)|
        ≤ Real.exp (-x * Real.cosh t) *
            (x * Real.cosh t * Real.cosh (ν * t) + |ν| * Real.cosh (ν * t)) :=
          mul_le_mul_of_nonneg_left habs hE.le
      _ = x * G ν 1 x t + |ν| * G ν 0 x t := by rw [hG1, hG0]; ring
      _ ≤ x * (Real.exp ((((1 : ℕ) : ℝ) + |ν| + 1) ^ 2 / x) * Real.exp (-t))
            + |ν| * (Real.exp ((((0 : ℕ) : ℝ) + |ν| + 1) ^ 2 / x) * Real.exp (-t)) :=
          add_le_add (mul_le_mul_of_nonneg_left b1 hx.le)
            (mul_le_mul_of_nonneg_left b0 (abs_nonneg _))
      _ = _ := by ring
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  have hsplit : ∫ t in Ioi (0 : ℝ), (x ^ 2 * G ν 2 x t - x * G ν 1 x t - (x ^ 2 + ν ^ 2) * G ν 0 x t)
      = x ^ 2 * F ν 2 x - x * F ν 1 x - (x ^ 2 + ν ^ 2) * F ν 0 x := by
    unfold F
    rw [integral_sub, integral_sub, integral_const_mul, integral_const_mul, integral_const_mul]
    all_goals first
      | exact (G_integrable ν 2 hx).const_mul _
      | exact (G_integrable ν 1 hx).const_mul _
      | exact (G_integrable ν 0 hx).const_mul _
      | exact ((G_integrable ν 2 hx).const_mul _).sub ((G_integrable ν 1 hx).const_mul _)
  rw [← hsplit, hftc]
  simp

end GKP1998Aux
open Filter Topology Asymptotics GKP1998 in
theorem solution (k z : ℝ) (hk : 0 < k) (hz : 0 < z) :
    throatOperator k 0 (fun w => w ^ 2 * besselK 2 (k * w)) z = 0 := by
  simp only [GKP1998Aux.F_zero]
  have hpow2 : ∀ w : ℝ, HasDerivAt (fun w : ℝ => w ^ 2) (2 * w) w := by
    intro w; simpa using hasDerivAt_pow 2 w
  have hpow3 : ∀ w : ℝ, HasDerivAt (fun w : ℝ => w ^ 3) (3 * w ^ 2) w := by
    intro w; simpa using hasDerivAt_pow 3 w
  have hFc : ∀ (n : ℕ) (w : ℝ), 0 < w → HasDerivAt (fun w => GKP1998Aux.F 2 n (k * w))
      (-GKP1998Aux.F 2 (n + 1) (k * w) * k) w := by
    intro n w hw
    have h1 : HasDerivAt (fun w : ℝ => k * w) k w :=
      ((hasDerivAt_id' w).const_mul k).congr_deriv (mul_one k)
    exact (GKP1998Aux.F_hasDerivAt 2 n (mul_pos hk hw)).comp w h1
  have hd1 : ∀ w : ℝ, 0 < w → HasDerivAt (fun w => w ^ 2 * GKP1998Aux.F 2 0 (k * w))
      (2 * w * GKP1998Aux.F 2 0 (k * w)
        - k * w ^ 2 * GKP1998Aux.F 2 1 (k * w)) w := by
    intro w hw
    exact ((hpow2 w).mul (hFc 0 w hw)).congr_deriv (by ring)
  have hev : (fun w => deriv (fun w => w ^ 2 * GKP1998Aux.F 2 0 (k * w)) w / w ^ 3)
      =ᶠ[𝓝 z] (fun w => (2 * w * GKP1998Aux.F 2 0 (k * w)
          - k * w ^ 2 * GKP1998Aux.F 2 1 (k * w)) / w ^ 3) := by
    filter_upwards [Ioi_mem_nhds hz] with w hw
    rw [(hd1 w hw).deriv]
  unfold GKP1998.throatOperator
  rw [hev.deriv_eq]
  have hkz : 0 < k * z := mul_pos hk hz
  have hA : HasDerivAt (fun w => 2 * w * GKP1998Aux.F 2 0 (k * w))
      (2 * GKP1998Aux.F 2 0 (k * z) - 2 * k * z * GKP1998Aux.F 2 1 (k * z)) z :=
    (((hasDerivAt_id' z).const_mul 2).mul (hFc 0 z hz)).congr_deriv (by ring)
  have hB : HasDerivAt (fun w => k * w ^ 2 * GKP1998Aux.F 2 1 (k * w))
      (2 * k * z * GKP1998Aux.F 2 1 (k * z)
        - k ^ 2 * z ^ 2 * GKP1998Aux.F 2 2 (k * z)) z :=
    (((hpow2 z).const_mul k).mul (hFc 1 z hz)).congr_deriv (by ring)
  have hNum : HasDerivAt (fun w => 2 * w * GKP1998Aux.F 2 0 (k * w)
          - k * w ^ 2 * GKP1998Aux.F 2 1 (k * w))
      (2 * GKP1998Aux.F 2 0 (k * z) - 2 * k * z * GKP1998Aux.F 2 1 (k * z)
        - (2 * k * z * GKP1998Aux.F 2 1 (k * z)
          - k ^ 2 * z ^ 2 * GKP1998Aux.F 2 2 (k * z))) z := hA.sub hB
  have hN : HasDerivAt (fun w => (2 * w * GKP1998Aux.F 2 0 (k * w)
          - k * w ^ 2 * GKP1998Aux.F 2 1 (k * w)) / w ^ 3)
      (((2 * GKP1998Aux.F 2 0 (k * z) - 2 * k * z * GKP1998Aux.F 2 1 (k * z)
        - (2 * k * z * GKP1998Aux.F 2 1 (k * z)
          - k ^ 2 * z ^ 2 * GKP1998Aux.F 2 2 (k * z))) * z ^ 3
        - (2 * z * GKP1998Aux.F 2 0 (k * z)
          - k * z ^ 2 * GKP1998Aux.F 2 1 (k * z)) * (3 * z ^ 2)) / (z ^ 3) ^ 2) z :=
    hNum.div (hpow3 z) (by positivity)
  rw [hN.deriv]
  have hz0 : z ≠ 0 := hz.ne'
  have hV : z ^ 3 * (((2 * GKP1998Aux.F 2 0 (k * z)
        - 2 * k * z * GKP1998Aux.F 2 1 (k * z)
        - (2 * k * z * GKP1998Aux.F 2 1 (k * z)
          - k ^ 2 * z ^ 2 * GKP1998Aux.F 2 2 (k * z))) * z ^ 3
        - (2 * z * GKP1998Aux.F 2 0 (k * z)
          - k * z ^ 2 * GKP1998Aux.F 2 1 (k * z)) * (3 * z ^ 2)) / (z ^ 3) ^ 2)
      = k ^ 2 * z ^ 2 * GKP1998Aux.F 2 2 (k * z)
        - k * z * GKP1998Aux.F 2 1 (k * z) - 4 * GKP1998Aux.F 2 0 (k * z) := by
    field_simp
    ring
  beta_reduce
  rw [hV]
  have hode := GKP1998Aux.bessel_ode 2 hkz
  linear_combination hode
