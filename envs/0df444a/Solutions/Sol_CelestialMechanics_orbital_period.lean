-- Prove2me | solution 1 for CelestialMechanics.orbital_period
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:30:52.252832+00:00
-- url     : https://prove2.me/submissions/900e5620-ace2-4f4a-a41e-d37721d4af5f

import Mathlib
import Definitions.Def_CelestialMechanics_binary_star_dynamics

open CelestialMechanics

/-- The mean anomaly as a smooth function of the true anomaly. -/
noncomputable def W7b_CelestialMechanics_Mf (β e s : ℝ) (θ : ℝ) : ℝ :=
  θ - 2 * Real.arctan (β * Real.sin θ / (1 + β * Real.cos θ))
    - e * s * Real.sin θ / (1 + e * Real.cos θ)

theorem W7b_CelestialMechanics_Mf_periodic (β e s θ : ℝ) :
    W7b_CelestialMechanics_Mf β e s (θ + 2 * Real.pi) = W7b_CelestialMechanics_Mf β e s θ + 2 * Real.pi := by
  unfold W7b_CelestialMechanics_Mf
  rw [Real.sin_add_two_pi, Real.cos_add_two_pi]
  ring

theorem W7b_CelestialMechanics_Mf_deriv (β e s θ : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (he : e = 2 * β / (1 + β ^ 2)) (hs : s = (1 - β ^ 2) / (1 + β ^ 2)) :
    HasDerivAt (W7b_CelestialMechanics_Mf β e s) (s ^ 3 / (1 + e * Real.cos θ) ^ 2) θ := by
  set c := Real.cos θ with hc
  set sn := Real.sin θ with hsnd
  have hsn : sn ^ 2 = 1 - c ^ 2 := by rw [hsnd, hc]; exact Real.sin_sq θ
  have hc1 : c ≤ 1 := Real.cos_le_one θ
  have hc2 : -1 ≤ c := Real.neg_one_le_cos θ
  have hb2 : 0 < 1 + β ^ 2 := by positivity
  have hD : 0 < 1 + β * c := by nlinarith
  have he1 : e < 1 := by
    rw [he, div_lt_one hb2]; nlinarith [sq_nonneg (1 - β)]
  have he0 : 0 ≤ e := by rw [he]; positivity
  have hE : 0 < 1 + e * c := by nlinarith
  have hw := ((Real.hasDerivAt_sin θ).const_mul β).div
    (((Real.hasDerivAt_cos θ).const_mul β).const_add 1) hD.ne'
  have ha := hw.arctan
  have hq := ((Real.hasDerivAt_sin θ).const_mul (e * s)).div
    (((Real.hasDerivAt_cos θ).const_mul e).const_add 1) hE.ne'
  have htot := ((hasDerivAt_id θ).sub (ha.const_mul 2)).sub hq
  have p1 : β * c * (1 + β * c) - β * sn * (β * -sn) = β * (c + β) := by
    linear_combination β ^ 2 * hsn
  have p2 : 1 + (β * sn / (1 + β * c)) ^ 2 = (1 + 2 * β * c + β ^ 2) / (1 + β * c) ^ 2 := by
    rw [div_pow, mul_pow, eq_div_iff (by positivity)]
    field_simp
    linear_combination β ^ 2 * hsn
  have p3 : e * s * c * (1 + e * c) - e * s * sn * (e * -sn) = e * s * (c + e) := by
    linear_combination e ^ 2 * s * hsn
  have hq2 : 0 < 1 + 2 * β * c + β ^ 2 := by nlinarith
  unfold W7b_CelestialMechanics_Mf
  refine HasDerivAt.congr_of_eventuallyEq (htot.congr_deriv ?_)
    (Filter.Eventually.of_forall fun y => ?_)
  · simp only [Pi.div_apply]
    rw [← hc, ← hsnd, p1, p2, p3, he, hs]
    rw [show (1 : ℝ) + 2 * β / (1 + β ^ 2) * c = (1 + 2 * β * c + β ^ 2) / (1 + β ^ 2) by
      field_simp; ring]
    have h1 := hq2.ne'
    have h2 := hb2.ne'
    have h3 := hD.ne'
    field_simp
    ring
  · simp only [Pi.div_apply, Pi.sub_apply, id]

theorem solution (G M a e h T t₀ : ℝ) (rad th : ℝ → ℝ) (r : ℝ → Space)
    (hG : 0 < G) (hM : 0 < M) (ha : 0 < a) (he0 : 0 ≤ e) (he1 : e < 1)
    (hh : 0 < h) (hha : h ^ 2 = (1 - e ^ 2) * G * M * a)
    (horb : IsConicOrbit a e h rad th r)
    (hT : 0 < T) (hrev : th (t₀ + T) = th t₀ + 2 * Real.pi) :
    T = Real.sqrt (4 * Real.pi ^ 2 * a ^ 3 / (G * M)) := by
  obtain ⟨hdiff, hrad, hder, -, -, -⟩ := horb
  set s := Real.sqrt (1 - e ^ 2) with hsdef
  have he2 : 0 < 1 - e ^ 2 := by nlinarith
  have hs0 : 0 < s := Real.sqrt_pos.mpr he2
  have hs2 : s ^ 2 = 1 - e ^ 2 := Real.sq_sqrt he2.le
  set β := e / (1 + s) with hβdef
  have hβ0 : 0 ≤ β := by positivity
  have hβ1 : β < 1 := by rw [hβdef, div_lt_one (by positivity)]; linarith
  have hbe : e = 2 * β / (1 + β ^ 2) := by
    rw [hβdef]; field_simp
    first
      | linear_combination 2 * e * hs2
      | linear_combination (-2) * e * hs2
      | linear_combination e * hs2
      | linear_combination (-e) * hs2
  have hbs : s = (1 - β ^ 2) / (1 + β ^ 2) := by
    rw [hβdef]; field_simp
    first
      | linear_combination (1 + s) * hs2
      | linear_combination (-(1 + s)) * hs2
      | linear_combination 2 * (1 + s) * hs2
      | linear_combination (-2) * (1 + s) * hs2
  set n := h / (a ^ 2 * s) with hn
  set Gf := fun t => W7b_CelestialMechanics_Mf β e s (th t) with hGf
  have hGd : ∀ t, HasDerivAt Gf n t := by
    intro t
    have h1 := (W7b_CelestialMechanics_Mf_deriv β e s (th t) hβ0 hβ1 hbe hbs).comp t
      (hdiff t).hasDerivAt
    refine h1.congr_deriv ?_
    rw [hder t, hrad t]
    have hE : 0 < 1 + e * Real.cos (th t) := by nlinarith [Real.neg_one_le_cos (th t)]
    rw [hn]
    field_simp
    rw [show (1 - e ^ 2) = s ^ 2 from hs2.symm]
    ring
  have hconst : ∀ x y, (fun t => Gf t - n * t) x = (fun t => Gf t - n * t) y := by
    apply is_const_of_deriv_eq_zero
    · intro t
      have hd : HasDerivAt (fun t => Gf t - n * t) (n - n * 1) t :=
        (hGd t).sub ((hasDerivAt_id' t).const_mul n)
      exact hd.differentiableAt
    · intro t
      have hd : HasDerivAt (fun t => Gf t - n * t) (n - n * 1) t :=
        (hGd t).sub ((hasDerivAt_id' t).const_mul n)
      rw [hd.deriv]; ring
  have key := hconst (t₀ + T) t₀
  simp only [hGf, hrev, W7b_CelestialMechanics_Mf_periodic] at key
  have hnT : n * T = 2 * Real.pi := by linarith
  have hnpos : 0 < n := by positivity
  have hTval : T = 2 * Real.pi * a ^ 2 * s / h := by
    rw [hn] at hnT
    field_simp at hnT
    field_simp
    linarith
  have hsq : T ^ 2 = 4 * Real.pi ^ 2 * a ^ 3 / (G * M) := by
    rw [hTval, div_pow]
    rw [hha, show (1 - e ^ 2) = s ^ 2 from hs2.symm]
    field_simp
    ring
  rw [← hsq, Real.sqrt_sq hT.le]
