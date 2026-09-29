-- Prove2me | solution 1 for CelestialMechanics.binary_star_system_solution
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:53:16.698983+00:00
-- url     : https://prove2.me/submissions/e1df9311-bc58-43c0-b14f-f022f7b82631

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

theorem W7b_CelestialMechanics_orbital_period (G M a e h T t₀ : ℝ) (rad th : ℝ → ℝ) (r : ℝ → Space)
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


/-! ## Construction of the binary star solution -/

theorem W7b_CelestialMechanics_Mf_cont (β e s : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (he : e = 2 * β / (1 + β ^ 2)) (hs : s = (1 - β ^ 2) / (1 + β ^ 2)) :
    Continuous (W7b_CelestialMechanics_Mf β e s) :=
  continuous_iff_continuousAt.mpr fun θ =>
    (W7b_CelestialMechanics_Mf_deriv β e s θ hβ0 hβ1 he hs).continuousAt

theorem W7b_CelestialMechanics_kepler_comp (hh G M p E C : ℝ) (hE : 0 < E) (hp : 0 < p)
    (hh2 : hh ^ 2 = G * M * p) :
    -(hh / p) * C * (hh * E ^ 2 / p ^ 2) = (-(G * M) / (p / E) ^ 3) * (p * C / E) := by
  have h1 : -(hh / p) * C * (hh * E ^ 2 / p ^ 2) = -(hh ^ 2) * C * E ^ 2 / p ^ 3 := by
    field_simp
    try ring
  rw [h1, hh2]
  field_simp
  try ring

/-- Existence of the true anomaly as a function of time. -/
theorem W7b_CelestialMechanics_theta_exists (e s β hh p n : ℝ) (he0 : 0 ≤ e) (he1 : e < 1)
    (hs0 : 0 < s) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hbe : e = 2 * β / (1 + β ^ 2)) (hbs : s = (1 - β ^ 2) / (1 + β ^ 2))
    (hnpos : 0 < n) (hnrel : ∀ x : ℝ, 0 < 1 + e * Real.cos x →
      (s ^ 3 / (1 + e * Real.cos x) ^ 2)⁻¹ * n = hh * (1 + e * Real.cos x) ^ 2 / p ^ 2) :
    ∃ th : ℝ → ℝ, (∀ t, HasDerivAt th (hh * (1 + e * Real.cos (th t)) ^ 2 / p ^ 2) t) ∧
      (∀ t, th (t + 2 * Real.pi / n) = th t + 2 * Real.pi) := by
  set Mf := W7b_CelestialMechanics_Mf β e s with hMf
  have hMfd : ∀ θ, HasDerivAt Mf (s ^ 3 / (1 + e * Real.cos θ) ^ 2) θ := fun θ =>
    W7b_CelestialMechanics_Mf_deriv β e s θ hβ0 hβ1 hbe hbs
  have hE : ∀ θ, 0 < 1 + e * Real.cos θ := fun θ => by
    nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  have hMfc : Continuous Mf := W7b_CelestialMechanics_Mf_cont β e s hβ0 hβ1 hbe hbs
  have hmono : StrictMono Mf := strictMono_of_deriv_pos fun θ => by
    rw [(hMfd θ).deriv]; have := hE θ; positivity
  have hbd : ∀ θ, |Mf θ - θ| ≤ Real.pi + e * s / (1 - e) := by
    intro θ
    simp only [hMf, W7b_CelestialMechanics_Mf]
    have h1 := Real.arctan_lt_pi_div_two (β * Real.sin θ / (1 + β * Real.cos θ))
    have h2 := Real.neg_pi_div_two_lt_arctan (β * Real.sin θ / (1 + β * Real.cos θ))
    have h3 : |e * s * Real.sin θ / (1 + e * Real.cos θ)| ≤ e * s / (1 - e) := by
      rw [abs_div, abs_of_pos (hE θ), abs_mul, abs_of_nonneg (by positivity : 0 ≤ e * s)]
      rw [div_le_div_iff₀ (hE θ) (by linarith)]
      have hc : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
      have hsn : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
      have hes : 0 ≤ e * s := by positivity
      have k1 : e * s * |Real.sin θ| * (1 - e) ≤ e * s * (1 - e) :=
        mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hes hsn) (by linarith)
      have k2 : e * s * (1 - e) ≤ e * s * (1 + e * Real.cos θ) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hes
      linarith
    rw [abs_le] at h3 ⊢
    constructor <;> linarith [h3.1, h3.2]
  have hsurj : Function.Surjective Mf := by
    apply hMfc.surjective
    · refine Filter.tendsto_atTop_mono (fun θ => ?_)
        (Filter.tendsto_atTop_add_const_right _ (-(Real.pi + e * s / (1 - e))) Filter.tendsto_id)
      have := hbd θ; rw [abs_le] at this; simp only [id]; linarith [this.1]
    · refine Filter.tendsto_atBot_mono (fun θ => ?_)
        (Filter.tendsto_atBot_add_const_right _ (Real.pi + e * s / (1 - e)) Filter.tendsto_id)
      have := hbd θ; rw [abs_le] at this; simp only [id]; linarith [this.2]
  set iso := StrictMono.orderIsoOfSurjective Mf hmono hsurj with hiso
  refine ⟨fun t => iso.symm (n * t), ?_, ?_⟩
  · intro t
    have hinv : HasDerivAt (fun y => iso.symm y)
        (s ^ 3 / (1 + e * Real.cos (iso.symm (n * t))) ^ 2)⁻¹ (n * t) := by
      apply HasDerivAt.of_local_left_inverse iso.symm.continuous.continuousAt (hMfd _)
      · have := hE (iso.symm (n * t)); positivity
      · exact Filter.Eventually.of_forall fun y =>
          StrictMono.orderIsoOfSurjective_self_symm_apply Mf hmono hsurj y
    have := hinv.comp t ((hasDerivAt_id' t).const_mul n)
    refine this.congr_deriv ?_
    rw [mul_one]
    exact hnrel _ (hE _)
  · intro t
    have h1 : n * (t + 2 * Real.pi / n) = Mf (iso.symm (n * t) + 2 * Real.pi) := by
      rw [hMf, W7b_CelestialMechanics_Mf_periodic, ← hMf,
        StrictMono.orderIsoOfSurjective_self_symm_apply Mf hmono hsurj]
      field_simp
    show iso.symm (n * (t + 2 * Real.pi / n)) = iso.symm (n * t) + 2 * Real.pi
    rw [h1]
    exact StrictMono.orderIsoOfSurjective_symm_apply_self Mf hmono hsurj _

/-- The Keplerian curve in the `x`-`y` plane. -/
noncomputable def W7b_CelestialMechanics_curve (p e : ℝ) (th : ℝ → ℝ) (t : ℝ) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm
    ![p * Real.cos (th t) / (1 + e * Real.cos (th t)), p * Real.sin (th t) / (1 + e * Real.cos (th t)), 0]

theorem W7b_CelestialMechanics_curve_apply (p e : ℝ) (th : ℝ → ℝ) (t : ℝ) :
    W7b_CelestialMechanics_curve p e th t 0 = p * Real.cos (th t) / (1 + e * Real.cos (th t)) ∧
    W7b_CelestialMechanics_curve p e th t 1 = p * Real.sin (th t) / (1 + e * Real.cos (th t)) ∧
    W7b_CelestialMechanics_curve p e th t 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [W7b_CelestialMechanics_curve]

theorem W7b_CelestialMechanics_curve_norm (p e : ℝ) (th : ℝ → ℝ) (t : ℝ) (hp : 0 < p)
    (hE : 0 < 1 + e * Real.cos (th t)) :
    ‖W7b_CelestialMechanics_curve p e th t‖ = p / (1 + e * Real.cos (th t)) := by
  obtain ⟨c0, c1, c2⟩ := W7b_CelestialMechanics_curve_apply p e th t
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, c0, c1, c2, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, sq_abs, norm_zero]
  have hsc := Real.sin_sq_add_cos_sq (th t)
  have h : (p * Real.cos (th t) / (1 + e * Real.cos (th t))) ^ 2 +
      (p * Real.sin (th t) / (1 + e * Real.cos (th t))) ^ 2 + 0 ^ 2 =
      (p / (1 + e * Real.cos (th t))) ^ 2 := by
    have e1 : (p * Real.cos (th t) / (1 + e * Real.cos (th t))) ^ 2 +
        (p * Real.sin (th t) / (1 + e * Real.cos (th t))) ^ 2 + 0 ^ 2 =
        (p / (1 + e * Real.cos (th t))) ^ 2 * (Real.sin (th t) ^ 2 + Real.cos (th t) ^ 2) := by ring
    rw [e1, hsc, mul_one]
  rw [h, Real.sqrt_sq (by positivity)]

theorem W7b_CelestialMechanics_curve_newton (G M p e hh : ℝ) (th : ℝ → ℝ) (he0 : 0 ≤ e)
    (he1 : e < 1) (hp : 0 < p) (hh2 : hh ^ 2 = G * M * p)
    (hthd : ∀ t, HasDerivAt th (hh * (1 + e * Real.cos (th t)) ^ 2 / p ^ 2) t) (t : ℝ) :
    iteratedDeriv 2 (W7b_CelestialMechanics_curve p e th) t =
      (-(G * M) / ‖W7b_CelestialMechanics_curve p e th t‖ ^ 3) •
        W7b_CelestialMechanics_curve p e th t := by
  have hE : ∀ x, 0 < 1 + e * Real.cos x := fun x => by
    nlinarith [Real.neg_one_le_cos x, Real.cos_le_one x]
  set Φ : ℝ → ℝ := fun x => hh * (1 + e * Real.cos x) ^ 2 / p ^ 2 with hΦ
  set Lsym := (EuclideanSpace.equiv (Fin 3) ℝ).symm with hLsym
  set u : ℝ → (Fin 3 → ℝ) := fun t =>
    ![p * Real.cos (th t) / (1 + e * Real.cos (th t)), p * Real.sin (th t) / (1 + e * Real.cos (th t)), 0]
    with hu
  set u1 : ℝ → (Fin 3 → ℝ) := fun t =>
    ![-(hh / p) * Real.sin (th t), hh / p * (Real.cos (th t) + e), 0] with hu1
  set u2 : ℝ → (Fin 3 → ℝ) := fun t =>
    ![-(hh / p) * Real.cos (th t) * Φ (th t), -(hh / p) * Real.sin (th t) * Φ (th t), 0] with hu2
  have hcurve : W7b_CelestialMechanics_curve p e th = fun t => Lsym (u t) := rfl
  have hXd : ∀ x, HasDerivAt (fun x => p * Real.cos x / (1 + e * Real.cos x))
      (-p * Real.sin x / (1 + e * Real.cos x) ^ 2) x := by
    intro x
    have := ((Real.hasDerivAt_cos x).const_mul p).div
      (((Real.hasDerivAt_cos x).const_mul e).const_add 1) (hE x).ne'
    refine this.congr_deriv ?_
    congr 1
    ring
  have hYd : ∀ x, HasDerivAt (fun x => p * Real.sin x / (1 + e * Real.cos x))
      (p * (Real.cos x + e) / (1 + e * Real.cos x) ^ 2) x := by
    intro x
    have := ((Real.hasDerivAt_sin x).const_mul p).div
      (((Real.hasDerivAt_cos x).const_mul e).const_add 1) (hE x).ne'
    refine this.congr_deriv ?_
    have hsc := Real.sin_sq_add_cos_sq x
    congr 1
    linear_combination p * e * hsc
  have hud : ∀ t, HasDerivAt u (u1 t) t := by
    intro t
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · have := (hXd (th t)).comp t (hthd t)
      refine this.congr_deriv ?_
      show -p * Real.sin (th t) / (1 + e * Real.cos (th t)) ^ 2 *
        (hh * (1 + e * Real.cos (th t)) ^ 2 / p ^ 2) = -(hh / p) * Real.sin (th t)
      have h1 := (hE (th t)).ne'
      have h2 : 1 + Real.cos (th t) * e ≠ 0 := by rw [mul_comm]; exact h1
      field_simp
    · have := (hYd (th t)).comp t (hthd t)
      refine this.congr_deriv ?_
      show p * (Real.cos (th t) + e) / (1 + e * Real.cos (th t)) ^ 2 *
        (hh * (1 + e * Real.cos (th t)) ^ 2 / p ^ 2) = hh / p * (Real.cos (th t) + e)
      have h1 := (hE (th t)).ne'
      have h2 : 1 + Real.cos (th t) * e ≠ 0 := by rw [mul_comm]; exact h1
      field_simp
    · exact hasDerivAt_const t (0 : ℝ)
  have hu1d : ∀ t, HasDerivAt u1 (u2 t) t := by
    intro t
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · have := ((Real.hasDerivAt_sin (th t)).comp t (hthd t)).const_mul (-(hh / p))
      refine this.congr_deriv ?_
      show -(hh / p) * (Real.cos (th t) * (hh * (1 + e * Real.cos (th t)) ^ 2 / p ^ 2)) =
        -(hh / p) * Real.cos (th t) * Φ (th t)
      simp only [hΦ]; ring
    · have := (((Real.hasDerivAt_cos (th t)).comp t (hthd t)).add_const e).const_mul (hh / p)
      refine this.congr_deriv ?_
      show hh / p * (-Real.sin (th t) * (hh * (1 + e * Real.cos (th t)) ^ 2 / p ^ 2)) =
        -(hh / p) * Real.sin (th t) * Φ (th t)
      simp only [hΦ]; ring
    · exact hasDerivAt_const t (0 : ℝ)
  have hrd : ∀ t, HasDerivAt (fun t => Lsym (u t)) (Lsym (u1 t)) t := fun t =>
    Lsym.hasFDerivAt.comp_hasDerivAt t (hud t)
  have hr1d : ∀ t, HasDerivAt (fun t => Lsym (u1 t)) (Lsym (u2 t)) t := fun t =>
    Lsym.hasFDerivAt.comp_hasDerivAt t (hu1d t)
  have hderiv_r : deriv (fun t => Lsym (u t)) = fun t => Lsym (u1 t) := funext fun t => (hrd t).deriv
  rw [hcurve, iteratedDeriv_succ, iteratedDeriv_one, hderiv_r, (hr1d t).deriv]
  have hnorm := W7b_CelestialMechanics_curve_norm p e th t hp (hE (th t))
  rw [hcurve] at hnorm
  rw [hnorm, ← map_smul]
  congr 1
  funext i
  fin_cases i
  · show -(hh / p) * Real.cos (th t) * Φ (th t) =
      (-(G * M) / (p / (1 + e * Real.cos (th t))) ^ 3) *
        (p * Real.cos (th t) / (1 + e * Real.cos (th t)))
    simp only [hΦ]
    exact W7b_CelestialMechanics_kepler_comp hh G M p _ (Real.cos (th t)) (hE _) hp hh2
  · show -(hh / p) * Real.sin (th t) * Φ (th t) =
      (-(G * M) / (p / (1 + e * Real.cos (th t))) ^ 3) *
        (p * Real.sin (th t) / (1 + e * Real.cos (th t)))
    simp only [hΦ]
    exact W7b_CelestialMechanics_kepler_comp hh G M p _ (Real.sin (th t)) (hE _) hp hh2
  · show (0 : ℝ) = (-(G * M) / (p / (1 + e * Real.cos (th t))) ^ 3) * 0
    ring

theorem W7b_CelestialMechanics_curve_contDiff (p e : ℝ) (th : ℝ → ℝ) (he0 : 0 ≤ e) (he1 : e < 1)
    (hth : ContDiff ℝ 2 th) : ContDiff ℝ 2 (W7b_CelestialMechanics_curve p e th) := by
  have hE : ∀ x, 0 < 1 + e * Real.cos x := fun x => by
    nlinarith [Real.neg_one_le_cos x, Real.cos_le_one x]
  have hvec : ContDiff ℝ ⊤ (fun x : ℝ => (![p * Real.cos x / (1 + e * Real.cos x),
      p * Real.sin x / (1 + e * Real.cos x), 0] : Fin 3 → ℝ)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i
    · exact ContDiff.div (by fun_prop) (by fun_prop) (fun x => (hE x).ne')
    · exact ContDiff.div (by fun_prop) (by fun_prop) (fun x => (hE x).ne')
    · exact contDiff_const
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp ((hvec.of_le le_top).comp hth)

theorem W7b_CelestialMechanics_iter_smul (f : ℝ → Space) (c : ℝ) (hf : ContDiff ℝ 2 f) (t : ℝ) :
    iteratedDeriv 2 (fun t => c • f t) t = c • iteratedDeriv 2 f t :=
  iteratedDeriv_const_smul hf.contDiffAt c

theorem W7b_CelestialMechanics_cd_smul (f : ℝ → Space) (c : ℝ) (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (fun t => c • f t) := hf.const_smul c

theorem W7b_CelestialMechanics_sub_smul (v : Space) (m₁ m₂ : ℝ) (hM : 0 < m₁ + m₂) :
    (m₁ / (m₁ + m₂)) • v - (-(m₂ / (m₁ + m₂))) • v = v := by
  rw [← sub_smul]
  have : m₁ / (m₁ + m₂) - -(m₂ / (m₁ + m₂)) = 1 := by field_simp; ring
  rw [this, one_smul]

theorem W7b_CelestialMechanics_com (v : Space) (m₁ m₂ : ℝ) :
    m₁ • ((-(m₂ / (m₁ + m₂))) • v) + m₂ • ((m₁ / (m₁ + m₂)) • v) = 0 := by
  rw [smul_smul, smul_smul, ← add_smul]
  have : m₁ * -(m₂ / (m₁ + m₂)) + m₂ * (m₁ / (m₁ + m₂)) = 0 := by ring
  rw [this, zero_smul]

theorem W7b_CelestialMechanics_newton1 (v w : Space) (G m₁ m₂ ρ : ℝ) (hM : 0 < m₁ + m₂)
    (hw : w = (-(G * (m₁ + m₂)) / ρ ^ 3) • v) :
    m₁ • ((-(m₂ / (m₁ + m₂))) • w) = (G * m₁ * m₂ / ρ ^ 3) • v := by
  rw [hw, smul_smul, smul_smul]
  congr 1
  field_simp
  try ring

theorem W7b_CelestialMechanics_newton2 (v w : Space) (G m₁ m₂ ρ : ℝ) (hM : 0 < m₁ + m₂)
    (hw : w = (-(G * (m₁ + m₂)) / ρ ^ 3) • v) :
    m₂ • ((m₁ / (m₁ + m₂)) • w) = (-(G * m₁ * m₂) / ρ ^ 3) • v := by
  rw [hw, smul_smul, smul_smul]
  congr 1
  field_simp
  try ring

theorem solution (G m₁ m₂ a e : ℝ)
    (hG : 0 < G) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (ha : 0 < a) (he0 : 0 ≤ e) (he1 : e < 1) :
    ∃ (r₁ r₂ : ℝ → Space) (rad th : ℝ → ℝ) (T : ℝ),
      IsNewtonianTwoBody G m₁ m₂ r₁ r₂ ∧
      (∀ t, m₁ • r₁ t + m₂ • r₂ t = 0) ∧
      IsConicOrbit a e (Real.sqrt ((1 - e ^ 2) * G * (m₁ + m₂) * a)) rad th
        (fun t => r₂ t - r₁ t) ∧
      (∀ t, r₁ t = (-(m₂ / (m₁ + m₂))) • (r₂ t - r₁ t)) ∧
      (∀ t, r₂ t = (m₁ / (m₁ + m₂)) • (r₂ t - r₁ t)) ∧
      0 < T ∧ T = Real.sqrt (4 * Real.pi ^ 2 * a ^ 3 / (G * (m₁ + m₂))) ∧
      (∀ t, r₁ (t + T) = r₁ t) ∧ (∀ t, r₂ (t + T) = r₂ t) := by
  have hM : 0 < m₁ + m₂ := by positivity
  have he2 : 0 < 1 - e ^ 2 := by nlinarith
  set s := Real.sqrt (1 - e ^ 2) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr he2
  have hs2 : s ^ 2 = 1 - e ^ 2 := Real.sq_sqrt he2.le
  set hh := Real.sqrt ((1 - e ^ 2) * G * (m₁ + m₂) * a) with hhdef
  have hhpos : 0 < hh := Real.sqrt_pos.mpr (by positivity)
  have hh2 : hh ^ 2 = (1 - e ^ 2) * G * (m₁ + m₂) * a := Real.sq_sqrt (by positivity)
  set p := a * (1 - e ^ 2) with hp
  have hp0 : 0 < p := by positivity
  have hh2' : hh ^ 2 = G * (m₁ + m₂) * p := by rw [hh2, hp]; ring
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
  set n := hh / (a ^ 2 * s) with hn
  have hnpos : 0 < n := by positivity
  have hnrel : ∀ x : ℝ, 0 < 1 + e * Real.cos x →
      (s ^ 3 / (1 + e * Real.cos x) ^ 2)⁻¹ * n = hh * (1 + e * Real.cos x) ^ 2 / p ^ 2 := by
    intro x hx
    rw [hn, hp, show (1 - e ^ 2) = s ^ 2 from hs2.symm]
    field_simp
    try ring
  obtain ⟨th, hthd, hthT⟩ :=
    W7b_CelestialMechanics_theta_exists e s β hh p n he0 he1 hs0 hβ0 hβ1 hbe hbs hnpos hnrel
  have hE : ∀ x, 0 < 1 + e * Real.cos x := fun x => by
    nlinarith [Real.neg_one_le_cos x, Real.cos_le_one x]
  -- regularity of the anomaly
  set Φ : ℝ → ℝ := fun x => hh * (1 + e * Real.cos x) ^ 2 / p ^ 2 with hΦ
  have hthc : Continuous th := continuous_iff_continuousAt.mpr fun t => (hthd t).continuousAt
  have hΦc : ContDiff ℝ ⊤ Φ := by simp only [hΦ]; fun_prop
  have hderiv_th : deriv th = Φ ∘ th := funext fun t => (hthd t).deriv
  have hth1 : ContDiff ℝ 1 th := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (hthd t).differentiableAt, ?_⟩
    rw [hderiv_th]; exact hΦc.continuous.comp hthc
  have hth2 : ContDiff ℝ 2 th := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
    refine ⟨fun t => (hthd t).differentiableAt, by simp, ?_⟩
    rw [hderiv_th]; exact (hΦc.of_le le_top).comp hth1
  set r := W7b_CelestialMechanics_curve p e th with hr
  have hrC : ContDiff ℝ 2 r := W7b_CelestialMechanics_curve_contDiff p e th he0 he1 hth2
  have hnorm : ∀ t, ‖r t‖ = p / (1 + e * Real.cos (th t)) := fun t =>
    W7b_CelestialMechanics_curve_norm p e th t hp0 (hE _)
  have hnewton : ∀ t, iteratedDeriv 2 r t = (-(G * (m₁ + m₂)) / ‖r t‖ ^ 3) • r t := fun t =>
    W7b_CelestialMechanics_curve_newton G (m₁ + m₂) p e hh th he0 he1 hp0 hh2' hthd t
  have hrne : ∀ t, r t ≠ 0 := fun t h => by
    have := hnorm t
    rw [h, norm_zero] at this
    have : 0 < p / (1 + e * Real.cos (th t)) := div_pos hp0 (hE _)
    linarith
  have hsub : ∀ t, (m₁ / (m₁ + m₂)) • r t - (-(m₂ / (m₁ + m₂))) • r t = r t := fun t =>
    W7b_CelestialMechanics_sub_smul (r t) m₁ m₂ hM
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 2 * Real.pi / n := ⟨_, rfl⟩
  have hTpos : 0 < T := by rw [hT]; positivity
  have hrT : ∀ t, r (t + T) = r t := by
    intro t
    rw [hT]
    simp only [hr, W7b_CelestialMechanics_curve, hthT t, Real.cos_add_two_pi, Real.sin_add_two_pi]
  refine ⟨fun t => (-(m₂ / (m₁ + m₂))) • r t, fun t => (m₁ / (m₁ + m₂)) • r t,
    fun t => p / (1 + e * Real.cos (th t)), th, T,
    ⟨W7b_CelestialMechanics_cd_smul r _ hrC, W7b_CelestialMechanics_cd_smul r _ hrC, ?_, ?_, ?_⟩,
    fun t => W7b_CelestialMechanics_com (r t) m₁ m₂,
    ⟨fun t => (hthd t).differentiableAt, fun t => rfl, ?_, ?_, ?_, ?_⟩, ?_, ?_, hTpos, ?_, ?_, ?_⟩
  · intro t h
    apply hrne t
    have := hsub t
    beta_reduce at h
    rw [h, sub_self] at this
    exact this.symm
  · intro t
    rw [W7b_CelestialMechanics_iter_smul r _ hrC t, hsub t]
    exact W7b_CelestialMechanics_newton1 (r t) _ G m₁ m₂ ‖r t‖ hM (hnewton t)
  · intro t
    rw [W7b_CelestialMechanics_iter_smul r _ hrC t, hsub t]
    exact W7b_CelestialMechanics_newton2 (r t) _ G m₁ m₂ ‖r t‖ hM (hnewton t)
  · intro t
    rw [(hthd t).deriv]
    have h1 := (hE (th t)).ne'
    field_simp
  · intro t
    show ((m₁ / (m₁ + m₂)) • r t - (-(m₂ / (m₁ + m₂))) • r t) 0 = _
    rw [hsub t, (W7b_CelestialMechanics_curve_apply p e th t).1]
    ring
  · intro t
    show ((m₁ / (m₁ + m₂)) • r t - (-(m₂ / (m₁ + m₂))) • r t) 1 = _
    rw [hsub t, (W7b_CelestialMechanics_curve_apply p e th t).2.1]
    ring
  · intro t
    show ((m₁ / (m₁ + m₂)) • r t - (-(m₂ / (m₁ + m₂))) • r t) 2 = _
    rw [hsub t, (W7b_CelestialMechanics_curve_apply p e th t).2.2]
  · intro t; show _ = _ • ((m₁ / (m₁ + m₂)) • r t - (-(m₂ / (m₁ + m₂))) • r t); rw [hsub t]
  · intro t; show _ = _ • ((m₁ / (m₁ + m₂)) • r t - (-(m₂ / (m₁ + m₂))) • r t); rw [hsub t]
  · have hTval : T = 2 * Real.pi * a ^ 2 * s / hh := by
      rw [hT, hn]; field_simp
    have hsq : T ^ 2 = 4 * Real.pi ^ 2 * a ^ 3 / (G * (m₁ + m₂)) := by
      rw [hTval, div_pow, hh2, show (1 - e ^ 2) = s ^ 2 from hs2.symm]
      field_simp
      ring
    rw [← hsq, Real.sqrt_sq hTpos.le]
  · intro t; show _ • r (t + T) = _ • r t; rw [hrT]
  · intro t; show _ • r (t + T) = _ • r t; rw [hrT]
