-- Prove2me | solution 1 for FlatlyFoliated.scalar_vacuum_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T18:06:23.425751+00:00
-- url     : https://prove2.me/submissions/827ea422-6ae1-4148-9212-87d08f204084

import Theorems.Thm_FlatlyFoliated_lemma1_symmetrization
import Theorems.Thm_FlatlyFoliated_symmetrization_flux_bound

open scoped ContDiff Topology
open FlatlyFoliated Filter Set Metric MeasureTheory

namespace ScalarVacuum

set_option backward.isDefEq.respectTransparency false
attribute [local instance] PiLp.normedAddCommGroup PiLp.normedSpace

private noncomputable abbrev axis (r : ℝ) : R3 := EuclideanSpace.single 0 r

private lemma axis_norm {r : ℝ} (hr : 0 ≤ r) : ‖axis r‖ = r := by
  simp [axis, Real.norm_eq_abs, abs_of_nonneg hr]

private lemma axis_deriv (r : ℝ) : HasDerivAt axis (axis 1) r := by
  have h := (hasDerivAt_id r).smul_const (axis 1)
  simp only [id_eq, one_smul] at h
  convert! h using 1
  ext s i
  simp [axis]

private lemma smooth_pd {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin 3) :
    ContDiff ℝ ∞ (pd i u) :=
  (hu.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

private lemma profile_deriv {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (r : ℝ) :
    HasDerivAt (fun s => u (axis s)) (pd 0 u (axis r)) r :=
  (hu.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r (axis_deriv r)

private lemma norm_deriv {x : R3} (hx : 0 < ‖x‖) :
    HasFDerivAt (fun y : R3 => ‖y‖) ((‖x‖)⁻¹ • innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 (ne_of_gt hx))
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  have he : (‖x‖)⁻¹ • innerSL ℝ x = (1 / (2 * ‖x‖)) • 2 • innerSL ℝ x := by
    ext v
    simp only [two_smul, add_apply, smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [← he] at h
  exact h

private lemma inner_axis (x : R3) (j : Fin 3) :
    innerSL ℝ x (EuclideanSpace.single j 1) = x j := by
  simp [innerSL_apply_apply, EuclideanSpace.inner_single_right]

private lemma radial_pd {b : ℝ → ℝ} {u : R3 → ℝ} {x : R3} {j i : Fin 3}
    (hx : 0 < ‖x‖) (hb : DifferentiableAt ℝ b ‖x‖)
    (he : u =ᶠ[𝓝 x] (fun y => b ‖y‖ * y i)) :
    pd j u x = deriv b ‖x‖ * (x j / ‖x‖) * x i +
      b ‖x‖ * (if i = j then 1 else 0) := by
  have h := (hb.hasDerivAt.comp_hasFDerivAt x (norm_deriv hx)).fun_mul
    (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun y : R3 => b ‖y‖ * y i) _ x at h
  rw [pd, he.fderiv_eq, h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, inner_axis, EuclideanSpace.proj,
    ]
  split_ifs <;> simp_all <;> ring

private lemma scalar_radial_pd {b : ℝ → ℝ} {u : R3 → ℝ} {x : R3} {j : Fin 3}
    (hx : 0 < ‖x‖) (hb : DifferentiableAt ℝ b ‖x‖)
    (he : u =ᶠ[𝓝 x] (fun y => b ‖y‖)) :
    pd j u x = deriv b ‖x‖ * (x j / ‖x‖) := by
  have h := hb.hasDerivAt.comp_hasFDerivAt x (norm_deriv hx)
  change HasFDerivAt (fun y : R3 => b ‖y‖) _ x at h
  rw [pd, he.fderiv_eq, h.fderiv]
  simp [inner_axis, div_eq_mul_inv, mul_comm, mul_left_comm]

private lemma scalar_repr {f : R3 → ℝ} (hs : IsSphSymm f) (x : R3) :
    f x = f (axis ‖x‖) := by
  let y := axis ‖x‖
  have hy : ‖y‖ = ‖x‖ := axis_norm (norm_nonneg x)
  let T := (Submodule.span ℝ {y - x})ᗮ.reflection
  have ht : T y = x := Submodule.reflection_sub hy
  simpa only [ht] using hs T y

private lemma axis_smooth : ContDiff ℝ ∞ axis := by
  have he : axis = fun r : ℝ => r • axis 1 := by
    ext r i
    simp [axis]
  rw [he]
  exact contDiff_id.smul contDiff_const

private lemma radial_hessian {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : IsSphSymm f) {r : ℝ} (hr : 0 < r) :
    ∀ i j : Fin 3, pd j (pd i f) (axis r) =
      if i = j then (if i = 0 then deriv (fun s => pd 0 f (axis s)) r
        else pd 0 f (axis r) / r) else 0 := by
  let U : ℝ → ℝ := fun s => pd 0 f (axis s)
  let b : ℝ → ℝ := fun s => U s / s
  have hU : Differentiable ℝ U :=
    ((smooth_pd hf 0).comp axis_smooth).differentiable (by simp)
  have hfirst : ∀ x : R3, 0 < ‖x‖ → ∀ i, pd i f x = b ‖x‖ * x i := by
    intro x hx i
    have h := scalar_radial_pd (j := i) hx (profile_deriv hf ‖x‖).differentiableAt
      (Filter.Eventually.of_forall (scalar_repr hs))
    rw [(profile_deriv hf ‖x‖).deriv] at h
    dsimp [b, U]
    rw [h]
    ring
  have hn := axis_norm hr.le
  have hev : ∀ᶠ y in 𝓝 (axis r), 0 < ‖y‖ :=
    continuous_norm.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by rwa [hn]))
  intro i j
  have hb : DifferentiableAt ℝ b r := (hU r).div differentiableAt_id (ne_of_gt hr)
  have he : pd i f =ᶠ[𝓝 (axis r)] (fun y => b ‖y‖ * y i) :=
    hev.mono (fun y hy => hfirst y hy i)
  have h := radial_pd (j := j) (i := i) (by rwa [hn]) (by simpa [hn] using hb) he
  fin_cases i <;> fin_cases j
  · exact (profile_deriv (smooth_pd hf 0) r).deriv.symm
  all_goals simpa [hn, axis, b, U] using h

private lemma radial_ode {Λ : ℝ} {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : IsSphSymm f)
    (heq : ∀ x, lap f x ^ 2 - hessNormSq f x = 2 * Λ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => s * (pd 0 f (axis s)) ^ 2) (Λ * r ^ 2) r := by
  have hh := radial_hessian hf hs hr
  have he := heq (axis r)
  simp only [lap, hessNormSq, Fin.sum_univ_three, hh] at he
  norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at he
  have hd := (hasDerivAt_id r).mul ((profile_deriv (smooth_pd hf 0) r).pow 2)
  simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul] at hd
  have hu := (profile_deriv (smooth_pd hf 0) r).deriv
  field_simp [ne_of_gt hr] at he
  convert! hd using 1
  rw [← hu]
  nlinarith only [he]

private lemma radial_square {Λ : ℝ} {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : IsSphSymm f) (heq : ∀ x, lap f x ^ 2 - hessNormSq f x = 2 * Λ) :
    ∀ r : ℝ, 0 < r → (pd 0 f (axis r)) ^ 2 = (Λ / 3) * r ^ 2 := by
  let H : ℝ → ℝ := fun r => r * (pd 0 f (axis r)) ^ 2 - (Λ / 3) * r ^ 3
  have hHd : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt H 0 r := by
    intro r hr
    have hd := (radial_ode hf hs heq hr).sub
      (((hasDerivAt_id r).pow 3).const_mul (Λ / 3))
    convert! hd using 1
    simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one]
    ring
  obtain ⟨k, hk⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero
    (convex_Ioi (0 : ℝ)).isPreconnected
    (fun r hr => (hHd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hHd r hr).deriv)
  have hHc : Continuous H := by
    exact (continuous_id.mul (((smooth_pd hf 0).comp axis_smooth).continuous.pow 2)).sub
      (continuous_const.mul (continuous_id.pow 3))
  have hz : H 0 = k := by
    apply (isClosed_eq hHc continuous_const).closure_subset_iff.mpr hk
    simp [closure_Ioi]
  have hk0 : k = 0 := by simpa [H] using hz.symm
  intro r hr
  have he := hk r hr
  dsimp [H] at he
  rw [hk0] at he
  have hm : r * ((pd 0 f (axis r)) ^ 2 - (Λ / 3) * r ^ 2) = 0 := by nlinarith only [he]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (ne_of_gt hr))

private lemma radial_positive {Λ : ℝ} (hΛ : 0 < Λ) {f : R3 → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : IsSphSymm f) (hconv : ∀ x, 0 < lap f x)
    (heq : ∀ x, lap f x ^ 2 - hessNormSq f x = 2 * Λ) :
    ∀ r : ℝ, 0 < r → pd 0 f (axis r) = Real.sqrt (Λ / 3) * r := by
  intro r hr
  let u := pd 0 f (axis r)
  let v := pd 0 (pd 0 f) (axis r)
  have hsquare := radial_square hf hs heq r hr
  have hode := radial_ode hf hs heq hr
  have hprod := ((hasDerivAt_id r).mul ((profile_deriv (smooth_pd hf 0) r).pow 2)).unique hode
  change 1 * u ^ 2 + r * ((2 : ℝ) * u ^ (2 - 1) * v) = Λ * r ^ 2 at hprod
  norm_num only [Nat.reduceSub, pow_one, one_mul] at hprod
  have hne : u ≠ 0 := by
    have hp : 0 < (Λ / 3) * r ^ 2 := mul_pos (by linarith) (sq_pos_of_pos hr)
    intro hz
    change u ^ 2 = _ at hsquare
    rw [hz] at hsquare
    nlinarith
  have hrel : r * v = u := by
    have hm : u * (r * v - u) = 0 := by
      change u ^ 2 = _ at hsquare
      nlinarith only [hsquare, hprod]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hne)
  have hlap : lap f (axis r) = v + 2 * (u / r) := by
    have hh := radial_hessian hf hs hr
    have hd := (profile_deriv (smooth_pd hf 0) r).deriv
    simp only [lap, Fin.sum_univ_three, hh]
    rw [hd]
    dsimp [u, v]
    ring
  have hup : 0 < u := by
    have hp := hconv (axis r)
    rw [hlap] at hp
    have hv : v = u / r := (eq_div_iff (ne_of_gt hr)).mpr (by nlinarith only [hrel])
    rw [hv] at hp
    exact (div_pos_iff.mp (by linarith : 0 < u / r)).resolve_right (fun h => (not_lt_of_ge hr.le) h.2) |>.1
  have hsq : (Real.sqrt (Λ / 3)) ^ 2 = Λ / 3 := Real.sq_sqrt (by linarith)
  have hspos := Real.sqrt_nonneg (Λ / 3)
  change u = _
  change u ^ 2 = _ at hsquare
  have he : u ^ 2 = (Real.sqrt (Λ / 3) * r) ^ 2 := by
    rw [mul_pow, hsq]
    exact hsquare
  exact (sq_eq_sq₀ hup.le (mul_nonneg hspos hr.le)).mp he

private lemma radial_classification {Λ : ℝ} (hΛ : 0 < Λ) {f : R3 → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : IsSphSymm f) (hconv : ∀ x, 0 < lap f x)
    (heq : ∀ x, lap f x ^ 2 - hessNormSq f x = 2 * Λ) :
    ∃ c : ℝ, ∀ x, f x = Real.sqrt (Λ / 12) * ‖x‖ ^ 2 + c := by
  let a := Real.sqrt (Λ / 12)
  have ha : Real.sqrt (Λ / 3) = 2 * a := by
    have h1 := Real.sq_sqrt (show 0 ≤ Λ / 3 by linarith)
    have h2 := Real.sq_sqrt (show 0 ≤ Λ / 12 by linarith)
    have h3 := Real.sqrt_nonneg (Λ / 3)
    have h4 := Real.sqrt_nonneg (Λ / 12)
    dsimp [a]
    nlinarith
  let H : ℝ → ℝ := fun r => f (axis r) - a * r ^ 2
  have hHd : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt H 0 r := by
    intro r hr
    have hd := (profile_deriv hf r).sub (((hasDerivAt_id r).pow 2).const_mul a)
    rw [radial_positive hΛ hf hs hconv heq r hr, ha] at hd
    convert! hd using 1
    simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring
  obtain ⟨c, hc⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero
    (convex_Ioi (0 : ℝ)).isPreconnected
    (fun r hr => (hHd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hHd r hr).deriv)
  have hHc : Continuous H := (hf.comp axis_smooth).continuous.sub
    (continuous_const.mul (continuous_id.pow 2))
  have hzero : H 0 = c := by
    apply (isClosed_eq hHc continuous_const).closure_subset_iff.mpr hc
    simp [closure_Ioi]
  refine ⟨c, fun x => ?_⟩
  rw [scalar_repr hs x]
  have hh : H ‖x‖ = c := by
    by_cases hx : ‖x‖ = 0
    · rwa [hx]
    · exact hc ‖x‖ (lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx))
  dsimp [H, a] at hh
  linarith
private lemma zero_of_ball_integrals {g : R3 → ℝ} (hg : Continuous g)
    (hpos : ∀ x, 0 ≤ g x)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ S : ℝ, R ≤ S →
      (∫ x in ball (0 : R3) S, g x) ≤ ε) : ∀ x, g x = 0 := by
  have hint (r : ℝ) : IntegrableOn g (ball (0 : R3) r) :=
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall (0 : R3) r)).mono_set
      ball_subset_closedBall
  have hle (r : ℝ) : (∫ x in ball (0 : R3) r, g x) ≤ 0 := by
    by_contra hn
    have hp : 0 < ∫ x in ball (0 : R3) r, g x := lt_of_not_ge hn
    obtain ⟨R, _, hR⟩ := hsmall ((∫ x in ball (0 : R3) r, g x) / 2) (by linarith)
    have hm : (∫ x in ball (0 : R3) r, g x) ≤
        ∫ x in ball (0 : R3) (max R r), g x :=
      setIntegral_mono_set (hint _) (ae_of_all _ hpos)
        (ae_of_all _ (ball_subset_ball (le_max_right R r)))
    have hb := hR (max R r) (le_max_left R r)
    linarith
  intro x
  let r := ‖x‖ + 1
  have hz : (∫ y in ball (0 : R3) r, g y) = 0 :=
    le_antisymm (hle r) (integral_nonneg hpos)
  have hae : g =ᵐ[(volume : Measure R3).restrict (ball 0 r)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hpos) (hint r)).mp hz
  exact Measure.eqOn_open_of_ae_eq hae isOpen_ball hg.continuousOn continuous_const.continuousOn
    (show x ∈ ball (0 : R3) r by simp [r, dist_zero_right])

private lemma defect_continuous {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (Λ : ℝ) :
    Continuous (fun x => lap u x ^ 2 - hessNormSq u x - 2 * Λ) := by
  have hl : ContDiff ℝ ∞ (lap u) :=
    ContDiff.sum (fun i _ => smooth_pd (smooth_pd hu i) i)
  have hh : ContDiff ℝ ∞ (hessNormSq u) :=
    ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => (smooth_pd (smooth_pd hu i) j).pow 2))
  exact ((hl.continuous.pow 2).sub hh.continuous).sub continuous_const

end ScalarVacuum

set_option backward.isDefEq.respectTransparency false in
open ScalarVacuum in
theorem solution (Λ : ℝ) (hΛ : 0 < Λ) (f : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (hconv : ∀ x, 0 < lap f x)
    (happrox : ApproxSphSymmAtInfty f)
    (heq : ∀ x, lap f x ^ 2 - hessNormSq f x = 2 * Λ) :
    ∃ c : ℝ, ∀ x, f x = Real.sqrt (Λ / 12) * ‖x‖ ^ 2 + c := by
  obtain ⟨hineq, hequiv⟩ := lemma1_symmetrization Λ hΛ f hf hconv happrox heq
  obtain ⟨hbar, hflux⟩ := symmetrization_flux_bound Λ f hf happrox heq
  have hz := zero_of_ball_integrals (defect_continuous hbar Λ)
    (fun x => sub_nonneg.mpr (hineq x)) hflux
  have hs : IsSphSymm f := hequiv.mp (fun x => sub_eq_zero.mp (hz x))
  exact radial_classification hΛ hf hs hconv heq
