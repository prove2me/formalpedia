-- Prove2me | solution 1 for Complex.integral_radial_loop_eq_two_pi_I_mul_sum_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/7f2c3a63-491b-534f-b9fe-1788bde54443

import Mathlib
import Theorems.Thm_Complex_integral_radial_loop_eq_two_mul_I_mul_setIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_integral_radial_loop_eq_two_pi_I_mul_sum_residue

namespace RadialResidue

open Complex MeasureTheory Set Filter intervalIntegral
open scoped Real Topology Interval

noncomputable def γ (c : ℂ) (r : ℝ → ℝ) (φ : ℝ) : ℂ := c + (r φ : ℂ) * exp (φ * I)

noncomputable def γ' (r : ℝ → ℝ) (φ : ℝ) : ℂ := (((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I)

theorem exp_mul_I_ne_zero (φ : ℝ) : exp (φ * I) ≠ 0 := exp_ne_zero _

theorem norm_exp_mul_I (φ : ℝ) : ‖exp (φ * I)‖ = 1 := norm_exp_ofReal_mul_I φ

theorem exp_mul_I_add_two_pi (φ : ℝ) : exp (((φ + 2 * π : ℝ) : ℂ) * I) = exp (φ * I) := by
  rw [ofReal_add, add_mul, exp_add]
  have : exp (((2 * π : ℝ) : ℂ) * I) = 1 := by
    rw [show ((2 * π : ℝ) : ℂ) * I = 2 * π * I by push_cast; ring]
    exact exp_two_pi_mul_I
  rw [this, mul_one]

theorem periodic_apply_arg {r : ℝ → ℝ} (hper : Function.Periodic r (2 * π)) {t : ℝ} (ht : 0 < t)
    (φ : ℝ) : r (arg ((t : ℂ) * exp (φ * I))) = r φ := by
  rw [arg_real_mul _ ht, arg_exp_mul_I, toIocMod]
  exact hper.sub_zsmul_eq _

section Loop

variable {c : ℂ} {r : ℝ → ℝ}
  (hcont : Continuous r) (hper : Function.Periodic r (2 * π)) (hpos : ∀ φ, 0 < r φ)

theorem γ_sub_c (φ : ℝ) : γ c r φ - c = (r φ : ℂ) * exp (φ * I) := by
  simp [γ]

include hpos in
theorem norm_γ_sub_c (φ : ℝ) : ‖γ c r φ - c‖ = r φ := by
  rw [γ_sub_c, norm_mul, norm_exp_mul_I, mul_one, Complex.norm_of_nonneg (hpos φ).le]

include hper hpos in
theorem r_arg_γ (φ : ℝ) : r (arg (γ c r φ - c)) = r φ := by
  rw [γ_sub_c]; exact periodic_apply_arg hper (hpos φ) φ

include hper hpos in

theorem γ_mem_K (φ : ℝ) : ‖γ c r φ - c‖ ≤ r (arg (γ c r φ - c)) := by
  rw [norm_γ_sub_c hpos, r_arg_γ hper hpos]

include hper hpos in

theorem γ_ne_segment {p : ℂ} (hp : ‖p - c‖ < r (arg (p - c))) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (φ : ℝ) : γ c r φ ≠ c + (t : ℂ) * (p - c) := by
  intro h
  have h1 : γ c r φ - c = (t : ℂ) * (p - c) := by rw [h]; ring
  rcases ht0.eq_or_lt with rfl | ht0'
  · rw [ofReal_zero, zero_mul, γ_sub_c] at h1
    exact (mul_ne_zero (ofReal_ne_zero.2 (hpos φ).ne') (exp_mul_I_ne_zero φ)) h1
  · have hn : r φ = t * ‖p - c‖ := by
      rw [← norm_γ_sub_c (c := c) hpos φ, h1, norm_mul, Complex.norm_of_nonneg ht0]
    have ha : r (arg (p - c)) = r φ := by
      rw [← r_arg_γ (c := c) hper hpos φ, h1, arg_real_mul _ ht0']
    have : t * ‖p - c‖ ≤ ‖p - c‖ := by
      calc t * ‖p - c‖ ≤ 1 * ‖p - c‖ := by gcongr
        _ = ‖p - c‖ := one_mul _
    linarith

include hper in
theorem γ_add_two_pi (φ : ℝ) : γ c r (φ + 2 * π) = γ c r φ := by
  simp only [γ, hper φ, exp_mul_I_add_two_pi]

include hcont in
theorem continuous_γ : Continuous (γ c r) := by
  unfold γ; fun_prop

theorem measurable_γ' (hcont : Continuous r) : Measurable (γ' r) := by
  unfold γ'
  exact ((measurable_ofReal.comp (measurable_deriv r)).add
    ((measurable_ofReal.comp hcont.measurable).mul measurable_const)).mul (by fun_prop)

noncomputable def rd (r : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (φ : ℝ) : ℝ :=
  derivWithin r (Icc a b) (projIcc a b hab φ : ℝ)

theorem continuous_rd {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) :
    Continuous (rd r a b hab.le) :=
  (hC.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)).comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) fun φ => (projIcc a b hab.le φ).2

theorem hasDerivAt_rd {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) {φ : ℝ}
    (hφ : φ ∈ Ioo a b) : HasDerivAt r (rd r a b hab.le φ) φ := by
  have hmem : φ ∈ Icc a b := ⟨hφ.1.le, hφ.2.le⟩
  have hd : DifferentiableAt ℝ r φ :=
    (hC.differentiableOn (by norm_num)).differentiableAt (Icc_mem_nhds hφ.1 hφ.2)
  have : rd r a b hab.le φ = deriv r φ := by
    rw [rd, projIcc_of_mem hab.le hmem]
    exact hd.derivWithin (uniqueDiffOn_Icc hab φ hmem)
  rw [this]
  exact hd.hasDerivAt

theorem deriv_eventuallyEq_rd {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) {φ : ℝ}
    (hφ : φ ∈ Ioo a b) : deriv r =ᶠ[𝓝 φ] rd r a b hab.le := by
  filter_upwards [Ioo_mem_nhds hφ.1 hφ.2] with ψ hψ
  exact (hasDerivAt_rd hab hC hψ).deriv

noncomputable def γd (r : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (φ : ℝ) : ℂ :=
  (((rd r a b hab φ : ℝ) : ℂ) + r φ * I) * exp (φ * I)

theorem γ'_eq_γd {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) {φ : ℝ}
    (hφ : φ ∈ Ioo a b) : γ' r φ = γd r a b hab.le φ := by
  rw [γ', γd, (hasDerivAt_rd hab hC hφ).deriv]

include hcont in
theorem continuous_γd {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) :
    Continuous (γd r a b hab.le) := by
  unfold γd
  have := continuous_rd hab hC
  fun_prop

include hcont in
theorem γ'_continuousAt {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) {φ : ℝ}
    (hφ : φ ∈ Ioo a b) : ContinuousAt (γ' r) φ := by
  refine ((continuous_γd hcont hab hC).continuousAt (x := φ)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hφ.1 hφ.2] with ψ hψ
  exact γ'_eq_γd hab hC hψ

theorem hasDerivAt_γ {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) {φ : ℝ}
    (hφ : φ ∈ Ioo a b) : HasDerivAt (γ c r) (γ' r φ) φ := by
  have hr : HasDerivAt (fun φ => (r φ : ℂ)) ((deriv r φ : ℝ) : ℂ) φ := by
    have := hasDerivAt_rd hab hC hφ
    rw [← this.deriv] at this
    exact this.ofReal_comp
  have he : HasDerivAt (fun φ : ℝ => exp (φ * I)) (exp (φ * I) * I) φ := by
    have h : HasDerivAt (fun x : ℝ => (x : ℂ) * I) (1 * I) φ :=
      (hasDerivAt_id φ).ofReal_comp.mul_const I
    have h__af := ((Complex.hasDerivAt_exp ((φ : ℂ) * I)).comp φ h)
    simp [one_mul] at h__af
    exact h__af
  have := (hr.mul he).const_add c
  refine this.congr_deriv ?_
  rw [γ']; ring

include hcont in

theorem intervalIntegrable_loop {h : ℂ → ℂ} (hh : ∀ φ, ContinuousAt h (γ c r φ))
    (N : ℕ) (φs : Fin (N + 1) → ℝ) (hφ0 : φs 0 = 0) (hφN : φs (Fin.last N) = 2 * π)
    (hmono : StrictMono φs)
    (hC2 : ∀ i : Fin N, ContDiffOn ℝ 2 r (Icc (φs i.castSucc) (φs i.succ))) :
    IntervalIntegrable (fun φ => h (γ c r φ) * γ' r φ) volume 0 (2 * π) := by
  have hhγ : Continuous fun φ => h (γ c r φ) :=
    continuous_iff_continuousAt.2 fun φ => (hh φ).comp (continuous_γ hcont).continuousAt
  set aN : ℕ → ℝ := fun k => if hk : k < N + 1 then φs ⟨k, hk⟩ else 2 * π with haN
  have haN0 : aN 0 = 0 := by
    have h0 : 0 < N + 1 := Nat.succ_pos N
    have : aN 0 = φs ⟨0, h0⟩ := by simp only [haN, dif_pos h0]
    rw [this, show (⟨0, h0⟩ : Fin (N + 1)) = 0 from rfl, hφ0]
  have haNN : aN N = 2 * π := by
    have hN : N < N + 1 := Nat.lt_succ_self N
    have : aN N = φs ⟨N, hN⟩ := by simp only [haN, dif_pos hN]
    rw [this, show (⟨N, hN⟩ : Fin (N + 1)) = Fin.last N from rfl, hφN]
  have hk1 : ∀ k (hk : k < N), aN k = φs (⟨k, hk⟩ : Fin N).castSucc := by
    intro k hk
    have h : k < N + 1 := by omega
    simp only [haN, dif_pos h]; rfl
  have hk2 : ∀ k (hk : k < N), aN (k + 1) = φs (⟨k, hk⟩ : Fin N).succ := by
    intro k hk
    have h : k + 1 < N + 1 := by omega
    simp only [haN, dif_pos h]; rfl
  rw [← haN0, ← haNN]
  refine IntervalIntegrable.trans_iterate fun k hk => ?_
  have hlt : aN k < aN (k + 1) := by
    rw [hk1 k hk, hk2 k hk]; exact hmono Fin.castSucc_lt_succ
  have hCk : ContDiffOn ℝ 2 r (Icc (aN k) (aN (k + 1))) := by
    rw [hk1 k hk, hk2 k hk]; exact hC2 _

  have hcts : Continuous fun φ => h (γ c r φ) * γd r (aN k) (aN (k + 1)) hlt.le φ :=
    hhγ.mul (continuous_γd hcont hlt hCk)
  rw [intervalIntegrable_iff]
  refine (intervalIntegrable_iff.1 (hcts.intervalIntegrable (aN k) (aN (k + 1)))).congr ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 ?_
  have hb : ∀ᵐ φ ∂(volume : Measure ℝ), φ ∉ ({aN (k + 1)} : Set ℝ) :=
    compl_mem_ae_iff.2 (measure_singleton _)
  filter_upwards [hb] with φ hφb hφI
  rw [uIoc_of_le hlt.le] at hφI
  rw [γ'_eq_γd hlt hCk ⟨hφI.1, lt_of_le_of_ne hφI.2 hφb⟩]

end Loop

section Winding

variable {c : ℂ} {r : ℝ → ℝ}
  (hcont : Continuous r) (hper : Function.Periodic r (2 * π)) (hpos : ∀ φ, 0 < r φ)
  (N : ℕ) (φs : Fin (N + 1) → ℝ) (hφ0 : φs 0 = 0) (hφN : φs (Fin.last N) = 2 * π)
  (hmono : StrictMono φs)
  (hC2 : ∀ i : Fin N, ContDiffOn ℝ 2 r (Icc (φs i.castSucc) (φs i.succ)))

noncomputable def wi (c : ℂ) (r : ℝ → ℝ) (q : ℂ) (φ : ℝ) : ℂ := γ' r φ / (γ c r φ - q)

theorem wi_eq (q : ℂ) (φ : ℝ) : wi c r q φ = (fun z => (z - q)⁻¹) (γ c r φ) * γ' r φ := by
  simp only [wi, div_eq_mul_inv, mul_comm]

include hcont hφ0 hφN hmono hC2 in
theorem intervalIntegrable_wi {q : ℂ} (hq : ∀ φ, γ c r φ ≠ q) :
    IntervalIntegrable (wi c r q) volume 0 (2 * π) := by
  have : wi c r q = fun φ => (fun z => (z - q)⁻¹) (γ c r φ) * γ' r φ := funext (wi_eq q)
  rw [this]
  refine intervalIntegrable_loop hcont (h := fun z => (z - q)⁻¹) (fun φ => ?_) N φs hφ0 hφN hmono hC2
  exact ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.2 (hq φ)))

include hcont hper hφ0 hφN hmono hC2 in

theorem exp_winding_eq_one {q : ℂ} (hq : ∀ φ, γ c r φ ≠ q) :
    exp (∫ φ in (0 : ℝ)..(2 * π), wi c r q φ) = 1 := by
  have hint := intervalIntegrable_wi hcont N φs hφ0 hφN hmono hC2 hq
  set Φ : ℝ → ℂ := fun x => ∫ φ in (0 : ℝ)..x, wi c r q φ with hΦ
  set E : ℝ → ℂ := fun x => exp (-Φ x) * (γ c r x - q) with hE
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity

  have hΦc : ContinuousOn Φ (Icc 0 (2 * π)) := by
    have hIO : IntegrableOn (wi c r q) (uIcc 0 (2 * π)) volume := by
      rw [uIcc_of_le h2π, integrableOn_Icc_iff_integrableOn_Ioc]
      exact hint.1
    have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) hIO
    rwa [uIcc_of_le h2π] at h
  have hEc : ContinuousOn E (Icc 0 (2 * π)) :=
    (hΦc.neg.cexp).mul ((continuous_γ hcont).continuousOn.sub continuousOn_const)

  set aN : ℕ → ℝ := fun k => if hk : k < N + 1 then φs ⟨k, hk⟩ else 2 * π with haN
  have haN0 : aN 0 = 0 := by
    have h0 : 0 < N + 1 := Nat.succ_pos N
    have : aN 0 = φs ⟨0, h0⟩ := by simp only [haN, dif_pos h0]
    rw [this, show (⟨0, h0⟩ : Fin (N + 1)) = 0 from rfl, hφ0]
  have haNN : aN N = 2 * π := by
    have hN : N < N + 1 := Nat.lt_succ_self N
    have : aN N = φs ⟨N, hN⟩ := by simp only [haN, dif_pos hN]
    rw [this, show (⟨N, hN⟩ : Fin (N + 1)) = Fin.last N from rfl, hφN]
  have hk1 : ∀ k (hk : k < N), aN k = φs (⟨k, hk⟩ : Fin N).castSucc := by
    intro k hk
    have h : k < N + 1 := by omega
    simp only [haN, dif_pos h]; rfl
  have hk2 : ∀ k (hk : k < N), aN (k + 1) = φs (⟨k, hk⟩ : Fin N).succ := by
    intro k hk
    have h : k + 1 < N + 1 := by omega
    simp only [haN, dif_pos h]; rfl
  have hmonoN : ∀ k, k ≤ N → aN k ∈ Icc 0 (2 * π) := by
    intro k hk
    have h : k < N + 1 := by omega
    have : aN k = φs ⟨k, h⟩ := by simp only [haN, dif_pos h]
    rw [this, ← hφ0, ← hφN]
    exact ⟨hmono.monotone (Fin.zero_le _), hmono.monotone (Fin.le_last _)⟩

  have hstep : ∀ k, k < N → E (aN (k + 1)) = E (aN k) := by
    intro k hk
    have hlt : aN k < aN (k + 1) := by
      rw [hk1 k hk, hk2 k hk]; exact hmono Fin.castSucc_lt_succ
    have hCk : ContDiffOn ℝ 2 r (Icc (aN k) (aN (k + 1))) := by
      rw [hk1 k hk, hk2 k hk]; exact hC2 _
    have hsub : Icc (aN k) (aN (k + 1)) ⊆ Icc 0 (2 * π) :=
      Icc_subset_Icc (hmonoN k hk.le).1 (hmonoN (k + 1) hk).2
    have hderiv : ∀ x ∈ Ioo (aN k) (aN (k + 1)), HasDerivAt E 0 x := by
      intro x hx
      have hx' : x ∈ Ioo 0 (2 * π) :=
        ⟨(hmonoN k hk.le).1.trans_lt hx.1, hx.2.trans_le (hmonoN (k + 1) hk).2⟩

      have hΦ' : HasDerivAt Φ (wi c r q x) x := by
        refine intervalIntegral.integral_hasDerivAt_right (hint.mono_set ?_) ?_ ?_
        · rw [uIcc_of_le h2π, uIcc_of_le hx'.1.le]; exact Icc_subset_Icc le_rfl hx'.2.le
        · exact ((measurable_γ' hcont).div ((continuous_γ hcont).measurable.sub
            measurable_const)).stronglyMeasurable.stronglyMeasurableAtFilter
        · exact (γ'_continuousAt hcont hlt hCk hx).div
            ((continuous_γ hcont).continuousAt.sub continuousAt_const) (sub_ne_zero.2 (hq x))
      have hγ := hasDerivAt_γ (c := c) hlt hCk hx
      have := ((hΦ'.neg.cexp).mul (hγ.sub_const q))
      refine this.congr_deriv ?_
      have hne : γ c r x - q ≠ 0 := sub_ne_zero.2 (hq x)
      rw [wi]
      field_simp
      ring
    have hftc := integral_eq_sub_of_hasDerivAt_of_le hlt.le (hEc.mono hsub) hderiv
      (_root_.intervalIntegrable_const (c := (0 : ℂ)))
    simp only [intervalIntegral.integral_zero] at hftc
    exact (sub_eq_zero.1 hftc.symm)
  have hchain : ∀ k, k ≤ N → E (aN k) = E (aN 0) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih => rw [hstep k (by omega), ih (by omega)]
  have hEN := hchain N le_rfl
  rw [haNN, haN0] at hEN

  have hΦ0 : Φ 0 = 0 := by simp [hΦ]
  have hγ2π : γ c r (2 * π) = γ c r 0 := by
    have := γ_add_two_pi (c := c) hper 0
    rwa [zero_add] at this
  simp only [hE, hΦ0, neg_zero, exp_zero, one_mul, hγ2π] at hEN
  have hne : γ c r 0 - q ≠ 0 := sub_ne_zero.2 (hq 0)
  have hexp : exp (-Φ (2 * π)) = 1 := by
    have := mul_right_cancel₀ hne (hEN.trans (one_mul _).symm)
    exact this
  rw [exp_neg, inv_eq_one] at hexp
  exact hexp

include hcont hper hpos hφ0 hφN hmono hC2 in

theorem continuous_winding_segment {p : ℂ} (hp : ‖p - c‖ < r (arg (p - c))) :
    Continuous fun t : Icc (0 : ℝ) 1 =>
      ∫ φ in (0 : ℝ)..(2 * π), wi c r (c + ((t : ℝ) : ℂ) * (p - c)) φ := by

  have hcomp : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (2 * π)) := isCompact_Icc.prod isCompact_Icc
  have hdc : Continuous fun z : ℝ × ℝ => ‖γ c r z.2 - (c + ((z.1 : ℝ) : ℂ) * (p - c))‖ := by
    have := continuous_γ (c := c) hcont
    fun_prop
  obtain ⟨z₀, hz₀, hmin⟩ := hcomp.exists_isMinOn (s := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (2 * π))
    ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, by positivity⟩⟩⟩ hdc.continuousOn
  set δ := ‖γ c r z₀.2 - (c + ((z₀.1 : ℝ) : ℂ) * (p - c))‖ with hδ
  have hδ0 : 0 < δ := norm_pos_iff.2 (sub_ne_zero.2
    (γ_ne_segment hper hpos hp (mem_prod.1 hz₀).1.1 (mem_prod.1 hz₀).1.2 _))
  have hlow : ∀ t ∈ Icc (0 : ℝ) 1, ∀ φ ∈ Icc (0 : ℝ) (2 * π),
      δ ≤ ‖γ c r φ - (c + ((t : ℝ) : ℂ) * (p - c))‖ :=
    fun t ht φ hφ => hmin (show (t, φ) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (2 * π) from ⟨ht, hφ⟩)
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hγ'int : IntervalIntegrable (γ' r) volume 0 (2 * π) := by
    have := intervalIntegrable_loop (c := c) hcont (h := fun _ => (1 : ℂ))
      (fun φ => continuousAt_const) N φs hφ0 hφN hmono hC2
    simpa using this
  refine intervalIntegral.continuous_of_dominated_interval
    (F := fun (t : Icc (0 : ℝ) 1) φ => wi c r (c + ((t : ℝ) : ℂ) * (p - c)) φ)
    (bound := fun φ => ‖γ' r φ‖ / δ) (fun t => ?_) (fun t => ?_) ?_ ?_
  · exact ((measurable_γ' hcont).div ((continuous_γ hcont).measurable.sub
      measurable_const)).aestronglyMeasurable
  · refine Eventually.of_forall fun φ hφ => ?_
    rw [uIoc_of_le h2π] at hφ
    simp only [wi, norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hδ0 (hlow t t.2 φ ⟨hφ.1.le, hφ.2⟩)
  · exact hγ'int.norm.div_const δ
  · refine Eventually.of_forall fun φ _ => ?_
    have hne : ∀ t : Icc (0 : ℝ) 1, γ c r φ - (c + ((t : ℝ) : ℂ) * (p - c)) ≠ 0 := fun t =>
      sub_ne_zero.2 (γ_ne_segment hper hpos hp t.2.1 t.2.2 φ)
    simp only [wi]
    exact continuous_const.div (by fun_prop) hne

include hcont hper hpos hφ0 hφN hmono hC2 in

theorem winding_centre : (∫ φ in (0 : ℝ)..(2 * π), wi c r c φ) = 2 * π * I := by

  have hwi : ∀ φ, wi c r c φ = ((deriv r φ / r φ : ℝ) : ℂ) + I := by
    intro φ
    have hr : (r φ : ℂ) ≠ 0 := ofReal_ne_zero.2 (hpos φ).ne'
    rw [wi, γ', γ, add_sub_cancel_left]
    push_cast
    field_simp
  simp_rw [hwi]
  set aN : ℕ → ℝ := fun k => if hk : k < N + 1 then φs ⟨k, hk⟩ else 2 * π with haN
  have haN0 : aN 0 = 0 := by
    have h0 : 0 < N + 1 := Nat.succ_pos N
    have : aN 0 = φs ⟨0, h0⟩ := by simp only [haN, dif_pos h0]
    rw [this, show (⟨0, h0⟩ : Fin (N + 1)) = 0 from rfl, hφ0]
  have haNN : aN N = 2 * π := by
    have hN : N < N + 1 := Nat.lt_succ_self N
    have : aN N = φs ⟨N, hN⟩ := by simp only [haN, dif_pos hN]
    rw [this, show (⟨N, hN⟩ : Fin (N + 1)) = Fin.last N from rfl, hφN]
  have hk1 : ∀ k (hk : k < N), aN k = φs (⟨k, hk⟩ : Fin N).castSucc := by
    intro k hk
    have h : k < N + 1 := by omega
    simp only [haN, dif_pos h]; rfl
  have hk2 : ∀ k (hk : k < N), aN (k + 1) = φs (⟨k, hk⟩ : Fin N).succ := by
    intro k hk
    have h : k + 1 < N + 1 := by omega
    simp only [haN, dif_pos h]; rfl

  have harc : ∀ k, k < N →
      (∫ φ in aN k..aN (k + 1), (((deriv r φ / r φ : ℝ) : ℂ) + I)) =
        (((Real.log (r (aN (k + 1))) - Real.log (r (aN k)) : ℝ) : ℂ) +
          (((aN (k + 1) - aN k : ℝ) : ℂ)) * I) ∧
      IntervalIntegrable (fun φ => ((deriv r φ / r φ : ℝ) : ℂ) + I) volume (aN k) (aN (k + 1)) := by
    intro k hk
    have hlt : aN k < aN (k + 1) := by
      rw [hk1 k hk, hk2 k hk]; exact hmono Fin.castSucc_lt_succ
    have hCk : ContDiffOn ℝ 2 r (Icc (aN k) (aN (k + 1))) := by
      rw [hk1 k hk, hk2 k hk]; exact hC2 _
    set a := aN k
    set b := aN (k + 1)

    have hq : Continuous fun φ => rd r a b hlt.le φ / r φ :=
      (continuous_rd hlt hCk).div hcont fun φ => (hpos φ).ne'
    have hqc' : Continuous fun φ => ((rd r a b hlt.le φ / r φ : ℝ) : ℂ) :=
      continuous_ofReal.comp hq
    have hqc : Continuous fun φ => ((rd r a b hlt.le φ / r φ : ℝ) : ℂ) + I := by fun_prop
    have hae : ∀ᵐ φ ∂(volume : Measure ℝ), φ ∈ Ι a b →
        (((deriv r φ / r φ : ℝ) : ℂ) + I) = ((rd r a b hlt.le φ / r φ : ℝ) : ℂ) + I := by
      have hb : ∀ᵐ φ ∂(volume : Measure ℝ), φ ∉ ({b} : Set ℝ) :=
        compl_mem_ae_iff.2 (measure_singleton _)
      filter_upwards [hb] with φ hφb hφI
      rw [uIoc_of_le hlt.le] at hφI
      rw [(hasDerivAt_rd hlt hCk ⟨hφI.1, lt_of_le_of_ne hφI.2 hφb⟩).deriv]
    refine ⟨?_, ?_⟩
    · rw [intervalIntegral.integral_congr_ae hae,
        intervalIntegral.integral_add (hqc'.intervalIntegrable _ _)
          _root_.intervalIntegrable_const,
        intervalIntegral.integral_const, intervalIntegral.integral_ofReal]
      have hlog : (∫ φ in a..b, rd r a b hlt.le φ / r φ) = Real.log (r b) - Real.log (r a) := by
        refine integral_eq_sub_of_hasDerivAt_of_le (f := fun φ => Real.log (r φ)) hlt.le
          ((Real.continuousOn_log.comp hcont.continuousOn fun φ _ => (hpos φ).ne'))
          (fun φ hφ => ?_) (hq.intervalIntegrable _ _)
        have := (Real.hasDerivAt_log (hpos φ).ne').comp φ (hasDerivAt_rd hlt hCk hφ)
        refine this.congr_deriv ?_
        rw [div_eq_inv_mul]
      rw [hlog, real_smul]
    · rw [intervalIntegrable_iff]
      refine (intervalIntegrable_iff.1 (hqc.intervalIntegrable a b)).congr ?_
      exact (ae_restrict_iff' measurableSet_uIoc).2 (hae.mono fun φ hφ hφI => (hφ hφI).symm)
  have key : (∫ φ in aN 0..aN N, (((deriv r φ / r φ : ℝ) : ℂ) + I)) = 2 * π * I := by
    rw [← sum_integral_adjacent_intervals (a := aN) (n := N) fun k hk => (harc k hk).2,
      Finset.sum_congr rfl fun k hk => (harc k (Finset.mem_range.1 hk)).1,
      Finset.sum_add_distrib, ← Finset.sum_mul]
    have h1 : ∑ k ∈ Finset.range N,
        (((Real.log (r (aN (k + 1))) - Real.log (r (aN k)) : ℝ) : ℂ)) = 0 := by
      have htel : ∑ k ∈ Finset.range N, (Real.log (r (aN (k + 1))) - Real.log (r (aN k))) =
          Real.log (r (aN N)) - Real.log (r (aN 0)) :=
        Finset.sum_range_sub (fun k => Real.log (r (aN k))) N
      rw [← ofReal_sum, htel, haNN, haN0]
      have : r (2 * π) = r 0 := by have := hper 0; rwa [zero_add] at this
      rw [this, sub_self, ofReal_zero]
    have h2 : ∑ k ∈ Finset.range N, (((aN (k + 1) - aN k : ℝ) : ℂ)) = 2 * π := by
      have htel : ∑ k ∈ Finset.range N, (aN (k + 1) - aN k) = aN N - aN 0 :=
        Finset.sum_range_sub (fun k => aN k) N
      rw [← ofReal_sum, htel, haNN, haN0]
      push_cast; ring
    rw [h1, h2, zero_add]
  rw [haN0, haNN] at key
  exact key

include hcont hper hpos hφ0 hφN hmono hC2 in

theorem winding_eq {p : ℂ} (hp : ‖p - c‖ < r (arg (p - c))) :
    (∫ φ in (0 : ℝ)..(2 * π), wi c r p φ) = 2 * π * I := by
  set W : Icc (0 : ℝ) 1 → ℂ := fun t =>
    ∫ φ in (0 : ℝ)..(2 * π), wi c r (c + ((t : ℝ) : ℂ) * (p - c)) φ with hW
  have hWc : Continuous W := continuous_winding_segment hcont hper hpos N φs hφ0 hφN hmono hC2 hp
  have hoff : ∀ t : Icc (0 : ℝ) 1, ∀ φ, γ c r φ ≠ c + ((t : ℝ) : ℂ) * (p - c) := fun t φ =>
    γ_ne_segment hper hpos hp t.2.1 t.2.2 φ
  have hex : ∀ t : Icc (0 : ℝ) 1, ∃ n : ℤ, W t = n * (2 * π * I) := fun t =>
    exp_eq_one_iff.1 (exp_winding_eq_one hcont hper N φs hφ0 hφN hmono hC2 (hoff t))
  choose n hn using hex

  have hnc : Continuous n := by
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    have hev : ∀ᶠ t in 𝓝 t₀, dist (W t) (W t₀) < 2 * π :=
      (Metric.tendsto_nhds.1 hWc.continuousAt) (2 * π) (by positivity)
    have hev' : ∀ᶠ t in 𝓝 t₀, n t = n t₀ := by
      filter_upwards [hev] with t ht
      have h2 : ‖(2 * π * I : ℂ)‖ = 2 * π := by
        rw [show (2 * π * I : ℂ) = ((2 * π : ℝ) : ℂ) * I by push_cast; ring, norm_mul, norm_I,
          mul_one, Complex.norm_of_nonneg (by positivity)]
      have hdiff : (((n t - n t₀ : ℤ) : ℝ) : ℂ) * (2 * π * I) = W t - W t₀ := by
        rw [hn t, hn t₀]; push_cast; ring
      have hlt : ‖(((n t - n t₀ : ℤ) : ℝ) : ℂ)‖ * (2 * π) < 2 * π := by
        have h' : ‖(((n t - n t₀ : ℤ) : ℝ) : ℂ) * (2 * π * I)‖ < 2 * π := by
          rw [hdiff, ← dist_eq_norm]; exact ht
        rwa [norm_mul, h2] at h'
      have h1 : ‖(((n t - n t₀ : ℤ) : ℝ) : ℂ)‖ < 1 :=
        (mul_lt_iff_lt_one_left (by positivity)).1 hlt
      rw [Complex.norm_real, Real.norm_eq_abs] at h1
      have h4 : |(n t - n t₀ : ℤ)| < 1 := by exact_mod_cast h1
      have := Int.abs_lt_one_iff.1 h4
      omega
    exact continuousAt_const.congr_of_eventuallyEq hev'
  haveI : PreconnectedSpace (Icc (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
  have hconst := IsPreconnected.constant isPreconnected_univ hnc.continuousOn
    (x := ⟨1, zero_le_one, le_rfl⟩) (y := ⟨0, le_rfl, zero_le_one⟩) (mem_univ _) (mem_univ _)
  have h1 : W ⟨1, zero_le_one, le_rfl⟩ = W ⟨0, le_rfl, zero_le_one⟩ := by
    rw [hn, hn, hconst]
  have hW1 : W ⟨1, zero_le_one, le_rfl⟩ = ∫ φ in (0 : ℝ)..(2 * π), wi c r p φ := by
    simp [hW]
  have hW0 : W ⟨0, le_rfl, zero_le_one⟩ = ∫ φ in (0 : ℝ)..(2 * π), wi c r c φ := by
    simp [hW]
  rw [← hW1, h1, hW0]
  exact winding_centre hcont hper hpos N φs hφ0 hφN hmono hC2

end Winding

section Principal

variable {c : ℂ} {r : ℝ → ℝ} (f : ℂ → ℂ) (P : Finset ℂ) (res : ℂ → ℂ)

noncomputable def R (z : ℂ) : ℂ := ∑ p ∈ P, res p / (z - p)

open Classical in

noncomputable def Ft (z : ℂ) : ℂ :=
  if z ∈ P then limUnder (𝓝[≠] z) (fun w => f w - R P res w) else f z - R P res z

theorem eventually_notMem (P : Finset ℂ) {z : ℂ} (hz : z ∉ P) : ∀ᶠ w in 𝓝 z, w ∉ P := by
  have : ∀ᶠ w in 𝓝 z, ∀ p ∈ P, w ≠ p := by
    rw [eventually_all_finset]
    intro p hp
    exact isOpen_ne.mem_nhds fun h => hz (h ▸ hp)
  exact this.mono fun w hw hwP => hw w hwP rfl

theorem eventually_notMem_punctured (P : Finset ℂ) (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, w ∉ P := by
  have h1 : ∀ᶠ w in 𝓝[≠] z, w ∉ P.erase z :=
    (eventually_notMem (P.erase z) (P.notMem_erase z)).filter_mono nhdsWithin_le_nhds
  have h2 : ∀ᶠ w in 𝓝[≠] z, w ≠ z := eventually_nhdsWithin_of_forall fun w hw => hw
  filter_upwards [h1, h2] with w hw1 hw2 hwP
  exact hw1 (Finset.mem_erase.2 ⟨hw2, hwP⟩)

theorem analyticAt_R {z : ℂ} (hz : ∀ p ∈ P, z ≠ p) : AnalyticAt ℂ (R P res) z := by
  unfold R
  refine Finset.analyticAt_fun_sum P fun p hp => ?_
  exact analyticAt_const.fun_div (analyticAt_id.fun_sub analyticAt_const) (sub_ne_zero.2 (hz p hp))

theorem analyticAt_Ft_of_notMem {z : ℂ} (hz : z ∉ P) (hf : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (Ft f P res) z := by
  have hR : AnalyticAt ℂ (R P res) z := analyticAt_R P res fun p hp h => hz (h ▸ hp)
  refine (hf.sub hR).congr ?_
  filter_upwards [eventually_notMem P hz] with w hw
  simp only [Ft, if_neg hw, Pi.sub_apply]

theorem analyticAt_Ft_of_mem {p : ℂ} (hp : p ∈ P) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g p)
    (hloc : ∀ᶠ z in 𝓝[≠] p, f z = res p / (z - p) + g z) : AnalyticAt ℂ (Ft f P res) p := by

  set R' : ℂ → ℂ := fun z => ∑ q ∈ P.erase p, res q / (z - q) with hR'
  have hR'an : AnalyticAt ℂ R' p := by
    refine Finset.analyticAt_fun_sum _ fun q hq => ?_
    exact analyticAt_const.fun_div (analyticAt_id.fun_sub analyticAt_const)
      (sub_ne_zero.2 (Finset.ne_of_mem_erase hq).symm)
  have hsplit : ∀ z, R P res z = res p / (z - p) + R' z := by
    intro z
    simp only [R, hR']
    rw [← Finset.add_sum_erase P _ hp]
  set h : ℂ → ℂ := fun z => g z - R' z with hh
  have hhan : AnalyticAt ℂ h p := hg.sub hR'an
  have hev : ∀ᶠ z in 𝓝[≠] p, f z - R P res z = h z := by
    filter_upwards [hloc] with z hz
    rw [hz, hsplit]; ring

  have hlim : limUnder (𝓝[≠] p) (fun w => f w - R P res w) = h p := by
    rw [show limUnder (𝓝[≠] p) (fun w => f w - R P res w) = limUnder (𝓝[≠] p) h from
      congrArg lim (Filter.map_congr hev)]
    exact (hhan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
  have hFp : Ft f P res p = h p := by simp only [Ft, if_pos hp, hlim]

  have hev' : ∀ᶠ z in 𝓝[≠] p, Ft f P res z = h z := by
    filter_upwards [hev, eventually_notMem_punctured P p] with z hz hzP
    simp only [Ft, if_neg hzP, hz]
  refine hhan.congr ?_
  rw [eventuallyEq_iff_exists_mem]
  obtain ⟨s, hs, hsub⟩ := hev'.exists_mem
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hs
  obtain ⟨t, ht, hts⟩ := hs
  refine ⟨t, ht, fun z hz => ?_⟩
  by_cases hzp : z = p
  · rw [hzp, hFp]
  · exact (hsub z (hts ⟨hz, hzp⟩)).symm

theorem Ft_of_notMem {z : ℂ} (hz : z ∉ P) : Ft f P res z = f z - R P res z := by
  simp only [Ft, if_neg hz]

end Principal

end RadialResidue

open RadialResidue Complex MeasureTheory Set Filter in
theorem solution
    (c : ℂ) (r : ℝ → ℝ) (hcont : Continuous r) (hper : Function.Periodic r (2 * Real.pi))
    (hpos : ∀ φ, 0 < r φ)
    (N : ℕ) (φs : Fin (N + 1) → ℝ) (hφ0 : φs 0 = 0) (hφN : φs (Fin.last N) = 2 * Real.pi)
    (hmono : StrictMono φs)
    (hC2 : ∀ i : Fin N, ContDiffOn ℝ 2 r (Set.Icc (φs i.castSucc) (φs i.succ)))
    (f : ℂ → ℂ) (P : Finset ℂ) (res : ℂ → ℂ)
    (hint : ∀ p ∈ P, ‖p - c‖ < r (arg (p - c)))
    (han : ∀ z : ℂ, ‖z - c‖ ≤ r (arg (z - c)) → z ∉ P → AnalyticAt ℂ f z)
    (hpole : ∀ p ∈ P, ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
      ∀ᶠ z in nhdsWithin p {p}ᶜ, f z = res p / (z - p) + g z) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
        f (c + r φ * exp (φ * I)) * ((((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I)) =
      2 * Real.pi * I * ∑ p ∈ P, res p := by

  have hFan : ∀ z : ℂ, ‖z - c‖ ≤ r (arg (z - c)) → AnalyticAt ℂ (Ft f P res) z := by
    intro z hz
    by_cases hzP : z ∈ P
    · obtain ⟨g, hg, hloc⟩ := hpole z hzP
      exact analyticAt_Ft_of_mem f P res hzP hg hloc
    · exact analyticAt_Ft_of_notMem f P res hzP (han z hz hzP)
  set F : ℂ → ℂ := Ft f P res with hF
  have hUo : IsOpen {z : ℂ | AnalyticAt ℂ F z} := isOpen_analyticAt ℂ F
  have hKU : ∀ z : ℂ, ‖z - c‖ ≤ r (arg (z - c)) → z ∈ {z : ℂ | AnalyticAt ℂ F z} :=
    fun z hz => hFan z hz
  have hAn : AnalyticOnNhd ℂ F {z : ℂ | AnalyticAt ℂ F z} := fun z hz => hz
  have hFC1 : ContDiffOn ℝ 1 F {z : ℂ | AnalyticAt ℂ F z} :=
    (hAn.contDiffOn_of_completeSpace (n := 1)).restrict_scalars ℝ

  have hG := Complex.integral_radial_loop_eq_two_mul_I_mul_setIntegral c r hcont hper hpos N φs
    hφ0 hφN hmono hC2 F (fun _ => 0) {z : ℂ | AnalyticAt ℂ F z} hUo hKU hFC1 contDiffOn_const
  have hRHS : (∫ z in {z : ℂ | ‖z - c‖ ≤ r (arg (z - c))},
      ((fderiv ℝ F z 1 + I * fderiv ℝ F z I) / 2 -
        (fderiv ℝ (fun _ : ℂ => (0 : ℂ)) z 1 - I * fderiv ℝ (fun _ : ℂ => (0 : ℂ)) z I) / 2)) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
    have hd : DifferentiableAt ℂ F z := (hFan z hz).differentiableAt
    rw [hd.fderiv_restrictScalars ℝ]
    simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, sub_zero, mul_zero, zero_div,
      ContinuousLinearMap.coe_restrictScalars']
    have : fderiv ℂ F z I = I * fderiv ℂ F z 1 := by
      rw [show (I : ℂ) = I • (1 : ℂ) by simp, map_smul, smul_eq_mul]; simp
    rw [this, ← mul_assoc, I_mul_I]
    ring
  rw [hRHS, mul_zero] at hG
  simp only [zero_mul, add_zero] at hG

  have hloop : ∀ φ, c + (r φ : ℂ) * exp (φ * I) ∉ P := by
    intro φ hφP
    have h1 := hint _ hφP
    rw [show c + (r φ : ℂ) * exp (φ * I) = γ c r φ from rfl, norm_γ_sub_c hpos,
      r_arg_γ hper hpos] at h1
    exact lt_irrefl _ h1
  have hdecomp : ∀ φ, f (c + (r φ : ℂ) * exp (φ * I)) * ((((deriv r φ : ℝ) : ℂ) + r φ * I) *
      exp (φ * I)) = F (γ c r φ) * γ' r φ + ∑ p ∈ P, res p * wi c r p φ := by
    intro φ
    have hF' : F (γ c r φ) = f (γ c r φ) - R P res (γ c r φ) := Ft_of_notMem f P res (hloop φ)
    have hsum : ∑ p ∈ P, res p * wi c r p φ = R P res (γ c r φ) * γ' r φ := by
      simp only [wi, R, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    rw [hsum, hF', sub_mul, sub_add_cancel]
    rfl
  simp_rw [hdecomp]

  have hFint : IntervalIntegrable (fun φ => F (γ c r φ) * γ' r φ) volume 0 (2 * Real.pi) :=
    intervalIntegrable_loop hcont (fun φ => (hFan _ (γ_mem_K hper hpos φ)).continuousAt)
      N φs hφ0 hφN hmono hC2
  have hpoles : ∀ p ∈ P, ∀ φ, γ c r φ ≠ p := fun p hp φ h => hloop φ (by rw [γ] at h; exact h ▸ hp)
  have hWint : ∀ p ∈ P, IntervalIntegrable (fun φ => res p * wi c r p φ) volume 0 (2 * Real.pi) :=
    fun p hp => (intervalIntegrable_wi hcont N φs hφ0 hφN hmono hC2 (hpoles p hp)).const_mul _
  have hWint' : IntervalIntegrable (fun φ => ∑ p ∈ P, res p * wi c r p φ) volume 0 (2 * Real.pi) := by
    have h := IntervalIntegrable.sum P hWint
    have : (∑ p ∈ P, fun φ => res p * wi c r p φ) = fun φ => ∑ p ∈ P, res p * wi c r p φ := by
      ext φ; simp only [Finset.sum_apply]
    rwa [this] at h
  have hG' : (∫ φ in (0 : ℝ)..(2 * Real.pi), F (γ c r φ) * γ' r φ) = 0 := hG
  rw [intervalIntegral.integral_add hFint hWint', hG', zero_add,
    intervalIntegral.integral_finsetSum hWint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [intervalIntegral.integral_const_mul,
    winding_eq hcont hper hpos N φs hφ0 hφN hmono hC2 (hint p hp)]
  ring

end S_Complex_integral_radial_loop_eq_two_pi_I_mul_sum_residue
end P2MW
export P2MW.S_Complex_integral_radial_loop_eq_two_pi_I_mul_sum_residue (solution)
