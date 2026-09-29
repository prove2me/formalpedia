-- Prove2me | solution 1 for Complex.exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/49ee3d00-9a01-57d7-a5f1-67c146f67202

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Complex.PhragmenLindelof
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im

set_option autoImplicit false

namespace GammaVerticalStrips

open Set Filter

private theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs, Complex.GammaIntegral]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx' : (0 : ℝ) < x := hx
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos hx', Complex.sub_re, Complex.one_re]

private theorem exists_bound_Gamma_re :
    ∃ M : ℝ, ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 2 → Real.Gamma σ ≤ M := by
  refine ⟨max (Real.Gamma (1 / 2)) (Real.Gamma (3 / 2)), fun σ h1 h2 => ?_⟩
  have hmem : σ ∈ segment ℝ (1 / 2 : ℝ) (3 / 2) := by
    rw [segment_eq_Icc (by norm_num)]
    exact ⟨h1, h2⟩
  exact Real.convexOn_Gamma.le_on_segment (by norm_num : (1 / 2 : ℝ) ∈ Ioi 0)
    (by norm_num : (3 / 2 : ℝ) ∈ Ioi 0) hmem

private theorem exp_abs_le_two_mul_cosh (x : ℝ) : Real.exp |x| ≤ 2 * Real.cosh x := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have := Real.exp_pos (-|x|)
  linarith

private theorem norm_Gamma_le_of_re_eq_half {w : ℂ} (hw : w.re = 1 / 2) :
    ‖Complex.Gamma w‖ ≤ (1 + 2 * Real.pi) * Real.exp (-(Real.pi / 2) * |w.im|) := by
  set t : ℝ := w.im with ht

  have hconj : (1 : ℂ) - w = (starRingEnd ℂ) w := by
    apply Complex.ext <;> simp [hw]
    norm_num
  have hrefl := Complex.Gamma_mul_Gamma_one_sub w
  rw [hconj, Complex.Gamma_conj] at hrefl

  have hpw : (Real.pi : ℂ) * w = ((Real.pi * t : ℝ) : ℂ) * Complex.I + (Real.pi : ℂ) / 2 := by
    apply Complex.ext <;> simp [hw, ht]
    ring
  have hsin : ‖Complex.sin ((Real.pi : ℂ) * w)‖ = Real.cosh (Real.pi * t) := by
    rw [hpw, Complex.sin_add_pi_div_two, Complex.cos_mul_I, ← Complex.ofReal_cosh, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
  have hsq : ‖Complex.Gamma w‖ * ‖Complex.Gamma w‖ * Real.cosh (Real.pi * t) = Real.pi := by
    have h := congrArg norm hrefl
    rw [norm_mul, Complex.norm_conj, norm_div, hsin, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos] at h
    rw [h]
    field_simp [(Real.cosh_pos _).ne']

  set g : ℝ := ‖Complex.Gamma w‖ with hg
  set e : ℝ := Real.exp (-(Real.pi / 2) * |t|) with he
  have hg0 : 0 ≤ g := norm_nonneg _
  have he0 : 0 < e := Real.exp_pos _
  have hee : e * e * Real.exp |Real.pi * t| = 1 := by
    rw [he, ← Real.exp_add, ← Real.exp_add, abs_mul, abs_of_pos Real.pi_pos]
    convert Real.exp_zero using 2
    ring
  have hcosh := exp_abs_le_two_mul_cosh (Real.pi * t)

  have h1 : g * g * Real.exp |Real.pi * t| ≤ 2 * Real.pi := by
    nlinarith [mul_nonneg (mul_nonneg hg0 hg0) (by positivity : (0 : ℝ) ≤ 1), hsq, hcosh,
      mul_nonneg hg0 hg0]
  have h2 : g * g ≤ 2 * Real.pi * (e * e) := by
    have hE : 0 < Real.exp |Real.pi * t| := Real.exp_pos _
    have : g * g = g * g * Real.exp |Real.pi * t| * (e * e) := by
      calc g * g = g * g * (e * e * Real.exp |Real.pi * t|) := by rw [hee, mul_one]
        _ = g * g * Real.exp |Real.pi * t| * (e * e) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)

  nlinarith [h2, Real.pi_pos, he0, hg0, mul_pos he0 he0, sq_nonneg (g - (1 + 2 * Real.pi) * e),
    mul_nonneg hg0 he0.le]

private theorem norm_Gamma_le_of_re_eq_half_or {w : ℂ} (hw : w.re = 1 / 2 ∨ w.re = 3 / 2) :
    ‖Complex.Gamma w‖ ≤ (1 + 2 * Real.pi) * (‖w‖ + 1) * Real.exp (-(Real.pi / 2) * |w.im|) := by
  have hK : (0 : ℝ) ≤ 1 + 2 * Real.pi := by positivity
  have he : (0 : ℝ) < Real.exp (-(Real.pi / 2) * |w.im|) := Real.exp_pos _
  rcases hw with hw | hw
  · have h := norm_Gamma_le_of_re_eq_half hw
    calc ‖Complex.Gamma w‖ ≤ (1 + 2 * Real.pi) * Real.exp (-(Real.pi / 2) * |w.im|) := h
      _ = (1 + 2 * Real.pi) * 1 * Real.exp (-(Real.pi / 2) * |w.im|) := by ring
      _ ≤ (1 + 2 * Real.pi) * (‖w‖ + 1) * Real.exp (-(Real.pi / 2) * |w.im|) := by
        gcongr
        linarith [norm_nonneg w]
  · have hw1 : w - 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp [hw] at this
      norm_num at this
    have hrec : Complex.Gamma w = (w - 1) * Complex.Gamma (w - 1) := by
      have := Complex.Gamma_add_one (w - 1) hw1
      rwa [sub_add_cancel] at this
    have hre : (w - 1).re = 1 / 2 := by simp [hw]; norm_num
    have him : (w - 1).im = w.im := by simp
    have h := norm_Gamma_le_of_re_eq_half hre
    rw [him] at h
    have hn : ‖w - 1‖ ≤ ‖w‖ + 1 := by
      calc ‖w - 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖w‖ + 1 := by simp
    rw [hrec, norm_mul]
    calc ‖w - 1‖ * ‖Complex.Gamma (w - 1)‖
        ≤ (‖w‖ + 1) * ((1 + 2 * Real.pi) * Real.exp (-(Real.pi / 2) * |w.im|)) :=
          mul_le_mul hn h (norm_nonneg _) (by positivity)
      _ = (1 + 2 * Real.pi) * (‖w‖ + 1) * Real.exp (-(Real.pi / 2) * |w.im|) := by ring

private theorem re_weight (z : ℂ) : ((-(Real.pi / 2 : ℝ) : ℂ) * Complex.I * z).re = Real.pi / 2 * z.im := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

private noncomputable def weighted (z : ℂ) : ℂ :=
  Complex.Gamma z * Complex.exp ((-(Real.pi / 2 : ℝ) : ℂ) * Complex.I * z) / z

private theorem norm_weighted (z : ℂ) :
    ‖weighted z‖ = ‖Complex.Gamma z‖ * Real.exp (Real.pi / 2 * z.im) / ‖z‖ := by
  rw [weighted, norm_div, norm_mul, Complex.norm_exp, re_weight]

private theorem differentiableOn_weighted :
    DifferentiableOn ℂ weighted {z : ℂ | 0 < z.re} := by
  intro z hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  have hΓ : DifferentiableAt ℂ Complex.Gamma z := by
    refine Complex.differentiableAt_Gamma z fun m hm => ?_
    have h := congrArg Complex.re hm
    simp at h
    have hz' : (0 : ℝ) < z.re := hz
    have : (0 : ℝ) ≤ (m : ℝ) := m.cast_nonneg
    linarith
  have hexp : DifferentiableAt ℂ (fun z : ℂ => Complex.exp ((-(Real.pi / 2 : ℝ) : ℂ) * Complex.I * z)) z :=
    (Complex.differentiable_exp.comp (differentiable_id.const_mul _)) z
  exact ((hΓ.mul hexp).div differentiableAt_id hz0).differentiableWithinAt

private theorem norm_Gamma_le_on_unit_strip {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 3 / 2) :
    ‖Complex.Gamma w‖ ≤ 3 * (1 + 2 * Real.pi) * ‖w‖ * Real.exp (-(Real.pi / 2) * w.im) := by
  obtain ⟨M, hM⟩ := exists_bound_Gamma_re
  have hK : (0 : ℝ) < 1 + 2 * Real.pi := by positivity

  have hline : ∀ z : ℂ, z.re = 1 / 2 ∨ z.re = 3 / 2 → ‖weighted z‖ ≤ 3 * (1 + 2 * Real.pi) := by
    intro z hz
    have hzn : (1 : ℝ) / 2 ≤ ‖z‖ := by
      have := Complex.abs_re_le_norm z
      rcases hz with hz | hz <;> rw [hz, abs_of_pos (by norm_num)] at this <;> linarith
    have hzpos : (0 : ℝ) < ‖z‖ := by linarith
    have hΓ := norm_Gamma_le_of_re_eq_half_or hz
    have hexp : Real.exp (-(Real.pi / 2) * |z.im|) * Real.exp (Real.pi / 2 * z.im) ≤ 1 := by
      rw [← Real.exp_add, Real.exp_le_one_iff]
      nlinarith [le_abs_self z.im, Real.pi_pos]
    rw [norm_weighted, div_le_iff₀ hzpos]
    have hE : (0 : ℝ) < Real.exp (Real.pi / 2 * z.im) := Real.exp_pos _
    calc ‖Complex.Gamma z‖ * Real.exp (Real.pi / 2 * z.im)
        ≤ (1 + 2 * Real.pi) * (‖z‖ + 1) * Real.exp (-(Real.pi / 2) * |z.im|) *
            Real.exp (Real.pi / 2 * z.im) := mul_le_mul_of_nonneg_right hΓ hE.le
      _ = (1 + 2 * Real.pi) * (‖z‖ + 1) *
            (Real.exp (-(Real.pi / 2) * |z.im|) * Real.exp (Real.pi / 2 * z.im)) := by ring
      _ ≤ (1 + 2 * Real.pi) * (‖z‖ + 1) * 1 := by gcongr
      _ ≤ 3 * (1 + 2 * Real.pi) * ‖z‖ := by nlinarith

  have hgrowth : ∀ z : ℂ, z ∈ Complex.re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2) →
      ‖weighted z‖ ≤ (2 * max M 0) * ‖Real.exp (Real.pi * Real.exp (1 * |z.im|))‖ := by
    intro z hz
    have hz1 : (1 : ℝ) / 2 < z.re := hz.1
    have hz2 : z.re < 3 / 2 := hz.2
    have hzn : (1 : ℝ) / 2 ≤ ‖z‖ := by
      have := Complex.abs_re_le_norm z
      rw [abs_of_pos (by linarith)] at this
      linarith
    have hzpos : (0 : ℝ) < ‖z‖ := by linarith
    have hΓ : ‖Complex.Gamma z‖ ≤ max M 0 :=
      (norm_Gamma_le_Gamma_re (by linarith)).trans ((hM _ hz1.le hz2.le).trans (le_max_left _ _))
    have hexp : Real.exp (Real.pi / 2 * z.im) ≤ Real.exp (Real.pi * Real.exp (1 * |z.im|)) := by
      rw [Real.exp_le_exp, one_mul]
      nlinarith [Real.add_one_le_exp |z.im|, Real.pi_pos, le_abs_self z.im, abs_nonneg z.im]
    rw [norm_weighted, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), div_le_iff₀ hzpos]
    have hM0 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
    calc ‖Complex.Gamma z‖ * Real.exp (Real.pi / 2 * z.im)
        ≤ max M 0 * Real.exp (Real.pi * Real.exp (1 * |z.im|)) :=
          mul_le_mul hΓ hexp (Real.exp_pos _).le hM0
      _ = max M 0 * Real.exp (Real.pi * Real.exp (1 * |z.im|)) * 1 := by ring
      _ ≤ 2 * max M 0 * Real.exp (Real.pi * Real.exp (1 * |z.im|)) * ‖z‖ := by
        have := Real.exp_pos (Real.pi * Real.exp (1 * |z.im|))
        nlinarith [mul_nonneg hM0 this.le]
  have hclosure : closure (Complex.re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2)) ⊆ {z : ℂ | 0 < z.re} := by
    refine (closure_minimal (preimage_mono Ioo_subset_Icc_self)
      (isClosed_Icc.preimage Complex.continuous_re)).trans ?_
    intro z hz
    have : (1 : ℝ) / 2 ≤ z.re := hz.1
    show (0 : ℝ) < z.re
    linarith
  have hPL : ‖weighted w‖ ≤ 3 * (1 + 2 * Real.pi) := by
    refine PhragmenLindelof.vertical_strip (differentiableOn_weighted.mono hclosure).diffContOnCl
      ⟨1, ?_, Real.pi, Asymptotics.IsBigO.of_bound (2 * max M 0) ?_⟩
      (fun z hz => hline z (Or.inl hz)) (fun z hz => hline z (Or.inr hz)) h1 h2
    · norm_num
      linarith [Real.two_le_pi]
    · exact Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall hgrowth)
  have hwn : (0 : ℝ) < ‖w‖ := by
    have := Complex.abs_re_le_norm w
    rw [abs_of_pos (by linarith)] at this
    linarith
  rw [norm_weighted, div_le_iff₀ hwn] at hPL
  have hE : Real.exp (-(Real.pi / 2) * w.im) * Real.exp (Real.pi / 2 * w.im) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  have hEpos : (0 : ℝ) < Real.exp (Real.pi / 2 * w.im) := Real.exp_pos _
  calc ‖Complex.Gamma w‖
      = ‖Complex.Gamma w‖ * Real.exp (Real.pi / 2 * w.im) * Real.exp (-(Real.pi / 2) * w.im) := by
        rw [mul_assoc, mul_comm (Real.exp _) (Real.exp _), hE, mul_one]
    _ ≤ 3 * (1 + 2 * Real.pi) * ‖w‖ * Real.exp (-(Real.pi / 2) * w.im) :=
        mul_le_mul_of_nonneg_right hPL (Real.exp_pos _).le

private theorem norm_Gamma_le_base {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 3 / 2) :
    ‖Complex.Gamma w‖ ≤ 6 * (1 + 2 * Real.pi) * (1 + |w.im|) * Real.exp (-(Real.pi / 2) * |w.im|) := by
  have hK : (0 : ℝ) < 1 + 2 * Real.pi := by positivity

  have key : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 3 / 2 → 0 ≤ z.im →
      ‖Complex.Gamma z‖ ≤ 6 * (1 + 2 * Real.pi) * (1 + |z.im|) * Real.exp (-(Real.pi / 2) * |z.im|) := by
    intro z hz1 hz2 hz3
    have h := norm_Gamma_le_on_unit_strip hz1 hz2
    rw [abs_of_nonneg hz3]
    have hzn : ‖z‖ ≤ 2 * (1 + z.im) := by
      have := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_pos (by linarith), abs_of_nonneg hz3] at this
      linarith
    calc ‖Complex.Gamma z‖ ≤ 3 * (1 + 2 * Real.pi) * ‖z‖ * Real.exp (-(Real.pi / 2) * z.im) := h
      _ ≤ 3 * (1 + 2 * Real.pi) * (2 * (1 + z.im)) * Real.exp (-(Real.pi / 2) * z.im) := by gcongr
      _ = 6 * (1 + 2 * Real.pi) * (1 + z.im) * Real.exp (-(Real.pi / 2) * z.im) := by ring
  rcases le_or_gt 0 w.im with hw | hw
  · exact key w h1 h2 hw
  ·
    have hc := key ((starRingEnd ℂ) w) (by simpa using h1) (by simpa using h2) (by simp; linarith)
    rw [Complex.Gamma_conj, Complex.norm_conj] at hc
    simpa [abs_neg] using hc

private theorem exists_bound_strip (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N : ℕ, ∀ w : ℂ, 1 / 2 - (k : ℝ) ≤ w.re → w.re ≤ 3 / 2 + (k : ℝ) → 1 ≤ |w.im| →
      ‖Complex.Gamma w‖ ≤ A * (1 + |w.im|) ^ N * Real.exp (-(Real.pi / 2) * |w.im|) := by
  induction k with
  | zero =>
    refine ⟨6 * (1 + 2 * Real.pi), by positivity, 1, fun w h1 h2 _ => ?_⟩
    rw [pow_one]
    exact norm_Gamma_le_base (by simpa using h1) (by simpa using h2)
  | succ k ih =>
    obtain ⟨A, hA, N, hN⟩ := ih
    refine ⟨A * ((k : ℝ) + 3), by positivity, N + 1, fun w h1 h2 h3 => ?_⟩
    push_cast at h1 h2
    have hX : (1 : ℝ) ≤ 1 + |w.im| := by linarith [abs_nonneg w.im]
    have hXN : (1 + |w.im|) ^ N ≤ (1 + |w.im|) ^ (N + 1) := pow_le_pow_right₀ hX (Nat.le_succ N)
    have he : (0 : ℝ) < Real.exp (-(Real.pi / 2) * |w.im|) := Real.exp_pos _
    have hk3 : (1 : ℝ) ≤ (k : ℝ) + 3 := by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    rcases lt_or_ge w.re (1 / 2 - (k : ℝ)) with hleft | hleft
    ·
      have hw0 : w ≠ 0 := by
        rintro rfl
        simp at h3
        norm_num at h3
      have hrec : Complex.Gamma (w + 1) = w * Complex.Gamma w := Complex.Gamma_add_one w hw0
      have hb := hN (w + 1) (by simp; linarith) (by simp; linarith) (by simpa using h3)
      simp only [Complex.add_im, Complex.one_im, add_zero] at hb
      rw [hrec, norm_mul] at hb
      have hwn : (1 : ℝ) ≤ ‖w‖ := h3.trans (Complex.abs_im_le_norm w)
      have hΓ : ‖Complex.Gamma w‖ ≤ A * (1 + |w.im|) ^ N * Real.exp (-(Real.pi / 2) * |w.im|) := by
        nlinarith [norm_nonneg (Complex.Gamma w)]
      calc ‖Complex.Gamma w‖ ≤ A * (1 + |w.im|) ^ N * Real.exp (-(Real.pi / 2) * |w.im|) := hΓ
        _ ≤ A * (1 + |w.im|) ^ (N + 1) * Real.exp (-(Real.pi / 2) * |w.im|) := by gcongr
        _ = A * 1 * (1 + |w.im|) ^ (N + 1) * Real.exp (-(Real.pi / 2) * |w.im|) := by ring
        _ ≤ A * ((k : ℝ) + 3) * (1 + |w.im|) ^ (N + 1) * Real.exp (-(Real.pi / 2) * |w.im|) := by
          gcongr
    rcases lt_or_ge (3 / 2 + (k : ℝ)) w.re with hright | hright
    ·
      have hw1 : w - 1 ≠ 0 := by
        intro h
        have := congrArg Complex.im h
        simp at this
        rw [this] at h3
        norm_num at h3
      have hrec : Complex.Gamma w = (w - 1) * Complex.Gamma (w - 1) := by
        have := Complex.Gamma_add_one (w - 1) hw1
        rwa [sub_add_cancel] at this
      have hb := hN (w - 1) (by simp; linarith) (by simp; linarith) (by simpa using h3)
      simp only [Complex.sub_im, Complex.one_im, sub_zero] at hb
      have hn : ‖w - 1‖ ≤ ((k : ℝ) + 3) * (1 + |w.im|) := by
        have := Complex.norm_le_abs_re_add_abs_im (w - 1)
        simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at this
        rw [abs_of_pos (by linarith)] at this
        nlinarith [abs_nonneg w.im]
      rw [hrec, norm_mul]
      calc ‖w - 1‖ * ‖Complex.Gamma (w - 1)‖
          ≤ ((k : ℝ) + 3) * (1 + |w.im|) * (A * (1 + |w.im|) ^ N * Real.exp (-(Real.pi / 2) * |w.im|)) :=
            mul_le_mul hn hb (norm_nonneg _) (by positivity)
        _ = A * ((k : ℝ) + 3) * (1 + |w.im|) ^ (N + 1) * Real.exp (-(Real.pi / 2) * |w.im|) := by
            rw [pow_succ]; ring
    ·
      have hb := hN w hleft hright h3
      calc ‖Complex.Gamma w‖ ≤ A * (1 + |w.im|) ^ N * Real.exp (-(Real.pi / 2) * |w.im|) := hb
        _ ≤ A * (1 + |w.im|) ^ (N + 1) * Real.exp (-(Real.pi / 2) * |w.im|) := by gcongr
        _ = A * 1 * (1 + |w.im|) ^ (N + 1) * Real.exp (-(Real.pi / 2) * |w.im|) := by ring
        _ ≤ A * ((k : ℝ) + 3) * (1 + |w.im|) ^ (N + 1) * Real.exp (-(Real.pi / 2) * |w.im|) := by
          gcongr

private theorem norm_sin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have h2 := Complex.two_sin z
  have hn : ‖(2 : ℂ) * Complex.sin z‖ ≤ 2 * Real.exp |z.im| := by
    rw [h2, norm_mul, Complex.norm_I, mul_one]
    calc ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖
        ≤ ‖Complex.exp (-z * Complex.I)‖ + ‖Complex.exp (z * Complex.I)‖ := norm_sub_le _ _
      _ = Real.exp z.im + Real.exp (-z.im) := by simp [Complex.norm_exp]
      _ ≤ Real.exp |z.im| + Real.exp |z.im| := by
          gcongr
          · exact le_abs_self _
          · exact neg_le_abs _
      _ = 2 * Real.exp |z.im| := by ring
  rw [norm_mul, Complex.norm_ofNat] at hn
  linarith

end GammaVerticalStrips

open GammaVerticalStrips in

theorem solution
    (σ₁ σ₂ : ℝ) :
    ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → 1 ≤ |w.im| →
      ‖Complex.Gamma w‖ ≤ A * (1 + |w.im|) ^ N * Real.exp (-(Real.pi / 2) * |w.im|) ∧
        Real.exp (-(Real.pi / 2) * |w.im|) ≤ A * (1 + |w.im|) ^ N * ‖Complex.Gamma w‖ := by
  obtain ⟨k, hk⟩ := exists_nat_ge (|σ₁| + |σ₂| + 1)
  obtain ⟨A, hA, N, hN⟩ := exists_bound_strip k
  refine ⟨A + A / Real.pi, N, fun w h1 h2 h3 => ?_⟩
  have hs1 := neg_abs_le σ₁
  have hs1' := le_abs_self σ₁
  have hs2 := neg_abs_le σ₂
  have hs2' := le_abs_self σ₂
  have hX : (0 : ℝ) ≤ (1 + |w.im|) ^ N := by positivity
  have he : (0 : ℝ) < Real.exp (-(Real.pi / 2) * |w.im|) := Real.exp_pos _
  have hAπ : (0 : ℝ) ≤ A / Real.pi := div_nonneg hA Real.pi_pos.le
  constructor
  ·
    have hb := hN w (by linarith) (by linarith) h3
    calc ‖Complex.Gamma w‖ ≤ A * (1 + |w.im|) ^ N * Real.exp (-(Real.pi / 2) * |w.im|) := hb
      _ ≤ (A + A / Real.pi) * (1 + |w.im|) ^ N * Real.exp (-(Real.pi / 2) * |w.im|) := by gcongr; linarith
  ·
    have hb := hN (1 - w) (by simp; linarith) (by simp; linarith) (by simpa using h3)
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at hb
    have hsin0 : Complex.sin ((Real.pi : ℂ) * w) ≠ 0 := by
      intro h
      obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.1 h
      have h0 : w.im = 0 := by simpa [Real.pi_ne_zero] using congrArg Complex.im hm
      rw [h0] at h3
      norm_num at h3
    have hrefl := Complex.Gamma_mul_Gamma_one_sub w
    rw [eq_div_iff hsin0] at hrefl
    have hnorm : ‖Complex.Gamma w‖ * ‖Complex.Gamma (1 - w)‖ * ‖Complex.sin ((Real.pi : ℂ) * w)‖ = Real.pi := by
      have h := congrArg norm hrefl
      rwa [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at h
    have hsin : ‖Complex.sin ((Real.pi : ℂ) * w)‖ ≤ Real.exp (Real.pi * |w.im|) := by
      have := norm_sin_le_exp_abs_im ((Real.pi : ℂ) * w)
      rwa [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul,
        abs_of_pos Real.pi_pos] at this

    set g : ℝ := ‖Complex.Gamma w‖ with hg
    set X : ℝ := (1 + |w.im|) ^ N with hXdef
    set e : ℝ := Real.exp (-(Real.pi / 2) * |w.im|) with hedef
    have hee : e * Real.exp (Real.pi * |w.im|) * e = 1 := by
      rw [hedef, ← Real.exp_add, ← Real.exp_add]
      convert Real.exp_zero using 2
      ring
    have hg0 : (0 : ℝ) ≤ g := norm_nonneg _
    have hG1 : (0 : ℝ) ≤ ‖Complex.Gamma (1 - w)‖ := norm_nonneg _
    have hS0 : (0 : ℝ) ≤ ‖Complex.sin ((Real.pi : ℂ) * w)‖ := norm_nonneg _

    have hstep : Real.pi ≤ g * (A * X * e) * Real.exp (Real.pi * |w.im|) := by
      have hAXe : (0 : ℝ) ≤ A * X * e := by positivity
      calc Real.pi = g * ‖Complex.Gamma (1 - w)‖ * ‖Complex.sin ((Real.pi : ℂ) * w)‖ := hnorm.symm
        _ ≤ g * (A * X * e) * ‖Complex.sin ((Real.pi : ℂ) * w)‖ := by gcongr
        _ ≤ g * (A * X * e) * Real.exp (Real.pi * |w.im|) := by gcongr

    have hstep2 : Real.pi * e ≤ A / Real.pi * X * g * Real.pi := by
      have : g * (A * X * e) * Real.exp (Real.pi * |w.im|) * e = g * A * X := by
        calc g * (A * X * e) * Real.exp (Real.pi * |w.im|) * e
            = g * A * X * (e * Real.exp (Real.pi * |w.im|) * e) := by ring
          _ = g * A * X := by rw [hee, mul_one]
      have h' := mul_le_mul_of_nonneg_right hstep he.le
      rw [this] at h'
      have hπ : A / Real.pi * X * g * Real.pi = g * A * X := by
        calc A / Real.pi * X * g * Real.pi = g * A * X * (Real.pi / Real.pi) := by ring
          _ = g * A * X := by rw [div_self Real.pi_ne_zero, mul_one]
      rw [hπ]
      exact h'
    have hfinal : e ≤ A / Real.pi * X * g := by
      have h' : e * Real.pi ≤ A / Real.pi * X * g * Real.pi := by linarith [hstep2]
      exact le_of_mul_le_mul_right h' Real.pi_pos
    calc e ≤ A / Real.pi * X * g := hfinal
      _ ≤ (A + A / Real.pi) * X * g := by gcongr; linarith

end S_Complex_exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
end P2MW
export P2MW.S_Complex_exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im (solution)
