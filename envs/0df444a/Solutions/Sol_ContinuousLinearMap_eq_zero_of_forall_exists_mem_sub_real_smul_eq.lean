-- Prove2me | solution 1 for ContinuousLinearMap.eq_zero_of_forall_exists_mem_sub_real_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d4ef8e1b-b6d9-5573-aaea-167aa432c05d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ContinuousLinearMap_eq_zero_of_forall_exists_mem_sub_real_smul_eq

set_option autoImplicit false

open scoped InnerProductSpace
open MeasureTheory Set

noncomputable section

namespace SymmetricRangeDensity

private def bump (c r : ℝ) : ℝ → ℝ := fun x => max 0 (min 1 (2 - |x - c| / r))

private theorem bump_continuous (c r : ℝ) : Continuous (bump c r) := by
  unfold bump
  fun_prop

private theorem bump_nonneg (c r x : ℝ) : 0 ≤ bump c r x := le_max_left _ _

private theorem bump_le_one (c r x : ℝ) : bump c r x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

private theorem bump_eq_one {c r x : ℝ} (hr : 0 < r) (hx : |x - c| ≤ r) : bump c r x = 1 := by
  unfold bump
  have h1 : |x - c| / r ≤ 1 := (div_le_one hr).mpr hx
  have h2 : (1 : ℝ) ≤ 2 - |x - c| / r := by linarith
  rw [min_eq_left h2, max_eq_right zero_le_one]

private theorem bump_eq_zero {c r x : ℝ} (hr : 0 < r) (hx : 2 * r ≤ |x - c|) : bump c r x = 0 := by
  unfold bump
  have h1 : (2 : ℝ) ≤ |x - c| / r := by
    rw [le_div_iff₀ hr]
    exact hx
  have h2 : min 1 (2 - |x - c| / r) ≤ 0 := le_trans (min_le_right _ _) (by linarith)
  exact le_antisymm (max_le le_rfl h2) (le_max_left _ _)

private theorem bump_hasCompactSupport {c r : ℝ} (hr : 0 < r) : HasCompactSupport (bump c r) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c (2 * r)) ?_
  intro x hx
  rw [Function.mem_support] at hx
  rw [Metric.mem_closedBall, Real.dist_eq]
  by_contra h
  exact hx (bump_eq_zero hr (le_of_lt (not_le.mp h)))

private def bumpC (c r : ℝ) (hr : 0 < r) : CompactlySupportedContinuousMap ℝ ℝ :=
  ⟨⟨bump c r, bump_continuous c r⟩, bump_hasCompactSupport hr⟩

private theorem bumpC_apply (c r : ℝ) (hr : 0 < r) (x : ℝ) : bumpC c r hr x = bump c r x := rfl

private theorem measure_eq_zero_of_forall_measure_closedBall_le_ofReal_mul_sq
    (μ : Measure ℝ) (K : ℝ → ℝ)
    (h : ∀ c r : ℝ, 0 < r → μ (Metric.closedBall c r) ≤ ENNReal.ofReal (K c * r ^ 2)) :
    μ = 0 := by

  have piece : ∀ (n : ℕ) (r a : ℝ), 0 < r →
      μ ({c | K c ≤ n} ∩ Icc a (a + r)) ≤ ENNReal.ofReal (n * r ^ 2) := by
    intro n r a hr
    rcases ({c | K c ≤ n} ∩ Icc a (a + r)).eq_empty_or_nonempty with hE | ⟨c, hcK, hcI⟩
    · rw [hE, measure_empty]
      exact zero_le
    · calc μ ({c | K c ≤ n} ∩ Icc a (a + r))
          ≤ μ (Metric.closedBall c r) := by
            apply measure_mono
            intro x hx
            rw [Metric.mem_closedBall]
            have hd := Real.dist_le_of_mem_Icc hx.2 hcI
            linarith
        _ ≤ ENNReal.ofReal (K c * r ^ 2) := h c r hr
        _ ≤ ENNReal.ofReal (n * r ^ 2) :=
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcK (sq_nonneg r))

  have block : ∀ n R : ℕ, μ ({c | K c ≤ n} ∩ Icc (-(R : ℝ)) R) = 0 := by
    intro n R
    refine le_antisymm ?_ zero_le
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    rw [zero_add]
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    obtain ⟨m, hm⟩ := exists_nat_gt ((2 * (R : ℝ) * n + n) / ε)
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    set r : ℝ := ((m : ℝ) + 1)⁻¹ with hr_def
    have hr : 0 < r := inv_pos.mpr hm1
    have hr_mul : r * ((m : ℝ) + 1) = 1 := inv_mul_cancel₀ hm1.ne'
    have cover : {c | K c ≤ n} ∩ Icc (-(R : ℝ)) R ⊆
        ⋃ j ∈ Finset.range (2 * R * (m + 1) + 1),
          ({c | K c ≤ n} ∩ Icc (-(R : ℝ) + j * r) (-(R : ℝ) + j * r + r)) := by
      intro c hc
      obtain ⟨hcK, hcR⟩ := hc
      have hc1 : -(R : ℝ) ≤ c := hcR.1
      have hc2 : c ≤ R := hcR.2
      set t : ℝ := (c + R) * ((m : ℝ) + 1) with ht_def
      have ht0 : 0 ≤ t := mul_nonneg (by linarith) hm1.le
      have htr : t * r = c + R := by
        rw [ht_def, mul_assoc, mul_comm ((m : ℝ) + 1) r, hr_mul, mul_one]
      have hj1 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
      have hj2 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
      have hjN : ⌊t⌋₊ < 2 * R * (m + 1) + 1 := by
        have ht_le : t ≤ ((2 * R * (m + 1) : ℕ) : ℝ) := by
          rw [ht_def]; push_cast; nlinarith
        exact Nat.lt_succ_of_le (Nat.floor_le_of_le ht_le)
      refine mem_iUnion₂.mpr ⟨⌊t⌋₊, Finset.mem_range.mpr hjN, hcK, ?_, ?_⟩
      ·
        have : (⌊t⌋₊ : ℝ) * r ≤ t * r := mul_le_mul_of_nonneg_right hj1 hr.le
        linarith
      ·
        have : t * r ≤ ((⌊t⌋₊ : ℝ) + 1) * r := mul_le_mul_of_nonneg_right hj2.le hr.le
        linarith
    calc μ ({c | K c ≤ n} ∩ Icc (-(R : ℝ)) R)
        ≤ μ (⋃ j ∈ Finset.range (2 * R * (m + 1) + 1),
            ({c | K c ≤ n} ∩ Icc (-(R : ℝ) + j * r) (-(R : ℝ) + j * r + r))) := measure_mono cover
      _ ≤ ∑ j ∈ Finset.range (2 * R * (m + 1) + 1),
            μ ({c | K c ≤ n} ∩ Icc (-(R : ℝ) + j * r) (-(R : ℝ) + j * r + r)) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _j ∈ Finset.range (2 * R * (m + 1) + 1), ENNReal.ofReal (n * r ^ 2) :=
          Finset.sum_le_sum fun j _ => piece n r _ hr
      _ = ENNReal.ofReal (((2 * R * (m + 1) + 1 : ℕ) : ℝ) * (n * r ^ 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _ ≤ (ε : ENNReal) := by
          rw [← ENNReal.ofReal_coe_nnreal]
          apply ENNReal.ofReal_le_ofReal
          have hm' : 2 * (R : ℝ) * n + n < ε * m := by
            have := (div_lt_iff₀ hε').mp hm
            linarith
          have hr2 : r ^ 2 * ((m : ℝ) + 1) ^ 2 = 1 := by
            rw [← mul_pow, hr_mul, one_pow]
          have key : (((2 * R * (m + 1) + 1 : ℕ) : ℝ) * n) ≤ (ε : ℝ) * ((m : ℝ) + 1) ^ 2 := by
            push_cast
            nlinarith [hm', (Nat.cast_nonneg n : (0 : ℝ) ≤ n), (Nat.cast_nonneg m : (0 : ℝ) ≤ m),
              (Nat.cast_nonneg R : (0 : ℝ) ≤ R), hε']
          calc ((2 * R * (m + 1) + 1 : ℕ) : ℝ) * (n * r ^ 2)
              = (((2 * R * (m + 1) + 1 : ℕ) : ℝ) * n) * r ^ 2 := by ring
            _ ≤ ((ε : ℝ) * ((m : ℝ) + 1) ^ 2) * r ^ 2 :=
                mul_le_mul_of_nonneg_right key (sq_nonneg r)
            _ = (ε : ℝ) := by
                rw [mul_assoc, mul_comm (((m : ℝ) + 1) ^ 2) (r ^ 2), hr2, mul_one]

  have huniv : (univ : Set ℝ) ⊆ ⋃ p : ℕ × ℕ, ({c | K c ≤ p.1} ∩ Icc (-(p.2 : ℝ)) p.2) := by
    intro c _
    refine mem_iUnion.mpr ⟨(⌈K c⌉₊, ⌈|c|⌉₊), Nat.le_ceil (K c), ?_, ?_⟩
    · have := Nat.le_ceil |c|
      have := neg_abs_le c
      linarith
    · have := Nat.le_ceil |c|
      have := le_abs_self c
      linarith
  refine Measure.measure_univ_eq_zero.1 (le_antisymm ?_ zero_le)
  calc μ univ ≤ μ (⋃ p : ℕ × ℕ, ({c | K c ≤ p.1} ∩ Icc (-(p.2 : ℝ)) p.2)) := measure_mono huniv
    _ = 0 := measure_iUnion_null_iff.2 fun p => block p.1 p.2

variable {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]

private theorem inner_apply_comm {B : S →L[ℂ] S} (hB : IsSelfAdjoint B) (x y : S) :
    ⟪B x, y⟫_ℂ = ⟪x, B y⟫_ℂ :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hB) x y

private def quadForm (A : S →L[ℂ] S) (u : S) (f : CompactlySupportedContinuousMap ℝ ℝ) : ℝ :=
  (⟪cfc (⇑f) A u, u⟫_ℂ).re

private theorem quadForm_add (A : S →L[ℂ] S) (u : S) (f g : CompactlySupportedContinuousMap ℝ ℝ) :
    quadForm A u (f + g) = quadForm A u f + quadForm A u g := by
  unfold quadForm
  have hfg : cfc (⇑(f + g)) A = cfc (⇑f) A + cfc (⇑g) A := by
    rw [CompactlySupportedContinuousMap.coe_add]
    exact cfc_add (a := A) (⇑f) (⇑g) (hf := f.continuous.continuousOn)
      (hg := g.continuous.continuousOn)
  rw [hfg, ContinuousLinearMap.add_apply, inner_add_left, Complex.add_re]

private theorem quadForm_smul (A : S →L[ℂ] S) (u : S) (a : ℝ) (f : CompactlySupportedContinuousMap ℝ ℝ) :
    quadForm A u (a • f) = a * quadForm A u f := by
  unfold quadForm
  have haf : cfc (⇑(a • f)) A = a • cfc (⇑f) A := by
    rw [CompactlySupportedContinuousMap.coe_smul]
    exact cfc_smul (a := A) a (⇑f) (hf := f.continuous.continuousOn)
  rw [haf, ContinuousLinearMap.smul_apply, ← Complex.coe_smul, inner_smul_left,
    Complex.conj_ofReal, Complex.re_ofReal_mul]

private theorem quadForm_nonneg {A : S →L[ℂ] S} (u : S) {f : CompactlySupportedContinuousMap ℝ ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ quadForm A u f := by
  unfold quadForm
  set g : ℝ → ℝ := fun x => Real.sqrt (f x) with hg
  have hgc : Continuous g := f.continuous.sqrt
  have hfgg : cfc (⇑f) A = cfc g A * cfc g A := by
    rw [← cfc_mul (a := A) g g (hf := hgc.continuousOn) (hg := hgc.continuousOn)]
    refine cfc_congr (fun x _ => ?_)
    exact (Real.mul_self_sqrt (hf x)).symm
  have hB : IsSelfAdjoint (cfc g A) := cfc_predicate g A
  rw [hfgg, ContinuousLinearMap.mul_apply, inner_apply_comm hB]
  simpa using (inner_self_nonneg (𝕜 := ℂ) (x := cfc g A u))

private def quadFormP (A : S →L[ℂ] S) (u : S) : CompactlySupportedContinuousMap ℝ ℝ →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := quadForm A u
      map_add' := quadForm_add A u
      map_smul' := fun a f => by simpa using quadForm_smul A u a f }
    (fun f hf => quadForm_nonneg u (fun x => by simpa using (CompactlySupportedContinuousMap.le_def.mp hf) x))

private theorem quadFormP_apply (A : S →L[ℂ] S) (u : S) (f : CompactlySupportedContinuousMap ℝ ℝ) :
    quadFormP A u f = quadForm A u f := rfl

private theorem quadForm_le {A : S →L[ℂ] S} (hA : IsSelfAdjoint A) {u w : S} {c r : ℝ} (hr : 0 ≤ r)
    (hw : A w - (c : ℂ) • w = u) (f : ℝ → ℝ) (hfc : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (hfz : ∀ x, r < |x - c| → f x = 0) :
    (⟪cfc f A u, u⟫_ℂ).re ≤ r ^ 2 * ‖w‖ ^ 2 := by

  have hdc : Continuous (fun x : ℝ => x - c) := by fun_prop
  have hD : ∀ y : S, cfc (fun x : ℝ => x - c) A y = A y - (c : ℂ) • y := by
    intro y
    have h1 : cfc (fun x : ℝ => x - c) A = cfc (fun x : ℝ => x) A - cfc (fun _ : ℝ => c) A :=
      cfc_sub (a := A) (fun x : ℝ => x) (fun _ : ℝ => c)
    rw [h1, cfc_id' (R := ℝ) (a := A) (ha := hA), cfc_const (a := A) c (ha := hA),
      ContinuousLinearMap.sub_apply, Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, Complex.coe_smul]
  have hDsa : IsSelfAdjoint (cfc (fun x : ℝ => x - c) A) := cfc_predicate _ A
  have hDw : cfc (fun x : ℝ => x - c) A w = u := by rw [hD, hw]

  have hgc : Continuous (fun x : ℝ => (x - c) * f x * (x - c)) := by fun_prop
  have hcfcg : cfc (fun x : ℝ => (x - c) * f x * (x - c)) A
      = cfc (fun x : ℝ => x - c) A * cfc f A * cfc (fun x : ℝ => x - c) A := by
    rw [← cfc_mul (a := A) (fun x : ℝ => x - c) f (hf := hdc.continuousOn) (hg := hfc.continuousOn),
      ← cfc_mul (a := A) (fun x : ℝ => (x - c) * f x) (fun x : ℝ => x - c)
        (hf := (hdc.mul hfc).continuousOn) (hg := hdc.continuousOn)]
  have hinner : ⟪cfc f A u, u⟫_ℂ = ⟪cfc (fun x : ℝ => (x - c) * f x * (x - c)) A w, w⟫_ℂ := by
    rw [← hDw, ← inner_apply_comm hDsa, hcfcg, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.mul_apply]

  have hgb : ∀ x ∈ spectrum ℝ A, ‖(x - c) * f x * (x - c)‖ ≤ r ^ 2 := by
    intro x _
    by_cases hx : r < |x - c|
    · rw [hfz x hx, mul_zero, zero_mul, norm_zero]
      positivity
    · have hx' : |x - c| ≤ r := not_lt.mp hx
      have hfx : |f x| ≤ 1 := abs_le.mpr ⟨by linarith [hf0 x], hf1 x⟩
      have hxc : 0 ≤ |x - c| := abs_nonneg _
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |x - c| * |f x| * |x - c| ≤ r * 1 * r := by
            gcongr
        _ = r ^ 2 := by ring
  have hnorm : ‖cfc (fun x : ℝ => (x - c) * f x * (x - c)) A‖ ≤ r ^ 2 := norm_cfc_le (sq_nonneg r) hgb
  calc (⟪cfc f A u, u⟫_ℂ).re = (⟪cfc (fun x : ℝ => (x - c) * f x * (x - c)) A w, w⟫_ℂ).re := by
        rw [hinner]
    _ ≤ ‖⟪cfc (fun x : ℝ => (x - c) * f x * (x - c)) A w, w⟫_ℂ‖ := Complex.re_le_norm _
    _ ≤ ‖cfc (fun x : ℝ => (x - c) * f x * (x - c)) A w‖ * ‖w‖ := norm_inner_le_norm _ _
    _ ≤ ‖cfc (fun x : ℝ => (x - c) * f x * (x - c)) A‖ * ‖w‖ * ‖w‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ w
    _ ≤ r ^ 2 * ‖w‖ * ‖w‖ := by gcongr
    _ = r ^ 2 * ‖w‖ ^ 2 := by ring

private theorem core {A : S →L[ℂ] S} (hA : IsSelfAdjoint A) (u : S)
    (hu : ∀ c : ℝ, ∃ w : S, A w - (c : ℂ) • w = u) : u = 0 := by
  classical
  choose w hw using hu

  set Λ := quadFormP A u with hΛ
  set μ : Measure ℝ := RealRMK.rieszMeasure Λ with hμ
  have hint : ∀ f : CompactlySupportedContinuousMap ℝ ℝ, ∫ x, f x ∂μ = quadForm A u f :=
    fun f => RealRMK.integral_rieszMeasure Λ f

  have hball : ∀ c : ℝ, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall c r) ≤ ENNReal.ofReal (4 * ‖w c‖ ^ 2 * r ^ 2) := by
    intro c r hr
    have h2r : (0 : ℝ) ≤ 2 * r := by linarith
    set f := bumpC c r hr with hf
    have hfi : Integrable (fun x => f x) μ := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
    have hlt : μ (Metric.closedBall c r) < ⊤ := measure_closedBall_lt_top

    have hlow : (μ (Metric.closedBall c r)).toReal ≤ ∫ x, f x ∂μ := by
      have h1 : ∫ x in Metric.closedBall c r, f x ∂μ ≤ ∫ x, f x ∂μ :=
        setIntegral_le_integral hfi (Filter.Eventually.of_forall (fun x => bump_nonneg c r x))
      have h2 : ∫ x in Metric.closedBall c r, f x ∂μ = ∫ x in Metric.closedBall c r, (1 : ℝ) ∂μ := by
        refine setIntegral_congr_fun measurableSet_closedBall (fun x hx => ?_)
        rw [Metric.mem_closedBall, Real.dist_eq] at hx
        exact bump_eq_one hr hx
      rw [h2, setIntegral_const, smul_eq_mul, mul_one] at h1
      simpa [Measure.real] using h1

    have hup : ∫ x, f x ∂μ ≤ (2 * r) ^ 2 * ‖w c‖ ^ 2 := by
      rw [hint f]
      exact quadForm_le hA h2r (hw c) (bump c r) (bump_continuous c r) (bump_nonneg c r)
        (bump_le_one c r) (fun x hx => bump_eq_zero hr (le_of_lt hx))
    have h4 : (2 * r) ^ 2 * ‖w c‖ ^ 2 = 4 * ‖w c‖ ^ 2 * r ^ 2 := by ring
    have hreal : (μ (Metric.closedBall c r)).toReal ≤ 4 * ‖w c‖ ^ 2 * r ^ 2 := by
      linarith [hlow, hup]
    exact (ENNReal.le_ofReal_iff_toReal_le hlt.ne (by positivity)).mpr hreal

  have hμ0 : μ = 0 := measure_eq_zero_of_forall_measure_closedBall_le_ofReal_mul_sq μ (fun c => 4 * ‖w c‖ ^ 2) hball

  obtain ⟨R₀, hR₀⟩ := (ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) A).isBounded.subset_closedBall 0
  set R : ℝ := max R₀ 0 + 1 with hR
  have hRpos : 0 < R := by positivity
  have hspec : ∀ x ∈ spectrum ℝ A, bump 0 R x = 1 := by
    intro x hx
    have hx' : |x - 0| ≤ R := by
      have := hR₀ hx
      rw [Metric.mem_closedBall, Real.dist_eq] at this
      linarith [le_max_left R₀ 0]
    exact bump_eq_one hRpos hx'
  have hone : cfc (bump 0 R) A = 1 := by
    rw [cfc_congr (g := fun _ : ℝ => (1 : ℝ)) (fun x hx => hspec x hx)]
    exact cfc_const_one (R := ℝ) (a := A) (ha := hA)
  have hmass : ‖u‖ ^ 2 = ∫ x, bumpC 0 R hRpos x ∂μ := by
    rw [hint, quadForm]
    show ‖u‖ ^ 2 = (⟪cfc (bump 0 R) A u, u⟫_ℂ).re
    rw [hone, ContinuousLinearMap.one_apply]
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) u).symm
  rw [hμ0, integral_zero_measure] at hmass
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hmass)

end SymmetricRangeDensity

open SymmetricRangeDensity in

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (E : Submodule ℂ H)
    (hsym : ∀ x ∈ E, ∀ y ∈ E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (v : H) (hsurj : ∀ c : ℝ, ∃ w ∈ E, T w - (c : ℂ) • w = v) :
    v = 0 := by
  classical

  set S := E.topologicalClosure with hS
  haveI : CompleteSpace S :=
    completeSpace_coe_iff_isComplete.mpr E.isClosed_topologicalClosure.isComplete
  set A : S →L[ℂ] S := S.orthogonalProjection.comp (T.comp S.subtypeL) with hAdef
  have hA_apply : ∀ x : S, A x = S.orthogonalProjection (T x) := fun x => rfl

  have hES : (E : Set H) ⊆ (S : Set H) := E.le_topologicalClosure
  have hScl : (S : Set H) = closure (E : Set H) := E.topologicalClosure_coe
  have hsym1 : ∀ y ∈ E, ∀ x ∈ S, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
    intro y hy x hx
    have hcl : IsClosed {x : H | ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ} :=
      isClosed_eq (T.continuous.inner continuous_const) (continuous_id.inner continuous_const)
    have hsub : (E : Set H) ⊆ {x : H | ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ} := fun x hx => hsym x hx y hy
    have hx' : (x : H) ∈ closure (E : Set H) := by rw [← hScl]; exact hx
    exact closure_minimal hsub hcl hx'
  have hsymS : ∀ x ∈ S, ∀ y ∈ S, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
    intro x hx y hy
    have hcl : IsClosed {y : H | ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ} :=
      isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner T.continuous)
    have hsub : (E : Set H) ⊆ {y : H | ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ} := fun y hy => hsym1 y hy x hx
    have hy' : (y : H) ∈ closure (E : Set H) := by rw [← hScl]; exact hy
    exact closure_minimal hsub hcl hy'

  have hA : IsSelfAdjoint A := by
    refine LinearMap.IsSymmetric.isSelfAdjoint (fun x y => ?_)
    show ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ
    rw [hA_apply, hA_apply, Submodule.inner_orthogonalProjection_eq_of_mem_right,
      Submodule.inner_orthogonalProjection_eq_of_mem_left]
    exact hsymS x x.2 y y.2

  choose w hwE hw using hsurj
  have hwS : ∀ c, w c ∈ S := fun c => hES (hwE c)
  have hPv : ∀ c : ℝ, A ⟨w c, hwS c⟩ - (c : ℂ) • ⟨w c, hwS c⟩ = S.orthogonalProjection v := by
    intro c
    have h1 : S.orthogonalProjection (w c) = ⟨w c, hwS c⟩ :=
      Submodule.orthogonalProjection_mem_subspace_eq_self (⟨w c, hwS c⟩ : S)
    show S.orthogonalProjection (T (w c)) - (c : ℂ) • (⟨w c, hwS c⟩ : S) = S.orthogonalProjection v
    rw [← h1, ← map_smul, ← map_sub, hw c]

  have hPv0 : S.orthogonalProjection v = 0 :=
    core hA (S.orthogonalProjection v) (fun c => ⟨⟨w c, hwS c⟩, hPv c⟩)

  set c₀ : ℝ := ‖A‖ + 1 with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  have heig : A ⟨w c₀, hwS c₀⟩ = (c₀ : ℂ) • ⟨w c₀, hwS c₀⟩ := by
    rw [← sub_eq_zero, hPv c₀, hPv0]
  have hw0 : (⟨w c₀, hwS c₀⟩ : S) = 0 := by
    by_contra hne
    have hpos : 0 < ‖(⟨w c₀, hwS c₀⟩ : S)‖ := norm_pos_iff.mpr hne
    have h1 : ‖A ⟨w c₀, hwS c₀⟩‖ ≤ ‖A‖ * ‖(⟨w c₀, hwS c₀⟩ : S)‖ := A.le_opNorm _
    rw [heig, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc₀pos] at h1
    have : c₀ ≤ ‖A‖ := le_of_mul_le_mul_right h1 hpos
    linarith
  have hw0' : w c₀ = 0 := by
    have := congrArg Subtype.val hw0
    simpa using this
  have := hw c₀
  rw [hw0', map_zero, smul_zero, sub_zero] at this
  exact this.symm

end

#print axioms solution

end S_ContinuousLinearMap_eq_zero_of_forall_exists_mem_sub_real_smul_eq
end P2MW
export P2MW.S_ContinuousLinearMap_eq_zero_of_forall_exists_mem_sub_real_smul_eq (solution)
