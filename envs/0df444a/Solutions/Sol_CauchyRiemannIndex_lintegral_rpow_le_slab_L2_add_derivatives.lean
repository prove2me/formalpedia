-- Prove2me | solution 1 for CauchyRiemannIndex.lintegral_rpow_le_slab_L2_add_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T21:35:11.696967+00:00
-- url     : https://prove2.me/submissions/99ea48ac-8b0a-4ddd-88f2-306082b12e70

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.MeanInequalitiesPow

-- ===== Scratch/CRBox1.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-! ### One-dimensional pieces -/

/-- A `C¹` curve: `|g x - g y| ≤ ∫_{[a,b]} |g'|` for `x, y ∈ [a, b]`. -/
lemma crbox_seg {g g' : ℝ → Vec n} (hg : ∀ r, HasDerivAt g (g' r) r) (hc : Continuous g')
    {a b x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖g x - g y‖ₑ ≤ ∫⁻ r in Icc a b, ‖g' r‖ₑ := by
  have key : ∀ x y, x ∈ Icc a b → y ∈ Icc a b → x ≤ y →
      ‖g y - g x‖ₑ ≤ ∫⁻ r in Icc a b, ‖g' r‖ₑ := by
    intro x y hx hy hxy
    have hint : IntervalIntegrable g' volume x y := hc.intervalIntegrable x y
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hg r) hint
    rw [← hftc, intervalIntegral.integral_of_le hxy]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_set ?_)
    intro r hr
    exact ⟨hx.1.trans hr.1.le, hr.2.trans hy.2⟩
  rcases le_total x y with h | h
  · rw [← enorm_neg, neg_sub]; exact key x y hx hy h
  · exact key y x hy hx h

/-- Jensen/Hölder on a finite measure: `(∫ f)^p ≤ μ(univ)^{p-1} ∫ f^p` for `p > 1`. -/
lemma crbox_jensen {α : Type*} [MeasurableSpace α] (μ : Measure α) {p : ℝ} (hp : 1 < p)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ a, f a ∂μ) ^ p ≤ μ univ ^ (p - 1) * ∫⁻ a, f a ^ p ∂μ := by
  have hpq := Real.HolderConjugate.conjExponent hp
  set q := p.conjExponent with hq
  have hq0 : 0 < q := hpq.symm.pos
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  have hp0 : 0 < p := by linarith
  calc (∫⁻ a, f a ∂μ) ^ p
      ≤ ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * μ univ ^ (1 / q)) ^ p :=
        ENNReal.rpow_le_rpow h hp0.le
    _ = (∫⁻ a, f a ^ p ∂μ) * μ univ ^ (p - 1) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        congr 1
        · rw [one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
        · congr 1
          have := hpq.inv_add_inv_eq_one
          field_simp
          field_simp at this
          linarith
    _ = μ univ ^ (p - 1) * ∫⁻ a, f a ^ p ∂μ := mul_comm _ _

/-- Superadditivity of `x ↦ x^q`, `q ≥ 1`, over a finite sum. -/
lemma crbox_sum_rpow_le {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) {q : ℝ} (hq : 1 ≤ q) :
    ∑ i ∈ s, f i ^ q ≤ (∑ i ∈ s, f i) ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos (by linarith : (0 : ℝ) < q)]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans (ENNReal.add_rpow_le_rpow_add _ _ hq)

/-- Splitting `[0, k/N)` into the `k` grid intervals of length `1/N`. -/
lemma crbox_partition (f : ℝ → ℝ≥0∞) (h : ℝ) (hh : 0 ≤ h) (k : ℕ) :
    ∫⁻ t in Ico 0 (k * h), f t =
      ∑ j ∈ Finset.range k, ∫⁻ t in Ico (j * h) ((j + 1) * h), f t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    push_cast
    rw [← lintegral_union measurableSet_Ico (Ico_disjoint_Ico_same),
      Ico_union_Ico_eq_Ico (by positivity) (by nlinarith)]

/-- `∫⁻ r in [s, s+h], ψ r = ∫⁻ ρ in [0, h], ψ (ρ + s)`. -/
lemma crbox_shift (ψ : ℝ → ℝ≥0∞) (hψ : Measurable ψ) (s h : ℝ) :
    ∫⁻ r in Icc s (s + h), ψ r = ∫⁻ ρ in Icc 0 h, ψ (ρ + s) := by
  have hmp := measurePreserving_add_right (volume : Measure ℝ) s
  rw [← hmp.setLIntegral_comp_preimage measurableSet_Icc hψ]
  congr 2
  ext ρ; simp only [mem_preimage, mem_Icc]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- `∫_s ∫_{[s, s+h]} ψ = h ∫ ψ`. -/
lemma crbox_shift_int (ψ : ℝ → ℝ≥0∞) (hψ : Measurable ψ) {h : ℝ} (hh : 0 ≤ h) :
    ∫⁻ s, ∫⁻ r in Icc s (s + h), ψ r = ENNReal.ofReal h * ∫⁻ r, ψ r := by
  rw [show (fun s => ∫⁻ r in Icc s (s + h), ψ r) = fun s => ∫⁻ ρ in Icc 0 h, ψ (ρ + s) from
    funext fun s => crbox_shift ψ hψ s h]
  rw [lintegral_lintegral_swap]
  · simp_rw [lintegral_add_left_eq_self (μ := (volume : Measure ℝ)) ψ]
    rw [setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm]
  · exact (hψ.comp (measurable_snd.add measurable_fst)).aemeasurable

end

end CauchyRiemannIndex

-- ===== Scratch/CRBox2.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

lemma crbox_hasDerivAt_s {u : ℝ × ℝ → Vec n} (hu : ContDiff ℝ 1 u) (t r : ℝ) :
    HasDerivAt (fun r => u (r, t)) (partialS u (r, t)) r := by
  have hd := ((hu.differentiable one_ne_zero) (r, t)).hasFDerivAt
  exact hd.comp_hasDerivAt r ((hasDerivAt_id r).prodMk (hasDerivAt_const r t))

lemma crbox_hasDerivAt_t {u : ℝ × ℝ → Vec n} (hu : ContDiff ℝ 1 u) (s r : ℝ) :
    HasDerivAt (fun r => u (s, r)) (partialT u (s, r)) r := by
  have hd := ((hu.differentiable one_ne_zero) (s, r)).hasFDerivAt
  exact hd.comp_hasDerivAt r ((hasDerivAt_const r s).prodMk (hasDerivAt_id r))

lemma crbox_cont_S {u : ℝ × ℝ → Vec n} (hu : ContDiff ℝ 1 u) : Continuous (partialS u) :=
  (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const

lemma crbox_cont_T {u : ℝ × ℝ → Vec n} (hu : ContDiff ℝ 1 u) : Continuous (partialT u) :=
  (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- Pointwise bound by a value at another point plus two segment integrals. -/
lemma crbox_point {u : ℝ × ℝ → Vec n} (hu : ContDiff ℝ 1 u) {s t σ τ a b h : ℝ}
    (hσ : σ ∈ Icc s (s + h)) (ht : t ∈ Icc a b) (hτ : τ ∈ Icc a b) :
    ‖u (s, t)‖ₑ ≤ ‖u (σ, τ)‖ₑ + (∫⁻ r in Icc s (s + h), ‖partialS u (r, t)‖ₑ) +
      ∫⁻ r in Ico a b, ‖partialT u (σ, r)‖ₑ := by
  have e : u (s, t) = u (σ, τ) + (u (s, t) - u (σ, t)) + (u (σ, t) - u (σ, τ)) := by abel
  have hs : s ∈ Icc s (s + h) := ⟨le_rfl, hσ.1.trans hσ.2⟩
  have h1 := crbox_seg (g := fun r => u (r, t)) (g' := fun r => partialS u (r, t))
    (crbox_hasDerivAt_s hu t) ((crbox_cont_S hu).comp (continuous_id.prodMk continuous_const))
    hs hσ
  have h2 := crbox_seg (g := fun r => u (σ, r)) (g' := fun r => partialT u (σ, r))
    (crbox_hasDerivAt_t hu σ) ((crbox_cont_T hu).comp (continuous_const.prodMk continuous_id))
    ht hτ
  rw [← setLIntegral_congr (Ico_ae_eq_Icc (μ := volume))] at h2
  rw [e]
  exact (enorm_add_le _ _).trans
    (add_le_add ((enorm_add_le _ _).trans (add_le_add le_rfl h1)) h2)

lemma crbox_meas_inner {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) (S : Set ℝ) :
    Measurable fun σ => ∫⁻ τ in S, f (σ, τ) :=
  hf.lintegral_prod_right'

/-- Averaged form of `crbox_point` over the box `[s, s+h] × [a, a+h)`. -/
lemma crbox_avg {u : ℝ × ℝ → Vec n} (hu : ContDiff ℝ 1 u) {s t a h : ℝ} (hh : 0 < h)
    (ht : t ∈ Ico a (a + h)) :
    ‖u (s, t)‖ₑ * (ENNReal.ofReal h * ENNReal.ofReal h) ≤
      (∫⁻ σ in Icc s (s + h), ∫⁻ τ in Ico a (a + h), ‖u (σ, τ)‖ₑ) +
        (∫⁻ r in Icc s (s + h), ‖partialS u (r, t)‖ₑ) * (ENNReal.ofReal h * ENNReal.ofReal h) +
        ENNReal.ofReal h * ∫⁻ σ in Icc s (s + h), ∫⁻ r in Ico a (a + h), ‖partialT u (σ, r)‖ₑ := by
  set H := ENNReal.ofReal h
  set A := ∫⁻ r in Icc s (s + h), ‖partialS u (r, t)‖ₑ
  set B : ℝ → ℝ≥0∞ := fun σ => ∫⁻ r in Ico a (a + h), ‖partialT u (σ, r)‖ₑ with hB
  have hHtop : H ≠ ⊤ := ENNReal.ofReal_ne_top
  have hIco : volume (Ico a (a + h)) = H := by rw [Real.volume_Ico, add_sub_cancel_left]
  have hIcc : volume (Icc s (s + h)) = H := by rw [Real.volume_Icc, add_sub_cancel_left]
  have hmu : Measurable fun z : ℝ × ℝ => ‖u z‖ₑ := hu.continuous.enorm.measurable
  have hmT : Measurable fun z : ℝ × ℝ => ‖partialT u z‖ₑ := (crbox_cont_T hu).enorm.measurable
  have step1 : ∀ σ ∈ Icc s (s + h),
      ‖u (s, t)‖ₑ * H ≤ (∫⁻ τ in Ico a (a + h), ‖u (σ, τ)‖ₑ) + (A + B σ) * H := by
    intro σ hσ
    calc ‖u (s, t)‖ₑ * H = ∫⁻ _ in Ico a (a + h), ‖u (s, t)‖ₑ := by
          rw [setLIntegral_const, hIco]
      _ ≤ ∫⁻ τ in Ico a (a + h), (‖u (σ, τ)‖ₑ + (A + B σ)) := by
          refine setLIntegral_mono' measurableSet_Ico fun τ hτ => ?_
          rw [← add_assoc]
          exact crbox_point hu hσ (Ico_subset_Icc_self ht) (Ico_subset_Icc_self hτ)
      _ = _ := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, hIco]
  have hX : Measurable fun σ => ∫⁻ τ in Ico a (a + h), ‖u (σ, τ)‖ₑ :=
    crbox_meas_inner hmu _
  have hBm : Measurable B := crbox_meas_inner hmT _
  calc ‖u (s, t)‖ₑ * (H * H) = ∫⁻ _ in Icc s (s + h), ‖u (s, t)‖ₑ * H := by
        rw [setLIntegral_const, hIcc, mul_assoc]
    _ ≤ ∫⁻ σ in Icc s (s + h), ((∫⁻ τ in Ico a (a + h), ‖u (σ, τ)‖ₑ) + (A + B σ) * H) :=
        setLIntegral_mono' measurableSet_Icc step1
    _ = (∫⁻ σ in Icc s (s + h), ∫⁻ τ in Ico a (a + h), ‖u (σ, τ)‖ₑ) +
          (A * H + ∫⁻ σ in Icc s (s + h), B σ) * H := by
        rw [lintegral_add_left hX, lintegral_mul_const' _ _ hHtop,
          lintegral_add_left measurable_const, setLIntegral_const, hIcc]
    _ = _ := by ring

/-- `(x + y + z)^p ≤ 3^{p-1} (x^p + y^p + z^p)`. -/
lemma crbox_three (x y z : ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (x + y + z) ^ p ≤ 3 ^ (p - 1) * (x ^ p + y ^ p + z ^ p) := by
  have := ENNReal.rpow_sum_le_const_mul_sum_rpow (s := (Finset.univ : Finset (Fin 3)))
    (f := ![x, y, z]) hp
  simpa [Fin.sum_univ_three] using this

end

end CauchyRiemannIndex

-- ===== Scratch/CRBox3.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

lemma crbox_H_mul {h : ℝ} (hh : 0 < h) (a b : ℝ) :
    ENNReal.ofReal h ^ a * ENNReal.ofReal h ^ b = ENNReal.ofReal h ^ (a + b) :=
  (ENNReal.rpow_add a b (ENNReal.ofReal_pos.2 hh).ne' ENNReal.ofReal_ne_top).symm

lemma crbox_H_rpow {h : ℝ} (hh : 0 < h) (a b : ℝ) :
    (ENNReal.ofReal h ^ a) ^ b = ENNReal.ofReal h ^ (a * b) :=
  (ENNReal.rpow_mul _ a b).symm

lemma crbox_H_inv {h : ℝ} (hh : 0 < h) : (ENNReal.ofReal h)⁻¹ = ENNReal.ofReal h ^ (-1 : ℝ) :=
  (ENNReal.rpow_neg_one _).symm

lemma crbox_H_one {h : ℝ} : ENNReal.ofReal h = ENNReal.ofReal h ^ (1 : ℝ) :=
  (ENNReal.rpow_one _).symm

/-- Box measure. -/
lemma crbox_box_univ (s a h : ℝ) :
    ((volume.restrict (Icc s (s + h))).prod (volume.restrict (Ico a (a + h)))) univ =
      ENNReal.ofReal h * ENNReal.ofReal h := by
  rw [← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
    Measure.restrict_apply_univ, Real.volume_Icc, Real.volume_Ico, add_sub_cancel_left,
    add_sub_cancel_left]

/-- The `p`-th power of the pointwise bound. -/
lemma crbox_pow {u : ℝ × ℝ → Vec n} (hu : ContDiff ℝ 1 u) {p : ℝ} (hp : 2 ≤ p)
    {s t a h : ℝ} (hh : 0 < h) (ht : t ∈ Ico a (a + h)) :
    ‖u (s, t)‖ₑ ^ p ≤ 3 ^ (p - 1) *
      (ENNReal.ofReal h ^ (-p) *
          (∫⁻ σ in Icc s (s + h), ∫⁻ τ in Ico a (a + h), ‖u (σ, τ)‖ₑ ^ (2 : ℝ)) ^ (p / 2) +
        ENNReal.ofReal h ^ (p - 1) * (∫⁻ r in Icc s (s + h), ‖partialS u (r, t)‖ₑ ^ p) +
        ENNReal.ofReal h ^ (p - 2) *
          ∫⁻ σ in Icc s (s + h), ∫⁻ r in Ico a (a + h), ‖partialT u (σ, r)‖ₑ ^ p) := by
  set H := ENNReal.ofReal h with hHdef
  have h0 : H ≠ 0 := (ENNReal.ofReal_pos.2 hh).ne'
  have htop : H ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  set I := Icc s (s + h)
  set J := Ico a (a + h)
  set X := ∫⁻ σ in I, ∫⁻ τ in J, ‖u (σ, τ)‖ₑ
  set G := ∫⁻ σ in I, ∫⁻ τ in J, ‖u (σ, τ)‖ₑ ^ (2 : ℝ)
  set A := ∫⁻ r in I, ‖partialS u (r, t)‖ₑ
  set B : ℝ → ℝ≥0∞ := fun σ => ∫⁻ r in J, ‖partialT u (σ, r)‖ₑ with hB
  set Y := ∫⁻ σ in I, B σ
  have hmu : Measurable fun z : ℝ × ℝ => ‖u z‖ₑ := hu.continuous.enorm.measurable
  have hmT : Measurable fun z : ℝ × ℝ => ‖partialT u z‖ₑ := (crbox_cont_T hu).enorm.measurable
  have hIcc : (volume.restrict I) univ = H := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc, add_sub_cancel_left]
  have hIco : (volume.restrict J) univ = H := by
    rw [Measure.restrict_apply_univ, Real.volume_Ico, add_sub_cancel_left]
  have hHH : H * H * (H⁻¹ * H⁻¹) = 1 := by
    rw [mul_mul_mul_comm, ENNReal.mul_inv_cancel h0 htop, one_mul]
  -- divided pointwise bound
  have havg := crbox_avg hu (s := s) hh ht
  have hdiv : ‖u (s, t)‖ₑ ≤ H⁻¹ * H⁻¹ * X + A + H⁻¹ * Y := by
    calc ‖u (s, t)‖ₑ = ‖u (s, t)‖ₑ * (H * H) * (H⁻¹ * H⁻¹) := by rw [mul_assoc, hHH, mul_one]
      _ ≤ (X + A * (H * H) + H * Y) * (H⁻¹ * H⁻¹) := by gcongr
      _ = H⁻¹ * H⁻¹ * X + A * (H * H * (H⁻¹ * H⁻¹)) + (H * H⁻¹) * H⁻¹ * Y := by ring
      _ = H⁻¹ * H⁻¹ * X + A + H⁻¹ * Y := by
        rw [hHH, ENNReal.mul_inv_cancel h0 htop]; ring
  have e2 : H ^ (2 : ℝ) = H * H := by rw [ENNReal.rpow_two, sq]
  have e1 : H ^ (-2 : ℝ) = H⁻¹ * H⁻¹ := by
    rw [ENNReal.rpow_neg, e2, ENNReal.mul_inv (Or.inl h0) (Or.inl htop)]
  -- term 1
  have hT1 : (H⁻¹ * H⁻¹ * X) ^ p ≤ H ^ (-p) * G ^ (p / 2) := by
    have hX2 : X ^ (2 : ℝ) ≤ (H * H) * G := by
      have hj := crbox_jensen ((volume.restrict I).prod (volume.restrict J)) (p := 2)
        (by norm_num) hmu.aemeasurable
      rw [crbox_box_univ, lintegral_prod _ hmu.aemeasurable,
        lintegral_prod _ (hmu.pow_const _).aemeasurable] at hj
      rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at hj
      exact hj
    have hXp : X ^ p ≤ (H * H) ^ (p / 2) * G ^ (p / 2) := by
      calc X ^ p = (X ^ (2 : ℝ)) ^ (p / 2) := by
            rw [← ENNReal.rpow_mul]; congr 1; ring
        _ ≤ ((H * H) * G) ^ (p / 2) := ENNReal.rpow_le_rpow hX2 (by positivity)
        _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    calc (H⁻¹ * H⁻¹ * X) ^ p = (H⁻¹ * H⁻¹) ^ p * X ^ p :=
          ENNReal.mul_rpow_of_nonneg _ _ hp0.le
      _ ≤ (H⁻¹ * H⁻¹) ^ p * ((H * H) ^ (p / 2) * G ^ (p / 2)) := by gcongr
      _ = ((H⁻¹ * H⁻¹) ^ p * (H * H) ^ (p / 2)) * G ^ (p / 2) := by ring
      _ = H ^ (-p) * G ^ (p / 2) := by
        congr 1
        rw [← e1, ← e2, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ h0 htop]
        congr 1; ring
  -- term 2
  have hT2 : A ^ p ≤ H ^ (p - 1) * ∫⁻ r in I, ‖partialS u (r, t)‖ₑ ^ p := by
    have hj := crbox_jensen (volume.restrict I) hp1 (f := fun r => ‖partialS u (r, t)‖ₑ)
      ((crbox_cont_S hu).comp (continuous_id.prodMk continuous_const)).enorm.measurable.aemeasurable
    rwa [hIcc] at hj
  -- term 3
  have hBp : ∀ σ, B σ ^ p ≤ H ^ (p - 1) * ∫⁻ r in J, ‖partialT u (σ, r)‖ₑ ^ p := by
    intro σ
    have hj := crbox_jensen (volume.restrict J) hp1 (f := fun r => ‖partialT u (σ, r)‖ₑ)
      ((crbox_cont_T hu).comp (continuous_const.prodMk continuous_id)).enorm.measurable.aemeasurable
    rwa [hIco] at hj
  have hBm : Measurable B := crbox_meas_inner hmT _
  have hT3 : (H⁻¹ * Y) ^ p ≤ H ^ (p - 2) * ∫⁻ σ in I, ∫⁻ r in J, ‖partialT u (σ, r)‖ₑ ^ p := by
    have hY : Y ^ p ≤ H ^ (p - 1) * ∫⁻ σ in I, B σ ^ p := by
      have hj := crbox_jensen (volume.restrict I) hp1 hBm.aemeasurable
      rwa [hIcc] at hj
    calc (H⁻¹ * Y) ^ p = H⁻¹ ^ p * Y ^ p := ENNReal.mul_rpow_of_nonneg _ _ hp0.le
      _ ≤ H⁻¹ ^ p * (H ^ (p - 1) * ∫⁻ σ in I, H ^ (p - 1) *
            ∫⁻ r in J, ‖partialT u (σ, r)‖ₑ ^ p) := by
          gcongr
          exact hY.trans (mul_le_mul_right (lintegral_mono fun σ => hBp σ) _)
      _ = (H⁻¹ ^ p * H ^ (p - 1) * H ^ (p - 1)) *
            ∫⁻ σ in I, ∫⁻ r in J, ‖partialT u (σ, r)‖ₑ ^ p := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) htop)]
          ring
      _ = H ^ (p - 2) * ∫⁻ σ in I, ∫⁻ r in J, ‖partialT u (σ, r)‖ₑ ^ p := by
          congr 1
          rw [← ENNReal.rpow_neg_one, ← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ h0 htop,
            ← ENNReal.rpow_add _ _ h0 htop]
          congr 1; ring
  calc ‖u (s, t)‖ₑ ^ p ≤ (H⁻¹ * H⁻¹ * X + A + H⁻¹ * Y) ^ p :=
        ENNReal.rpow_le_rpow hdiv hp0.le
    _ ≤ 3 ^ (p - 1) * ((H⁻¹ * H⁻¹ * X) ^ p + A ^ p + (H⁻¹ * Y) ^ p) :=
        crbox_three _ _ _ hp1.le
    _ ≤ _ := mul_le_mul_right (add_le_add (add_le_add hT1 hT2) hT3) _

end

end CauchyRiemannIndex

-- ===== Scratch/CRBox4.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

lemma crbox_rpow_ne_top {x : ℝ≥0∞} (h0 : x ≠ 0) (ht : x ≠ ⊤) (a : ℝ) : x ^ a ≠ ⊤ := by
  rcases le_or_gt 0 a with ha | ha
  · exact ENNReal.rpow_ne_top_of_nonneg ha ht
  · exact (ENNReal.rpow_lt_top_of_nonneg (by linarith : 0 ≤ -a) (ENNReal.inv_ne_top.2 h0)).ne
      |> fun h => by rwa [ENNReal.inv_rpow, ← ENNReal.rpow_neg, neg_neg] at h

/-- Integration of `crbox_pow` over one `t`-cell `[a, a+h)`. -/
lemma crbox_slice {u : ℝ × ℝ → Vec n} (hu : ContDiff ℝ 1 u) {p : ℝ} (hp : 2 ≤ p)
    {h : ℝ} (hh : 0 < h) (s a : ℝ) :
    ∫⁻ t in Ico a (a + h), ‖u (s, t)‖ₑ ^ p ≤ 3 ^ (p - 1) *
      (ENNReal.ofReal h ^ (1 - p) *
          (∫⁻ σ in Icc s (s + h), ∫⁻ τ in Ico a (a + h), ‖u (σ, τ)‖ₑ ^ (2 : ℝ)) ^ (p / 2) +
        ENNReal.ofReal h ^ (p - 1) *
          (∫⁻ t in Ico a (a + h), ∫⁻ r in Icc s (s + h), ‖partialS u (r, t)‖ₑ ^ p) +
        ENNReal.ofReal h ^ (p - 1) *
          ∫⁻ σ in Icc s (s + h), ∫⁻ r in Ico a (a + h), ‖partialT u (σ, r)‖ₑ ^ p) := by
  set H := ENNReal.ofReal h with hHdef
  have h0 : H ≠ 0 := (ENNReal.ofReal_pos.2 hh).ne'
  have htop : H ≠ ⊤ := ENNReal.ofReal_ne_top
  have hIco : volume (Ico a (a + h)) = H := by rw [Real.volume_Ico, add_sub_cancel_left]
  set c1 := H ^ (-p) *
    (∫⁻ σ in Icc s (s + h), ∫⁻ τ in Ico a (a + h), ‖u (σ, τ)‖ₑ ^ (2 : ℝ)) ^ (p / 2)
  set c3 := H ^ (p - 2) *
    ∫⁻ σ in Icc s (s + h), ∫⁻ r in Ico a (a + h), ‖partialT u (σ, r)‖ₑ ^ p
  set f : ℝ → ℝ≥0∞ := fun t => ∫⁻ r in Icc s (s + h), ‖partialS u (r, t)‖ₑ ^ p with hf
  have hfm : Measurable f :=
    (((crbox_cont_S hu).enorm.measurable.pow_const p)).lintegral_prod_left'
  have h3 : (3 : ℝ≥0∞) ^ (p - 1) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)
  calc ∫⁻ t in Ico a (a + h), ‖u (s, t)‖ₑ ^ p
      ≤ ∫⁻ t in Ico a (a + h), 3 ^ (p - 1) * (c1 + H ^ (p - 1) * f t + c3) :=
        setLIntegral_mono' measurableSet_Ico fun t ht => crbox_pow hu hp hh ht
    _ = 3 ^ (p - 1) * (c1 * H + H ^ (p - 1) * (∫⁻ t in Ico a (a + h), f t) + c3 * H) := by
        rw [lintegral_const_mul' _ _ h3,
          lintegral_add_left ((hfm.const_mul (H ^ (p - 1))).const_add c1),
          lintegral_add_left measurable_const,
          setLIntegral_const, setLIntegral_const, hIco,
          lintegral_const_mul' (H ^ (p - 1)) f (crbox_rpow_ne_top h0 htop _)]
    _ = _ := by
        have e1 : c1 * H = H ^ (1 - p) *
            (∫⁻ σ in Icc s (s + h), ∫⁻ τ in Ico a (a + h), ‖u (σ, τ)‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
          rw [mul_comm, ← mul_assoc]
          congr 1
          rw [show H * H ^ (-p) = H ^ (1 : ℝ) * H ^ (-p) by rw [ENNReal.rpow_one],
            ← ENNReal.rpow_add _ _ h0 htop]; congr 1 <;> ring
        have e3 : c3 * H = H ^ (p - 1) *
            ∫⁻ σ in Icc s (s + h), ∫⁻ r in Ico a (a + h), ‖partialT u (σ, r)‖ₑ ^ p := by
          rw [mul_comm, ← mul_assoc]
          congr 1
          rw [show H * H ^ (p - 2) = H ^ (1 : ℝ) * H ^ (p - 2) by rw [ENNReal.rpow_one],
            ← ENNReal.rpow_add _ _ h0 htop]; congr 1 <;> ring
        rw [e1, e3]

end

end CauchyRiemannIndex

-- ===== Scratch/CRBox5.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

lemma crbox_partition' (f : ℝ → ℝ≥0∞) {h : ℝ} (hh : 0 ≤ h) (k : ℕ) :
    ∫⁻ t in Ico 0 (k * h), f t =
      ∑ j ∈ Finset.range k, ∫⁻ t in Ico (j * h) (j * h + h), f t := by
  rw [crbox_partition f h hh k]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_mul, one_mul]

/-- Sum of `crbox_slice` over the `N` cells of `[0, 1)`. -/
lemma crbox_cell_sum {u : ℝ × ℝ → Vec n} (hu : ContDiff ℝ 1 u) {p : ℝ} (hp : 2 ≤ p)
    {N : ℕ} {h : ℝ} (hh : 0 < h) (hNh : (N : ℝ) * h = 1) (s : ℝ) :
    ∫⁻ t in Ico 0 1, ‖u (s, t)‖ₑ ^ p ≤ 3 ^ (p - 1) *
      (ENNReal.ofReal h ^ (1 - p) *
          (∫⁻ σ in Icc s (s + h), ∫⁻ τ in Ico 0 1, ‖u (σ, τ)‖ₑ ^ (2 : ℝ)) ^ (p / 2) +
        ENNReal.ofReal h ^ (p - 1) *
          (∫⁻ t in Ico 0 1, ∫⁻ r in Icc s (s + h), ‖partialS u (r, t)‖ₑ ^ p) +
        ENNReal.ofReal h ^ (p - 1) *
          ∫⁻ σ in Icc s (s + h), ∫⁻ r in Ico 0 1, ‖partialT u (σ, r)‖ₑ ^ p) := by
  set H := ENNReal.ofReal h
  have hI : Ico (0 : ℝ) 1 = Ico 0 (N * h) := by rw [hNh]
  have hmu : Measurable fun z : ℝ × ℝ => ‖u z‖ₑ ^ (2 : ℝ) :=
    hu.continuous.enorm.measurable.pow_const _
  have hmT : Measurable fun z : ℝ × ℝ => ‖partialT u z‖ₑ ^ p :=
    (crbox_cont_T hu).enorm.measurable.pow_const _
  -- splitting the inner integrals
  have splitσ : ∀ F : ℝ × ℝ → ℝ≥0∞, Measurable F →
      ∫⁻ σ in Icc s (s + h), ∫⁻ τ in Ico 0 1, F (σ, τ) =
        ∑ j ∈ Finset.range N, ∫⁻ σ in Icc s (s + h), ∫⁻ τ in Ico (j * h) (j * h + h), F (σ, τ) := by
    intro F hF
    rw [← lintegral_finset_sum _ fun j _ => hF.lintegral_prod_right']
    refine lintegral_congr fun σ => ?_
    rw [hI, crbox_partition' _ hh.le]
  have hG := splitσ _ hmu
  have hT := splitσ _ hmT
  have hS : ∫⁻ t in Ico 0 1, ∫⁻ r in Icc s (s + h), ‖partialS u (r, t)‖ₑ ^ p =
      ∑ j ∈ Finset.range N,
        ∫⁻ t in Ico (j * h) (j * h + h), ∫⁻ r in Icc s (s + h), ‖partialS u (r, t)‖ₑ ^ p := by
    rw [hI, crbox_partition' _ hh.le]
  have hp2 : 1 ≤ p / 2 := by linarith
  calc ∫⁻ t in Ico 0 1, ‖u (s, t)‖ₑ ^ p
      = ∑ j ∈ Finset.range N, ∫⁻ t in Ico (j * h) (j * h + h), ‖u (s, t)‖ₑ ^ p := by
        rw [hI, crbox_partition' _ hh.le]
    _ ≤ ∑ j ∈ Finset.range N, 3 ^ (p - 1) *
          (H ^ (1 - p) * (∫⁻ σ in Icc s (s + h), ∫⁻ τ in Ico (j * h) (j * h + h),
              ‖u (σ, τ)‖ₑ ^ (2 : ℝ)) ^ (p / 2) +
            H ^ (p - 1) * (∫⁻ t in Ico (j * h) (j * h + h), ∫⁻ r in Icc s (s + h),
              ‖partialS u (r, t)‖ₑ ^ p) +
            H ^ (p - 1) * ∫⁻ σ in Icc s (s + h), ∫⁻ r in Ico (j * h) (j * h + h),
              ‖partialT u (σ, r)‖ₑ ^ p) :=
        Finset.sum_le_sum fun j _ => crbox_slice hu hp hh s (j * h)
    _ = 3 ^ (p - 1) *
          (H ^ (1 - p) * ∑ j ∈ Finset.range N, (∫⁻ σ in Icc s (s + h),
              ∫⁻ τ in Ico (j * h) (j * h + h), ‖u (σ, τ)‖ₑ ^ (2 : ℝ)) ^ (p / 2) +
            H ^ (p - 1) * (∫⁻ t in Ico 0 1, ∫⁻ r in Icc s (s + h), ‖partialS u (r, t)‖ₑ ^ p) +
            H ^ (p - 1) * ∫⁻ σ in Icc s (s + h), ∫⁻ r in Ico 0 1, ‖partialT u (σ, r)‖ₑ ^ p) := by
        rw [hS, hT]
        simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    _ ≤ _ := by
        rw [hG]
        gcongr
        exact crbox_sum_rpow_le _ _ hp2

end

end CauchyRiemannIndex

-- ===== Scratch/CRBox.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

lemma crbox_cyl :
    cylMeasure = (volume : Measure ℝ).prod (volume.restrict (Ico (0 : ℝ) 1)) := by
  rw [cylMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem crbox_final (n : ℕ) (p : ℝ) (hp : 2 ≤ p) (N : ℕ)
    (hN : 1 ≤ N) (u : ℝ × ℝ → Vec n) (hu : ContDiff ℝ 1 u) :
    ∫⁻ x, ‖u x‖ₑ ^ p ∂cylMeasure ≤
      (3 : ℝ≥0∞) ^ (p - 1) *
        ((N : ℝ≥0∞) ^ (p - 1) *
            (∫⁻ s : ℝ, (∫⁻ x in Set.Icc s (s + 1 / (N : ℝ)) ×ˢ Set.Ico (0 : ℝ) 1,
              ‖u x‖ₑ ^ (2 : ℝ)) ^ (p / 2)) +
          (N : ℝ≥0∞) ^ (-p) *
            (∫⁻ x, ‖partialS u x‖ₑ ^ p ∂cylMeasure + ∫⁻ x, ‖partialT u x‖ₑ ^ p ∂cylMeasure)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set h : ℝ := 1 / (N : ℝ) with hhdef
  have hh : 0 < h := by positivity
  have hNh : (N : ℝ) * h = 1 := by rw [hhdef]; field_simp
  set H := ENNReal.ofReal h with hHdef
  have hHN : H = (N : ℝ≥0∞)⁻¹ := by
    rw [hHdef, hhdef, one_div, ENNReal.ofReal_inv_of_pos hN0, ENNReal.ofReal_natCast]
  have h0 : H ≠ 0 := (ENNReal.ofReal_pos.2 hh).ne'
  have htop : H ≠ ⊤ := ENNReal.ofReal_ne_top
  have h3 : (3 : ℝ≥0∞) ^ (p - 1) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)
  have hmu2 : Measurable fun z : ℝ × ℝ => ‖u z‖ₑ ^ (2 : ℝ) :=
    hu.continuous.enorm.measurable.pow_const _
  have hmP : Measurable fun z : ℝ × ℝ => ‖u z‖ₑ ^ p :=
    hu.continuous.enorm.measurable.pow_const _
  have hmS : Measurable fun z : ℝ × ℝ => ‖partialS u z‖ₑ ^ p :=
    (crbox_cont_S hu).enorm.measurable.pow_const _
  have hmT : Measurable fun z : ℝ × ℝ => ‖partialT u z‖ₑ ^ p :=
    (crbox_cont_T hu).enorm.measurable.pow_const _
  set g0 : ℝ → ℝ≥0∞ := fun σ => ∫⁻ τ in Ico 0 1, ‖u (σ, τ)‖ₑ ^ (2 : ℝ) with hg0def
  set g1 : ℝ → ℝ≥0∞ := fun σ => ∫⁻ r in Ico 0 1, ‖partialT u (σ, r)‖ₑ ^ p with hg1def
  have hg0 : Measurable g0 := hmu2.lintegral_prod_right'
  have hg1 : Measurable g1 := hmT.lintegral_prod_right'
  have hshift_meas : ∀ g : ℝ → ℝ≥0∞, Measurable g →
      Measurable fun s => ∫⁻ σ in Icc s (s + h), g σ := by
    intro g hg
    have : (fun s => ∫⁻ σ in Icc s (s + h), g σ) = fun s => ∫⁻ ρ in Icc 0 h, g (ρ + s) :=
      funext fun s => crbox_shift g hg s h
    rw [this]
    exact (hg.comp (measurable_snd.add measurable_fst)).lintegral_prod_right'
  have hGm : Measurable fun s => (∫⁻ σ in Icc s (s + h), g0 σ) ^ (p / 2) :=
    (hshift_meas g0 hg0).pow_const _
  have hTm := hshift_meas g1 hg1
  -- the `s`-integrals of the derivative terms
  have hTint : ∫⁻ s, ∫⁻ σ in Icc s (s + h), g1 σ = H * ∫⁻ x, ‖partialT u x‖ₑ ^ p ∂cylMeasure := by
    rw [crbox_shift_int g1 hg1 hh.le, crbox_cyl, lintegral_prod _ hmT.aemeasurable]
  have hSint : ∫⁻ s, ∫⁻ t in Ico 0 1, ∫⁻ r in Icc s (s + h), ‖partialS u (r, t)‖ₑ ^ p =
      H * ∫⁻ x, ‖partialS u x‖ₑ ^ p ∂cylMeasure := by
    have hφ : ∀ t, Measurable fun r => ‖partialS u (r, t)‖ₑ ^ p := fun t =>
      hmS.comp (measurable_id.prodMk measurable_const)
    have hK : Measurable fun z : ℝ × ℝ => ∫⁻ ρ in Icc 0 h, ‖partialS u (ρ + z.1, z.2)‖ₑ ^ p := by
      refine Measurable.lintegral_prod_right' (f := fun w : (ℝ × ℝ) × ℝ =>
        ‖partialS u (w.2 + w.1.1, w.1.2)‖ₑ ^ p) ?_
      exact hmS.comp ((measurable_snd.add (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_fst))
    calc ∫⁻ s, ∫⁻ t in Ico 0 1, ∫⁻ r in Icc s (s + h), ‖partialS u (r, t)‖ₑ ^ p
        = ∫⁻ s, ∫⁻ t in Ico 0 1, ∫⁻ ρ in Icc 0 h, ‖partialS u (ρ + s, t)‖ₑ ^ p := by
          refine lintegral_congr fun s => lintegral_congr fun t => ?_
          exact crbox_shift _ (hφ t) s h
      _ = ∫⁻ t in Ico 0 1, ∫⁻ s, ∫⁻ ρ in Icc 0 h, ‖partialS u (ρ + s, t)‖ₑ ^ p :=
          lintegral_lintegral_swap (f := fun s t => ∫⁻ ρ in Icc 0 h, ‖partialS u (ρ + s, t)‖ₑ ^ p)
            hK.aemeasurable
      _ = ∫⁻ t in Ico 0 1, H * ∫⁻ r, ‖partialS u (r, t)‖ₑ ^ p := by
          refine lintegral_congr fun t => ?_
          rw [← crbox_shift_int _ (hφ t) hh.le]
          exact lintegral_congr fun s => (crbox_shift _ (hφ t) s h).symm
      _ = H * ∫⁻ x, ‖partialS u x‖ₑ ^ p ∂cylMeasure := by
          rw [lintegral_const_mul' _ _ htop, crbox_cyl, lintegral_prod _ hmS.aemeasurable,
            lintegral_lintegral_swap (f := fun r t => ‖partialS u (r, t)‖ₑ ^ p) hmS.aemeasurable]
  have hslab : ∀ s, ∫⁻ x in Icc s (s + h) ×ˢ Ico (0 : ℝ) 1, ‖u x‖ₑ ^ (2 : ℝ) =
      ∫⁻ σ in Icc s (s + h), g0 σ := by
    intro s
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hmu2.aemeasurable]
  have hpow1 : H ^ (1 - p) = (N : ℝ≥0∞) ^ (p - 1) := by
    rw [hHN, ENNReal.inv_rpow, ← ENNReal.rpow_neg, neg_sub]
  have hpow2 : H ^ (p - 1) * H = (N : ℝ≥0∞) ^ (-p) := by
    rw [show H ^ (p - 1) * H = H ^ (p - 1) * H ^ (1 : ℝ) by rw [ENNReal.rpow_one],
      ← ENNReal.rpow_add _ _ h0 htop, sub_add_cancel, hHN, ENNReal.inv_rpow, ← ENNReal.rpow_neg]
  calc ∫⁻ x, ‖u x‖ₑ ^ p ∂cylMeasure
      = ∫⁻ s, ∫⁻ t in Ico 0 1, ‖u (s, t)‖ₑ ^ p := by
        rw [crbox_cyl, lintegral_prod _ hmP.aemeasurable]
    _ ≤ ∫⁻ s, 3 ^ (p - 1) *
          (H ^ (1 - p) * (∫⁻ σ in Icc s (s + h), g0 σ) ^ (p / 2) +
            (H ^ (p - 1) * (∫⁻ σ in Icc s (s + h), g1 σ) +
              H ^ (p - 1) * (∫⁻ t in Ico 0 1, ∫⁻ r in Icc s (s + h),
                ‖partialS u (r, t)‖ₑ ^ p))) := by
        refine lintegral_mono fun s => (crbox_cell_sum hu hp hh hNh s).trans (le_of_eq ?_)
        ring
    _ = 3 ^ (p - 1) *
          (H ^ (1 - p) * (∫⁻ s, (∫⁻ σ in Icc s (s + h), g0 σ) ^ (p / 2)) +
            (H ^ (p - 1) * (H * ∫⁻ x, ‖partialT u x‖ₑ ^ p ∂cylMeasure) +
              H ^ (p - 1) * (H * ∫⁻ x, ‖partialS u x‖ₑ ^ p ∂cylMeasure))) := by
        rw [lintegral_const_mul' _ _ h3, lintegral_add_left (hGm.const_mul _),
          lintegral_add_left (hTm.const_mul _),
          lintegral_const_mul' _ _ (crbox_rpow_ne_top h0 htop _),
          lintegral_const_mul' _ _ (crbox_rpow_ne_top h0 htop _),
          lintegral_const_mul' _ _ (crbox_rpow_ne_top h0 htop _), hTint, hSint]
    _ = _ := by
        simp_rw [hslab]
        rw [hpow1]
        simp only [← mul_assoc, hpow2]
        ring

end

end CauchyRiemannIndex

open scoped ENNReal in
open CauchyRiemannIndex MeasureTheory in
theorem solution (n : ℕ) (p : ℝ) (hp : 2 ≤ p) (N : ℕ)
    (hN : 1 ≤ N) (u : ℝ × ℝ → Vec n) (hu : ContDiff ℝ 1 u) :
    ∫⁻ x, ‖u x‖ₑ ^ p ∂cylMeasure ≤
      (3 : ℝ≥0∞) ^ (p - 1) *
        ((N : ℝ≥0∞) ^ (p - 1) *
            (∫⁻ s : ℝ, (∫⁻ x in Set.Icc s (s + 1 / (N : ℝ)) ×ˢ Set.Ico (0 : ℝ) 1,
              ‖u x‖ₑ ^ (2 : ℝ)) ^ (p / 2)) +
          (N : ℝ≥0∞) ^ (-p) *
            (∫⁻ x, ‖partialS u x‖ₑ ^ p ∂cylMeasure + ∫⁻ x, ‖partialT u x‖ₑ ^ p ∂cylMeasure)) :=
  crbox_final n p hp N hN u hu
