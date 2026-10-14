-- Prove2me | solution 1 for DbarRegularity.weakType_one_integral_mul_sub_of_hormander
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T15:54:09.004503+00:00
-- url     : https://prove2.me/submissions/87c87fa9-d9f1-4731-bddb-b5fd30f96fd9

import Definitions.Def_DbarRegularity_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Theorems.Thm_DbarRegularity_exists_good_bad_decomposition
import Theorems.Thm_DbarRegularity_ae_enorm_integral_mul_tsum_le
import Theorems.Thm_DbarRegularity_lintegral_compl_ball_integral_mul_sub_le
import Theorems.Thm_DbarRegularity_ae_integrable_mul_sub_of_memLp_two_of_integrable
import Theorems.Thm_DbarRegularity_aestronglyMeasurable_integral_mul_sub
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov



namespace DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal NNReal

/-- Weak type `(1, 1)` for convolution with an `L²` kernel `K` on `ℝ^d` that satisfies the
Hörmander condition with constant `B₁` and is bounded on `L²` with norm `B₂`:
`|{|K * f| > α}| ≤ C (1 + B₁ + B₂²) ‖f‖₁ / α`, with `C` depending only on `d`. -/
theorem weakType_one_integral_mul_sub_of_hormander {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ≥0, ∀ (K : EuclideanSpace ℝ (Fin d) → ℂ), MemLp K 2 volume → ∀ B₁ B₂ : ℝ≥0,
      (∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ B₁) →
      (∀ g, MemLp g 2 volume →
        eLpNorm (fun x => ∫ y, K (x - y) * g y) 2 volume ≤ B₂ * eLpNorm g 2 volume) →
      ∀ f, MemLp f 1 volume → ∀ α : ℝ≥0, 0 < α →
        volume {x | (α : ℝ≥0∞) < ‖∫ y, K (x - y) * f y‖ₑ} ≤
          ((C * (1 + B₁ + B₂ ^ 2) : ℝ≥0) : ℝ≥0∞) / α * eLpNorm f 1 volume := by
  obtain ⟨Ccz, hCtop, hcz⟩ := exists_good_bad_decomposition hd
  lift Ccz to ℝ≥0 using hCtop with Cn
  refine ⟨Cn + 4 + 4 * 2 ^ d, ?_⟩
  intro K hK B₁ B₂ hH hL2 f hf α hα
  have hf1 : Integrable f volume := memLp_one_iff_integrable.1 hf
  have hαr : (0 : ℝ) < α := by exact_mod_cast hα
  obtain ⟨ι, hι, c, r, b, hbint, hb0, hsupp, hdisj, hBint, hgb, hg1, hsumb, hball⟩ :=
    hcz f hf1 α hαr
  have ha0 : (α : ℝ≥0∞) ≠ 0 := by simp [hα.ne']
  have hatop : (α : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hNtop : eLpNorm f 1 volume ≠ ⊤ := hf.2.ne
  have hgi : Integrable (fun x => f x - ∑' k, b k x) volume := hf1.sub hBint
  have rpow2 : ∀ z : ℝ≥0∞, z ^ (2 : ℝ) = z ^ 2 := fun z => by
    rw [← ENNReal.rpow_natCast]; norm_num
  have ha2 : (α : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.div_pos ha0 ENNReal.ofNat_ne_top).ne'
  have ha2' : (α : ℝ≥0∞) / 2 ≠ ⊤ := ENNReal.div_ne_top hatop two_ne_zero
  have hinv2 : ((α : ℝ≥0∞) / 2)⁻¹ = 2 * (α : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.inv_div (Or.inl ENNReal.ofNat_ne_top) (Or.inl two_ne_zero), div_eq_mul_inv]
  -- splitting `K * f = K * g + K * (∑ bₖ)`
  have hsplit : ∀ᵐ x, ‖∫ y, K (x - y) * f y‖ₑ ≤
      ‖∫ y, K (x - y) * (f y - ∑' k, b k y)‖ₑ + ‖∫ y, K (x - y) * ∑' k, b k y‖ₑ := by
    filter_upwards [ae_integrable_mul_sub_of_memLp_two_of_integrable hK hgi,
      ae_integrable_mul_sub_of_memLp_two_of_integrable hK hBint] with x h1 h2
    have : ∫ y, K (x - y) * f y =
        (∫ y, K (x - y) * (f y - ∑' k, b k y)) + ∫ y, K (x - y) * ∑' k, b k y := by
      rw [← integral_add h1 h2]; congr 1; funext y; ring
    rw [this]; exact enorm_add_le _ _
  set E : Set (EuclideanSpace ℝ (Fin d)) := ⋃ k, ball (c k) (2 * r k) with hE
  have hEm : MeasurableSet E := MeasurableSet.iUnion fun k => measurableSet_ball
  have hincl : ({x | (α : ℝ≥0∞) < ‖∫ y, K (x - y) * f y‖ₑ} : Set (EuclideanSpace ℝ (Fin d)))
      ≤ᵐ[volume] (({x | (α : ℝ≥0∞) / 2 < ‖∫ y, K (x - y) * (f y - ∑' k, b k y)‖ₑ} ∪ E) ∪
        ({x | (α : ℝ≥0∞) / 2 < ‖∫ y, K (x - y) * ∑' k, b k y‖ₑ} ∩ Eᶜ) :
          Set (EuclideanSpace ℝ (Fin d))) := by
    filter_upwards [hsplit] with x hx hxa
    have hxa' : (α : ℝ≥0∞) < ‖∫ y, K (x - y) * f y‖ₑ := hxa
    show x ∈ (_ : Set (EuclideanSpace ℝ (Fin d)))
    by_contra hcon
    simp only [mem_union, mem_inter_iff, mem_compl_iff, mem_setOf_eq, not_or, not_and,
      not_lt] at hcon
    have h3 := hx.trans (add_le_add hcon.1.1 (not_lt.1 fun h => hcon.2 h hcon.1.2))
    rw [ENNReal.add_halves] at h3
    exact absurd hxa' (not_lt.2 h3)
  -- the good part
  have hgM : ∀ᵐ x, ‖f x - ∑' k, b k x‖ₑ ≤ 2 ^ d * (α : ℝ≥0∞) := by
    filter_upwards [hgb] with x hx
    rw [← ofReal_norm_eq_enorm]
    calc ENNReal.ofReal ‖f x - ∑' k, b k x‖ ≤ ENNReal.ofReal (2 ^ d * α) :=
          ENNReal.ofReal_le_ofReal hx
      _ = 2 ^ d * (α : ℝ≥0∞) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
            ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
  have hg2 : ∫⁻ x, ‖f x - ∑' k, b k x‖ₑ ^ 2 ≤ 2 ^ d * (α : ℝ≥0∞) * eLpNorm f 1 volume := by
    calc ∫⁻ x, ‖f x - ∑' k, b k x‖ₑ ^ 2
        ≤ ∫⁻ x, 2 ^ d * (α : ℝ≥0∞) * ‖f x - ∑' k, b k x‖ₑ :=
          lintegral_mono_ae (hgM.mono fun x hx => by rw [pow_two]; exact mul_le_mul' hx le_rfl)
      _ = 2 ^ d * (α : ℝ≥0∞) * ∫⁻ x, ‖f x - ∑' k, b k x‖ₑ :=
          lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
            hatop)
      _ ≤ 2 ^ d * (α : ℝ≥0∞) * eLpNorm f 1 volume := by
          gcongr; rw [← eLpNorm_one_eq_lintegral_enorm]; exact hg1
  have hg2' : eLpNorm (fun x => f x - ∑' k, b k x) 2 volume ^ 2 =
      ∫⁻ x, ‖f x - ∑' k, b k x‖ₑ ^ 2 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, rpow2]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have hgL2 : MemLp (fun x => f x - ∑' k, b k x) 2 volume := by
    refine ⟨hgi.1, ?_⟩
    have h1 : eLpNorm (fun x => f x - ∑' k, b k x) 2 volume ^ 2 < ⊤ := by
      rw [hg2']
      exact hg2.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top
        (ENNReal.pow_lt_top ENNReal.ofNat_lt_top) hatop.lt_top) hNtop.lt_top)
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h] at h1; simp at h1
  have hI : volume {x | (α : ℝ≥0∞) / 2 < ‖∫ y, K (x - y) * (f y - ∑' k, b k y)‖ₑ} ≤
      4 * 2 ^ d * (B₂ : ℝ≥0∞) ^ 2 * (α : ℝ≥0∞)⁻¹ * eLpNorm f 1 volume := by
    have hTgm : AEStronglyMeasurable (fun x => ∫ y, K (x - y) * (f y - ∑' k, b k y)) volume :=
      aestronglyMeasurable_integral_mul_sub K _ hK.1 hgi.1
    have cheb := meas_ge_le_mul_pow_eLpNorm_enorm volume (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      hTgm ha2 (fun h => (ha2' h).elim)
    simp only [ENNReal.toReal_ofNat, rpow2] at cheb
    calc volume {x | (α : ℝ≥0∞) / 2 < ‖∫ y, K (x - y) * (f y - ∑' k, b k y)‖ₑ}
        ≤ volume {x | (α : ℝ≥0∞) / 2 ≤ ‖∫ y, K (x - y) * (f y - ∑' k, b k y)‖ₑ} :=
          measure_mono (setOf_subset_setOf.2 fun x hx => le_of_lt hx)
      _ ≤ ((α : ℝ≥0∞) / 2)⁻¹ ^ 2 *
            eLpNorm (fun x => ∫ y, K (x - y) * (f y - ∑' k, b k y)) 2 volume ^ 2 := cheb
      _ ≤ ((α : ℝ≥0∞) / 2)⁻¹ ^ 2 *
            ((B₂ : ℝ≥0∞) * eLpNorm (fun x => f x - ∑' k, b k x) 2 volume) ^ 2 := by
          gcongr; exact hL2 _ hgL2
      _ = ((α : ℝ≥0∞) / 2)⁻¹ ^ 2 * (B₂ : ℝ≥0∞) ^ 2 *
            eLpNorm (fun x => f x - ∑' k, b k x) 2 volume ^ 2 := by ring
      _ ≤ ((α : ℝ≥0∞) / 2)⁻¹ ^ 2 * (B₂ : ℝ≥0∞) ^ 2 *
            (2 ^ d * (α : ℝ≥0∞) * eLpNorm f 1 volume) := by
          gcongr; rw [hg2']; exact hg2
      _ = 4 * 2 ^ d * (B₂ : ℝ≥0∞) ^ 2 * (α : ℝ≥0∞)⁻¹ * eLpNorm f 1 volume *
            ((α : ℝ≥0∞)⁻¹ * α) := by rw [hinv2]; ring
      _ = 4 * 2 ^ d * (B₂ : ℝ≥0∞) ^ 2 * (α : ℝ≥0∞)⁻¹ * eLpNorm f 1 volume := by
          rw [ENNReal.inv_mul_cancel ha0 hatop, mul_one]
  -- the exceptional set
  have hII : volume E ≤ (Cn : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ * eLpNorm f 1 volume := by
    calc volume E ≤ ∑' k, volume (ball (c k) (2 * r k)) := measure_iUnion_le _
      _ ≤ (Cn : ℝ≥0∞) / ENNReal.ofReal α * eLpNorm f 1 volume := hball
      _ = (Cn : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ * eLpNorm f 1 volume := by
          rw [ENNReal.ofReal_coe_nnreal, div_eq_mul_inv]
  -- the bad part off the exceptional set
  have hTb : ∫⁻ x in Eᶜ, ‖∫ y, K (x - y) * ∑' k, b k y‖ₑ ≤
      (B₁ : ℝ≥0∞) * (2 * eLpNorm f 1 volume) := by
    calc ∫⁻ x in Eᶜ, ‖∫ y, K (x - y) * ∑' k, b k y‖ₑ
        ≤ ∫⁻ x in Eᶜ, ∑' k, ‖∫ y, K (x - y) * b k y‖ₑ :=
          lintegral_mono_ae (ae_restrict_of_ae
            (ae_enorm_integral_mul_tsum_le hK b hbint hdisj hBint))
      _ = ∑' k, ∫⁻ x in Eᶜ, ‖∫ y, K (x - y) * b k y‖ₑ :=
          lintegral_tsum fun k =>
            (aestronglyMeasurable_integral_mul_sub K (b k) hK.1 (hbint k).1).enorm.restrict
      _ ≤ ∑' k, ∫⁻ x in (ball (c k) (2 * r k))ᶜ, ‖∫ y, K (x - y) * b k y‖ₑ :=
          ENNReal.tsum_le_tsum fun k => lintegral_mono_set
            (compl_subset_compl.2 (subset_iUnion (fun k => ball (c k) (2 * r k)) k))
      _ ≤ ∑' k, (B₁ : ℝ≥0∞) * eLpNorm (b k) 1 volume := ENNReal.tsum_le_tsum fun k => by
          have := lintegral_compl_ball_integral_mul_sub_le K hK.1 (B₁ : ℝ)
            (by simpa only [ENNReal.ofReal_coe_nnreal] using hH) (b k) (hbint k) (hb0 k) (c k)
            (r k) (hsupp k)
          simpa only [ENNReal.ofReal_coe_nnreal] using this
      _ = (B₁ : ℝ≥0∞) * ∑' k, eLpNorm (b k) 1 volume := ENNReal.tsum_mul_left
      _ ≤ (B₁ : ℝ≥0∞) * (2 * eLpNorm f 1 volume) := by gcongr
  have hIII : volume ({x | (α : ℝ≥0∞) / 2 < ‖∫ y, K (x - y) * ∑' k, b k y‖ₑ} ∩ Eᶜ) ≤
      4 * (B₁ : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ * eLpNorm f 1 volume := by
    rw [← Measure.restrict_apply' hEm.compl]
    calc volume.restrict Eᶜ {x | (α : ℝ≥0∞) / 2 < ‖∫ y, K (x - y) * ∑' k, b k y‖ₑ}
        ≤ volume.restrict Eᶜ {x | (α : ℝ≥0∞) / 2 ≤ ‖∫ y, K (x - y) * ∑' k, b k y‖ₑ} :=
          measure_mono (setOf_subset_setOf.2 fun x hx => le_of_lt hx)
      _ ≤ (∫⁻ x in Eᶜ, ‖∫ y, K (x - y) * ∑' k, b k y‖ₑ) / ((α : ℝ≥0∞) / 2) :=
          meas_ge_le_lintegral_div
            (aestronglyMeasurable_integral_mul_sub K _ hK.1 hBint.1).enorm.restrict ha2 ha2'
      _ ≤ (B₁ : ℝ≥0∞) * (2 * eLpNorm f 1 volume) / ((α : ℝ≥0∞) / 2) := by gcongr
      _ = 4 * (B₁ : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ * eLpNorm f 1 volume := by
          rw [div_eq_mul_inv, hinv2]; ring
  have key : (4 * 2 ^ d * B₂ ^ 2 + Cn + 4 * B₁ : ℝ≥0) ≤
      (Cn + 4 + 4 * 2 ^ d) * (1 + B₁ + B₂ ^ 2) := by
    rw [← NNReal.coe_le_coe]; push_cast
    have hc : (0 : ℝ) ≤ Cn := NNReal.coe_nonneg _
    have hx : (0 : ℝ) ≤ B₁ := NNReal.coe_nonneg _
    have hy : (0 : ℝ) ≤ (B₂ : ℝ) ^ 2 := sq_nonneg _
    have ht : (0 : ℝ) ≤ 2 ^ d := by positivity
    nlinarith [mul_nonneg hc hx, mul_nonneg hc hy, mul_nonneg ht hx, mul_nonneg ht hy]
  calc volume {x | (α : ℝ≥0∞) < ‖∫ y, K (x - y) * f y‖ₑ}
      ≤ volume (({x | (α : ℝ≥0∞) / 2 < ‖∫ y, K (x - y) * (f y - ∑' k, b k y)‖ₑ} ∪ E) ∪
          ({x | (α : ℝ≥0∞) / 2 < ‖∫ y, K (x - y) * ∑' k, b k y‖ₑ} ∩ Eᶜ)) :=
        measure_mono_ae hincl
    _ ≤ volume {x | (α : ℝ≥0∞) / 2 < ‖∫ y, K (x - y) * (f y - ∑' k, b k y)‖ₑ} + volume E +
          volume ({x | (α : ℝ≥0∞) / 2 < ‖∫ y, K (x - y) * ∑' k, b k y‖ₑ} ∩ Eᶜ) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ 4 * 2 ^ d * (B₂ : ℝ≥0∞) ^ 2 * (α : ℝ≥0∞)⁻¹ * eLpNorm f 1 volume +
          (Cn : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ * eLpNorm f 1 volume +
          4 * (B₁ : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ * eLpNorm f 1 volume := by gcongr
    _ = ((4 * 2 ^ d * B₂ ^ 2 + Cn + 4 * B₁ : ℝ≥0) : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ *
          eLpNorm f 1 volume := by
        push_cast; ring
    _ ≤ (((Cn + 4 + 4 * 2 ^ d) * (1 + B₁ + B₂ ^ 2) : ℝ≥0) : ℝ≥0∞) / α *
          eLpNorm f 1 volume := by
        rw [div_eq_mul_inv]; gcongr
        all_goals exact_mod_cast key

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem solution {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ≥0, ∀ (K : EuclideanSpace ℝ (Fin d) → ℂ), MemLp K 2 volume → ∀ B₁ B₂ : ℝ≥0,
      (∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ B₁) →
      (∀ g, MemLp g 2 volume →
        eLpNorm (fun x => ∫ y, K (x - y) * g y) 2 volume ≤ B₂ * eLpNorm g 2 volume) →
      ∀ f, MemLp f 1 volume → ∀ α : ℝ≥0, 0 < α →
        volume {x | (α : ℝ≥0∞) < ‖∫ y, K (x - y) * f y‖ₑ} ≤
          ((C * (1 + B₁ + B₂ ^ 2) : ℝ≥0) : ℝ≥0∞) / α * eLpNorm f 1 volume :=
  weakType_one_integral_mul_sub_of_hormander hd
