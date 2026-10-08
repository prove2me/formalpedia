-- Prove2me | solution 1 for AvramDividend.Classical.positiveLaplace_cumulative_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T22:26:36.458068+00:00
-- url     : https://prove2.me/submissions/507ba66a-37ca-4703-beaf-ba6a244a2597

import Mathlib
import Theorems.Thm_AvramDividend_Classical_positiveLIntegral_exp_neg_mul_Ioi

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal
open AvramDividend.Classical

theorem solution
    (β : Measure ℝ) [SFinite β] (s : ℝ) (hs : 0 < s)
    (hsupp : β (Iio 0) = 0) :
    (∫⁻ x : ℝ in Ioi 0,
      ENNReal.ofReal (Real.exp (-s * x)) * β (Iic x)) =
      ENNReal.ofReal (1 / s) *
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂β) := by
  let w : ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (-s * x))
  let G : ℝ → ℝ → ℝ≥0∞ := fun x z =>
    ({p : ℝ × ℝ | p.2 ≤ p.1}.indicator
      (fun p : ℝ × ℝ => w p.1) (x, z))

  have hw : Measurable w := by
    dsimp [w]
    fun_prop
  have hrel : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  have hG : Measurable (Function.uncurry G) := by
    have hbase : Measurable (fun p : ℝ × ℝ => w p.1) :=
      hw.comp measurable_fst
    have hind :
        Measurable
          ({p : ℝ × ℝ | p.2 ≤ p.1}.indicator
            (fun p : ℝ × ℝ => w p.1)) :=
      hbase.indicator hrel
    have hfun :
        Function.uncurry G =
          {p : ℝ × ℝ | p.2 ≤ p.1}.indicator
            (fun p : ℝ × ℝ => w p.1) := by
      funext p
      rcases p with ⟨x, z⟩
      rfl
    rw [hfun]
    exact hind

  have hG_Iic (x z : ℝ) :
      G x z = (Iic x).indicator (fun _ : ℝ => w x) z := by
    by_cases hzx : z ≤ x <;> simp [G, hzx]
  have hG_Ici (z : ℝ) :
      (fun x : ℝ => G x z) = (Ici z).indicator w := by
    funext x
    by_cases hzx : z ≤ x <;> simp [G, hzx]

  have hcum (x : ℝ) :
      (∫⁻ z : ℝ, G x z ∂β) = w x * β (Iic x) := by
    calc
      (∫⁻ z : ℝ, G x z ∂β) =
          ∫⁻ z : ℝ, (Iic x).indicator (fun _ : ℝ => w x) z ∂β := by
            apply lintegral_congr
            intro z
            exact hG_Iic x z
      _ = ∫⁻ _z : ℝ in Iic x, w x ∂β := by
            rw [lintegral_indicator measurableSet_Iic]
      _ = w x * β (Iic x) := setLIntegral_const (Iic x) (w x)

  have hnonneg : ∀ᵐ z : ℝ ∂β, 0 ≤ z := by
    exact (measure_eq_zero_iff_ae_notMem.mp hsupp).mono
      (fun z hz => le_of_not_gt (by simpa only [mem_Iio] using hz))

  have htail (z : ℝ) (hz : 0 ≤ z) :
      (∫⁻ x : ℝ in Ioi 0, G x z) =
        ENNReal.ofReal (Real.exp (-s * z) / s) := by
    rw [hG_Ici z]
    rw [lintegral_indicator measurableSet_Ici]
    rw [Measure.restrict_restrict measurableSet_Ici]
    by_cases hz0 : z = 0
    · subst z
      have hset : Ici (0 : ℝ) ∩ Ioi 0 = Ioi 0 := by
        ext x
        simp only [mem_inter_iff, mem_Ici, mem_Ioi]
        constructor
        · intro hx
          exact hx.2
        · intro hx
          exact ⟨le_of_lt hx, hx⟩
      rw [hset]
      simpa [w] using positiveLIntegral_exp_neg_mul_Ioi s 0 hs
    · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      have hset : Ici z ∩ Ioi 0 = Ici z := by
        ext x
        simp only [mem_inter_iff, mem_Ici, mem_Ioi]
        constructor
        · intro hx
          exact hx.1
        · intro hx
          exact ⟨hx, hzpos.trans_le hx⟩
      rw [hset]
      change (∫⁻ x : ℝ, w x ∂volume.restrict (Ici z)) =
        ENNReal.ofReal (Real.exp (-s * z) / s)
      rw [← MeasureTheory.restrict_Ioi_eq_restrict_Ici]
      simpa [w] using positiveLIntegral_exp_neg_mul_Ioi s z hs

  change
    (∫⁻ x : ℝ in Ioi 0, w x * β (Iic x)) =
      ENNReal.ofReal (1 / s) * (∫⁻ z : ℝ, w z ∂β)
  calc
    (∫⁻ x : ℝ in Ioi 0, w x * β (Iic x)) =
        ∫⁻ x : ℝ in Ioi 0, ∫⁻ z : ℝ, G x z ∂β := by
          apply lintegral_congr
          intro x
          exact (hcum x).symm
    _ = ∫⁻ z : ℝ, (∫⁻ x : ℝ in Ioi 0, G x z) ∂β := by
          exact lintegral_lintegral_swap
            (μ := volume.restrict (Ioi (0 : ℝ))) (ν := β)
            hG.aemeasurable
    _ = ∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z) / s) ∂β := by
          apply lintegral_congr_ae
          exact hnonneg.mono (fun z hz => htail z hz)
    _ = ∫⁻ z : ℝ, ENNReal.ofReal (1 / s) * w z ∂β := by
          apply lintegral_congr
          intro z
          dsimp [w]
          calc
            ENNReal.ofReal (Real.exp (-s * z) / s) =
                ENNReal.ofReal (s⁻¹ * Real.exp (-s * z)) := by
                  congr 1
                  simp [div_eq_mul_inv, mul_comm]
            _ = ENNReal.ofReal s⁻¹ *
                ENNReal.ofReal (Real.exp (-s * z)) :=
                  ENNReal.ofReal_mul (inv_nonneg.mpr hs.le)
            _ = ENNReal.ofReal (1 / s) *
                ENNReal.ofReal (Real.exp (-s * z)) := by
                  simp [one_div]
    _ = ENNReal.ofReal (1 / s) * (∫⁻ z : ℝ, w z ∂β) := by
          rw [lintegral_const_mul'
            (ENNReal.ofReal (1 / s)) w ENNReal.ofReal_ne_top]
