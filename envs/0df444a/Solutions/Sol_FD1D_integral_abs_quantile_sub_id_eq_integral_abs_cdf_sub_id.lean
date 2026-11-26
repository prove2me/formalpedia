-- Prove2me | solution 1 for FD1D.integral_abs_quantile_sub_id_eq_integral_abs_cdf_sub_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:14.593248+00:00
-- url     : https://prove2.me/submissions/a931f567-0b05-4aaa-82bc-0be7ea771cef

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_HaarSupportNested_trans
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


section
namespace FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace DyadicMass
end DyadicMass
namespace HaarTerm
end HaarTerm
namespace DyadicMass
end DyadicMass
namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]
end FiniteLaw
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace DyadicMass
end DyadicMass
private theorem integral_abs_leStep_right
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    (∫ z in Icc (0 : ℝ) 1, |leStep a z - leStep b z|) = |a - b| := by
  rcases le_total a b with hab | hba
  · have heq : EqOn
        (fun z : ℝ => |leStep a z - leStep b z|)
        ((Ico a b).indicator (fun _ : ℝ => 1)) (Icc (0 : ℝ) 1) := by
      intro z _
      by_cases haz : a ≤ z
      · by_cases hbz : b ≤ z
        · have hnot : z ∉ Ico a b := fun h => (not_lt_of_ge hbz) h.2
          simp [leStep, haz, hbz, hnot]
        · have hmem : z ∈ Ico a b := ⟨haz, lt_of_not_ge hbz⟩
          simp [leStep, haz, hbz, hmem]
      · have hbz : ¬b ≤ z := fun hbz => haz (hab.trans hbz)
        have hnot : z ∉ Ico a b := fun h => haz h.1
        simp [leStep, haz, hbz, hnot]
    rw [setIntegral_congr_fun measurableSet_Icc heq]
    rw [setIntegral_indicator measurableSet_Ico]
    have hinter : Icc (0 : ℝ) 1 ∩ Ico a b = Ico a b := by
      apply inter_eq_right.mpr
      intro z hz
      exact ⟨ha.1.trans hz.1, hz.2.le.trans hb.2⟩
    rw [hinter]
    simp [Real.volume_Ico, measureReal_def, hab,
      abs_of_nonpos (sub_nonpos.mpr hab)]
  · have heq : EqOn
        (fun z : ℝ => |leStep a z - leStep b z|)
        ((Ico b a).indicator (fun _ : ℝ => 1)) (Icc (0 : ℝ) 1) := by
      intro z _
      by_cases hbz : b ≤ z
      · by_cases haz : a ≤ z
        · have hnot : z ∉ Ico b a := fun h => (not_lt_of_ge haz) h.2
          simp [leStep, haz, hbz, hnot]
        · have hmem : z ∈ Ico b a := ⟨hbz, lt_of_not_ge haz⟩
          simp [leStep, haz, hbz, hmem]
      · have haz : ¬a ≤ z := fun haz => hbz (hba.trans haz)
        have hnot : z ∉ Ico b a := fun h => hbz h.1
        simp [leStep, haz, hbz, hnot]
    rw [setIntegral_congr_fun measurableSet_Icc heq]
    rw [setIntegral_indicator measurableSet_Ico]
    have hinter : Icc (0 : ℝ) 1 ∩ Ico b a = Ico b a := by
      apply inter_eq_right.mpr
      intro z hz
      exact ⟨hb.1.trans hz.1, hz.2.le.trans ha.2⟩
    rw [hinter]
    simp [Real.volume_Ico, measureReal_def, hba,
      abs_of_nonneg (sub_nonneg.mpr hba)]
private theorem integral_abs_leStep_left
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    (∫ z in Icc (0 : ℝ) 1, |leStep z a - leStep z b|) = |a - b| := by
  rcases le_total a b with hab | hba
  · have heq : EqOn
        (fun z : ℝ => |leStep z a - leStep z b|)
        ((Ioc a b).indicator (fun _ : ℝ => 1)) (Icc (0 : ℝ) 1) := by
      intro z _
      by_cases hza : z ≤ a
      · have hzb : z ≤ b := hza.trans hab
        have hnot : z ∉ Ioc a b := fun h => (not_lt_of_ge hza) h.1
        simp [leStep, hza, hzb, hnot]
      · by_cases hzb : z ≤ b
        · have hmem : z ∈ Ioc a b := ⟨lt_of_not_ge hza, hzb⟩
          simp [leStep, hza, hzb, hmem]
        · have hnot : z ∉ Ioc a b := fun h => hzb h.2
          simp [leStep, hza, hzb, hnot]
    rw [setIntegral_congr_fun measurableSet_Icc heq]
    rw [setIntegral_indicator measurableSet_Ioc]
    have hinter : Icc (0 : ℝ) 1 ∩ Ioc a b = Ioc a b := by
      apply inter_eq_right.mpr
      intro z hz
      exact ⟨ha.1.trans hz.1.le, hz.2.trans hb.2⟩
    rw [hinter]
    simp [Real.volume_Ioc, measureReal_def, hab,
      abs_of_nonpos (sub_nonpos.mpr hab)]
  · have heq : EqOn
        (fun z : ℝ => |leStep z a - leStep z b|)
        ((Ioc b a).indicator (fun _ : ℝ => 1)) (Icc (0 : ℝ) 1) := by
      intro z _
      by_cases hzb : z ≤ b
      · have hza : z ≤ a := hzb.trans hba
        have hnot : z ∉ Ioc b a := fun h => (not_lt_of_ge hzb) h.1
        simp [leStep, hza, hzb, hnot]
      · by_cases hza : z ≤ a
        · have hmem : z ∈ Ioc b a := ⟨lt_of_not_ge hzb, hza⟩
          simp [leStep, hza, hzb, hmem]
        · have hnot : z ∉ Ioc b a := fun h => hza h.2
          simp [leStep, hza, hzb, hnot]
    rw [setIntegral_congr_fun measurableSet_Icc heq]
    rw [setIntegral_indicator measurableSet_Ioc]
    have hinter : Icc (0 : ℝ) 1 ∩ Ioc b a = Ioc b a := by
      apply inter_eq_right.mpr
      intro z hz
      exact ⟨hb.1.trans hz.1.le, hz.2.trans ha.2⟩
    rw [hinter]
    simp [Real.volume_Ioc, measureReal_def, hba,
      abs_of_nonneg (sub_nonneg.mpr hba)]
namespace MonotoneQuantilePolicy
end MonotoneQuantilePolicy
namespace FiniteLaw
end FiniteLaw
end
end FD1D
end

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace FD1D
theorem _root_.solution
    {F T : ℝ → ℝ}
    (_hF : Measurable F) (hT : Measurable T)
    (hF01 : MapsTo F (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hT01 : MapsTo T (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hgc : ∀ u ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) 1,
      T u ≤ z ↔ u ≤ F z) :
    (∫ u in Icc (0 : ℝ) 1, |T u - u|) =
      ∫ z in Icc (0 : ℝ) 1, |F z - z| := by
  let k : ℝ → ℝ → ℝ := fun u z => |leStep (T u) z - leStep u z|
  have hk_meas : Measurable (Function.uncurry k) := by
    have h₁ : Measurable (fun p : ℝ × ℝ => leStep (T p.1) p.2) := by
      apply Measurable.ite
      · exact measurableSet_le (hT.comp measurable_fst) measurable_snd
      · exact measurable_const
      · exact measurable_const
    have h₂ : Measurable (fun p : ℝ × ℝ => leStep p.1 p.2) := by
      apply Measurable.ite
      · exact measurableSet_le measurable_fst measurable_snd
      · exact measurable_const
      · exact measurable_const
    exact (h₁.sub h₂).abs
  have hk_on : IntegrableOn (Function.uncurry k)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (volume.prod volume) := by
    apply Measure.integrableOn_of_bounded
      (by
        rw [Measure.prod_prod]
        norm_num [Real.volume_Icc])
      hk_meas.aestronglyMeasurable (M := 1)
    filter_upwards with p
    change ‖|leStep (T p.1) p.2 - leStep p.1 p.2|‖ ≤ 1
    rw [Real.norm_eq_abs, abs_abs]
    unfold leStep
    split_ifs <;> norm_num
  have hk : Integrable (Function.uncurry k)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod
        (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hk_on
  calc
    (∫ u in Icc (0 : ℝ) 1, |T u - u|)
        = ∫ u in Icc (0 : ℝ) 1, ∫ z in Icc (0 : ℝ) 1, k u z := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro u hu
          exact (integral_abs_leStep_right (hT01 hu) hu).symm
    _ = ∫ z in Icc (0 : ℝ) 1, ∫ u in Icc (0 : ℝ) 1, k u z :=
      integral_integral_swap hk
    _ = ∫ z in Icc (0 : ℝ) 1, |F z - z| := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro z hz
      change (∫ u in Icc (0 : ℝ) 1, k u z) = |F z - z|
      rw [← integral_abs_leStep_left (hF01 hz) hz]
      apply setIntegral_congr_fun measurableSet_Icc
      intro u hu
      dsimp only [k]
      unfold leStep
      rw [if_congr (hgc u hu z hz)] <;> rfl
end FD1D
