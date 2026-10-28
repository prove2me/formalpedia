-- Prove2me | solution 1 for ExploreFirst.Relative.jensen_ratio
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:48:48.530149+00:00
-- url     : https://prove2.me/submissions/6f6739ab-5031-499b-916a-78f34a2c30fb

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_ExploreFirst_Relative_Setting

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace Aux_EFRJ
open ExploreFirst.Relative

lemma pp_ge {K T : ℕ} (a : Fin K) (h : BanditHistory K T) : 1 ≤ pullsPlus a h :=
  le_max_right _ _

lemma pp_le {K T : ℕ} (a : Fin K) (h : BanditHistory K T) : pullsPlus a h ≤ T + 1 := by
  unfold pullsPlus
  have : armPullCount a h ≤ T := by
    unfold armPullCount
    calc _ ≤ (Finset.univ : Finset (Fin T)).card := Finset.card_le_univ _
      _ = T := by simp
  apply max_le
  · have : (armPullCount a h : ℝ) ≤ T := by exact_mod_cast this
    linarith
  · have : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    linarith

lemma pp_meas {K T : ℕ} (a : Fin K) : Measurable (fun h : BanditHistory K T => pullsPlus a h) := by
  have hc : Measurable (fun h : BanditHistory K T => (armPullCount a h : ℝ)) := by
    have e : (fun h : BanditHistory K T => (armPullCount a h : ℝ))
        = (fun x : Fin T → Fin K => (({t | x t = a}.toFinset.card : ℕ) : ℝ)) ∘
          (fun h : BanditHistory K T => fun t => (h t).1) := rfl
    rw [e]
    exact (measurable_of_countable _).comp
      (measurable_pi_lambda _ fun t => measurable_fst.comp (measurable_pi_apply t))
  exact hc.max measurable_const

lemma tangent (x m : ℝ) (hx : 0 ≤ x) (hm : 0 ≤ m) :
    x / (1 + x) ≤ m / (1 + m) + 1 / (1 + m) ^ 2 * (x - m) := by
  rw [← sub_nonneg]
  have e : m / (1 + m) + 1 / (1 + m) ^ 2 * (x - m) - x / (1 + x)
      = (x - m) ^ 2 / ((1 + m) ^ 2 * (1 + x)) := by
    field_simp
    ring
  rw [e]
  positivity

end Aux_EFRJ

open ExploreFirst.Relative in
theorem solution {K : ℕ} (π : BanditPolicy K) (ν : StochasticBandit K) (a a' : Fin K)
    (T : ℕ) :
    (∫ h, pullsPlus a h / (pullsPlus a h + pullsPlus a' h) ∂(banditMeasure ν π T) =
      ∫ h, (pullsPlus a h / pullsPlus a' h) / (1 + pullsPlus a h / pullsPlus a' h)
        ∂(banditMeasure ν π T)) ∧
    (∫ h, (pullsPlus a h / pullsPlus a' h) / (1 + pullsPlus a h / pullsPlus a' h)
        ∂(banditMeasure ν π T) ≤
      (∫ h, pullsPlus a h / pullsPlus a' h ∂(banditMeasure ν π T)) /
        (1 + ∫ h, pullsPlus a h / pullsPlus a' h ∂(banditMeasure ν π T))) := by
  set μ := banditMeasure ν π T with hμ
  set X : BanditHistory K T → ℝ := fun h => pullsPlus a h / pullsPlus a' h with hXdef
  have hX0 : ∀ h, 0 ≤ X h := fun h =>
    div_nonneg (le_trans zero_le_one (Aux_EFRJ.pp_ge a h)) (le_trans zero_le_one (Aux_EFRJ.pp_ge a' h))
  have hX1 : ∀ h, X h ≤ T + 1 := by
    intro h
    have h1 := Aux_EFRJ.pp_ge a' h
    have h2 := Aux_EFRJ.pp_le a h
    have h3 := Aux_EFRJ.pp_ge a h
    rw [hXdef, div_le_iff₀ (by linarith)]
    nlinarith
  have hXm : Measurable X := (Aux_EFRJ.pp_meas a).div (Aux_EFRJ.pp_meas a')
  have hXi : Integrable X μ := by
    refine Integrable.of_bound hXm.aestronglyMeasurable (T + 1) (ae_of_all _ fun h => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hX0 h)]
    exact hX1 h
  refine ⟨?_, ?_⟩
  · refine integral_congr_ae (ae_of_all _ fun h => ?_)
    have h1 := Aux_EFRJ.pp_ge a h
    have h2 := Aux_EFRJ.pp_ge a' h
    have hq : pullsPlus a' h ≠ 0 := by linarith
    have hpq : pullsPlus a h + pullsPlus a' h ≠ 0 := by linarith
    field_simp
    ring
  · set m := ∫ h, X h ∂μ with hm
    have hm0 : 0 ≤ m := integral_nonneg hX0
    have hfi : Integrable (fun h => X h / (1 + X h)) μ := by
      refine Integrable.of_bound (hXm.div (measurable_const.add hXm)).aestronglyMeasurable 1
        (ae_of_all _ fun h => ?_)
      have := hX0 h
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one (by linarith)]
      linarith
    have hgi : Integrable (fun h => m / (1 + m) + 1 / (1 + m) ^ 2 * (X h - m)) μ :=
      (integrable_const _).add ((hXi.sub (integrable_const m)).const_mul _)
    have hpt : ∀ h, X h / (1 + X h) ≤ m / (1 + m) + 1 / (1 + m) ^ 2 * (X h - m) :=
      fun h => Aux_EFRJ.tangent (X h) m (hX0 h) hm0
    have hmono := integral_mono hfi hgi hpt
    have hval : ∫ h, (m / (1 + m) + 1 / (1 + m) ^ 2 * (X h - m)) ∂μ = m / (1 + m) := by
      have hi2 : Integrable (fun h => 1 / (1 + m) ^ 2 * (X h - m)) μ :=
        (hXi.sub (integrable_const m)).const_mul _
      have hi3 : ∫ h, (X h - m) ∂μ = m - m := by
        rw [integral_sub hXi (integrable_const m)]
        simp [← hm]
      rw [integral_add (integrable_const _) hi2, integral_const_mul, hi3]
      simp
    rw [hval] at hmono
    exact hmono
