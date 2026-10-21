-- Prove2me | solution 1 for CostlyPriceInterp.MarketEq.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:28:59.25588+00:00
-- url     : https://prove2.me/submissions/e74d3f1e-13e4-4bd3-9e99-5d0c6cd02202

import Mathlib
import Definitions.Def_CostlyPriceInterp_MarketEq_Model
import Theorems.Thm_CostlyPriceInterp_MarketEq_coefficient_matching
import Theorems.Thm_CostlyPriceInterp_MarketEq_a_expressions
import Theorems.Thm_CostlyPriceInterp_MarketEq_cubic_reduction
import Theorems.Thm_CostlyPriceInterp_MarketEq_existence_ivt
import Theorems.Thm_CostlyPriceInterp_MarketEq_uniqueness_discriminant

open CostlyPriceInterp.MarketEq

theorem solution (P : Params) (hP : P.Standing) :
    (∃! a : ℝ × ℝ, IsLinearEq P a.1 a.2) ∧
    ∀ av au : ℝ, IsLinearEq P av au →
      av = avOf P (au / av) ∧ au = auOf P (au / av) ∧
      0 < au / av ∧ au / av < alphaBar P ∧ cubicF P (au / av) = 0 ∧
      (∀ x : ℝ, 0 < x → cubicF P x = 0 → x = au / av) ∧
      0 < au := by
  obtain ⟨-, -, -, ⟨α0, hα0, hf0⟩⟩ := existence_ivt P hP
  have huniq := (uniqueness_discriminant P hP).2.2.2
  -- characterization of equilibria
  have hchar : ∀ av au : ℝ, IsLinearEq P av au →
      av ≠ 0 ∧ av = avOf P (au / av) ∧ au = auOf P (au / av) ∧ cubicF P (au / av) = 0 := by
    intro av au h
    obtain ⟨hav, h1, h2⟩ := (coefficient_matching P hP av au).1 h
    obtain ⟨e1, e2⟩ := a_expressions P hP (au / av)
    rw [e1] at h1
    rw [e2] at h2
    refine ⟨hav, h1, h2, ?_⟩
    apply ((cubic_reduction P hP (au / av)).1).1
    rw [← h1, ← h2]
    field_simp
  refine ⟨?_, ?_⟩
  · refine ⟨(avOf P α0, α0 * avOf P α0), ?_, ?_⟩
    · have hpos := (cubic_reduction P hP α0).2
      have hq : α0 * avOf P α0 / avOf P α0 = α0 := by field_simp
      show IsLinearEq P (avOf P α0) (α0 * avOf P α0)
      rw [coefficient_matching P hP, hq]
      obtain ⟨e1, e2⟩ := a_expressions P hP α0
      refine ⟨hpos.ne', e1.symm, ?_⟩
      rw [e2]
      exact ((cubic_reduction P hP α0).1).2 hf0
    · rintro ⟨av, au⟩ h
      obtain ⟨hav, h1, h2, h3⟩ := hchar av au h
      have hα : au / av = α0 := huniq _ _ h3 hf0
      rw [hα] at h1 h2
      have hau : au = α0 * av := by
        rw [← hα]; field_simp
      rw [Prod.mk.injEq]
      exact ⟨h1, by rw [hau, h1]⟩
  · intro av au h
    obtain ⟨hav, h1, h2, h3⟩ := hchar av au h
    have hα : au / av = α0 := huniq _ _ h3 hf0
    have hpos := (cubic_reduction P hP (au / av)).2
    refine ⟨h1, h2, by rw [hα]; exact hα0.1, by rw [hα]; exact hα0.2, h3,
      fun x hx hfx => huniq _ _ hfx h3, ?_⟩
    have hau : au = au / av * av := by field_simp
    rw [hau]
    rw [← h1] at hpos
    exact mul_pos (by rw [hα]; exact hα0.1) hpos
