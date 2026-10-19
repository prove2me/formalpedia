-- Prove2me | solution 1 for DynOpaque.TwoPeriod.lemma_4_corrected
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T11:54:16.301276+00:00
-- url     : https://prove2.me/submissions/d7383788-aa75-43c1-aa48-2e15b5af424e

import Definitions.Def_DynOpaque_TwoPeriod_Model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Convex.Function
import Lean.Elab.Tactic.Omega
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

open DynOpaque.TwoPeriod

/-- Lemma 4, p. 12, CORRECTED (`p₁ = vL`, `p₂ = vHL`, objective (5)). Part (i) as printed
("ξ₁ = 1 or ξ₂ = 0 is optimal") is false; the corrected (i′) says that some optimal decision has
`ξ₁ ∈ {0, 1}`, in the form: every offering pair is weakly beaten by one with `ξ₁ ∈ {0, 1}`.
(ii) with `ξ₁ = 1`, (5) is dominated by (3); (iii) with `ξ₁ = 0`, (5) is dominated by (4). -/
theorem solution (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α) :
    (∀ x ∈ box, ∃ y ∈ box, (y.1 = 0 ∨ y.1 = 1) ∧
      obj5 vH vL cH cL α x.1 x.2 ≤ obj5 vH vL cH cL α y.1 y.2) ∧
    (∀ ξ₂ ∈ Set.Icc (0 : ℝ) 1, obj5 vH vL cH cL α 1 ξ₂ ≤ obj3 vH vL cH cL α 1 ξ₂) ∧
    (∀ ξ₂ ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ box, obj5 vH vL cH cL α 0 ξ₂ ≤ obj4 vH vL cH cL y.1 y.2) := by
  have ha0 := hS.2.2.1
  have ha1 := hS.2.2.2.1
  constructor
  · intro x hx
    by_cases hcmp : obj5 vH vL cH cL α 0 x.2 ≤ obj5 vH vL cH cL α 1 x.2
    · refine ⟨(1,x.2), ⟨⟨by norm_num,by norm_num⟩,hx.2⟩, Or.inr rfl, ?_⟩
      have h := mul_nonneg (sub_nonneg.mpr hx.1.2) (sub_nonneg.mpr hcmp)
      dsimp [obj5] at *
      nlinarith
    · refine ⟨(0,x.2), ⟨⟨by norm_num,by norm_num⟩,hx.2⟩, Or.inl rfl, ?_⟩
      have h := mul_nonneg hx.1.1 (sub_nonneg.mpr (le_of_not_ge hcmp))
      dsimp [obj5] at *
      nlinarith
  · constructor
    · intro y hy
      dsimp [obj5,obj3,vHL]
      linarith [hS.1]
    · intro y hy
      by_cases ht : 0 ≤ vHL vH vL - y * cH - (1-y)*cL
      · refine ⟨(y,0),⟨hy,⟨by norm_num,by norm_num⟩⟩,?_⟩
        have h := mul_nonneg ha0 (mul_nonneg hy.1 ht)
        dsimp [obj5,obj4]
        nlinarith
      · refine ⟨(0,0),⟨⟨by norm_num,by norm_num⟩,⟨by norm_num,by norm_num⟩⟩,?_⟩
        have h := mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (sub_nonneg.mpr ha1) hy.1) (le_of_not_ge ht)
        dsimp [obj5,obj4]
        nlinarith



