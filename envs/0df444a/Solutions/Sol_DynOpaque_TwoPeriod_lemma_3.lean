-- Prove2me | solution 1 for DynOpaque.TwoPeriod.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T11:54:13.214568+00:00
-- url     : https://prove2.me/submissions/274c686e-9849-4d27-9c6f-62a6950c7904

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

/-- Lemma 3, p. 12: optimal offering decisions for objective (4) (`p₁ = vHL`, `p₂ = vL`). -/
theorem solution (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α) :
    ((vHL vH vL - cL) / (cH - cL) < 2 →
      IsOptimalOffering (obj4 vH vL cH cL) ((vHL vH vL - cL) / (2 * (cH - cL))) 0) ∧
    ((vHL vH vL - cL) / (cH - cL) ≥ 2 →
      IsOptimalOffering (obj4 vH vL cH cL) 1 0) := by
  have hd : 0 < cH - cL := sub_pos.mpr hS.2.1
  have hA : 0 < vHL vH vL - cL := by
    unfold vHL
    linarith [hS.1, hS.2.2.2.2]
  constructor
  · intro hr
    let q : ℝ := (vHL vH vL - cL) / (2 * (cH - cL))
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hq1 : q ≤ 1 := by
      dsimp [q]
      apply (div_le_one₀ (by positivity : 0 < 2 * (cH - cL))).mpr
      have h := (div_lt_iff₀ hd).mp hr
      linarith
    have hstat : 2 * (cH - cL) * q = vHL vH vL - cL := by
      dsimp [q]
      field_simp
    constructor
    · exact ⟨⟨hq0,hq1⟩,⟨by norm_num,by norm_num⟩⟩
    · intro x hx
      have hdiff : obj4 vH vL cH cL q 0 - obj4 vH vL cH cL x.1 x.2 =
          (cH - cL) * (x.1 - q) ^ 2 + (cH - cL) * x.2 := by
        dsimp only [obj4]
        linear_combination (x.1 - q) * hstat
      have h1 := mul_nonneg hd.le (sq_nonneg (x.1 - q))
      have h2 := mul_nonneg hd.le hx.2.1
      linarith
  · intro hr
    have hbound : 2 * (cH - cL) ≤ vHL vH vL - cL := (le_div_iff₀ hd).mp hr
    constructor
    · exact ⟨⟨by norm_num,by norm_num⟩,⟨by norm_num,by norm_num⟩⟩
    · intro x hx
      have h1 := mul_nonneg (sub_nonneg.mpr hx.1.2) (sub_nonneg.mpr hbound)
      have h2 := mul_nonneg hd.le (sq_nonneg (1 - x.1))
      have h3 := mul_nonneg hd.le hx.2.1
      dsimp [obj4]
      nlinarith



