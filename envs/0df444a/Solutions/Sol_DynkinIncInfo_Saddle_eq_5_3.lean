-- Prove2me | solution 1 for DynkinIncInfo.Saddle.eq_5_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T18:56:55.253956+00:00
-- url     : https://prove2.me/submissions/89665ee0-7f6c-44bb-8416-8d5980765315

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game
import Definitions.Def_DynkinIncInfo_Saddle_Regions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open DynkinIncInfo.Saddle

theorem solution {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (x y : ℝ) (hx : 0 < x) (hy : y ∈ Set.Ioo (0 : ℝ) 1) (t : ℝ≥0) (ω : Ω) :
    Real.log (S p st x y t ω)
        + p.σ ^ 2 / p.δ0 * Real.log (Y p st x y t ω / (1 - Y p st x y t ω))
      = Real.log x + p.σ ^ 2 / p.δ0 * Real.log (y / (1 - y)) + k p * (t : ℝ) ∧
    S p st x y t ω
      = F p (Real.log x + p.σ ^ 2 / p.δ0 * Real.log (y / (1 - y)) + k p * (t : ℝ))
          (Y p st x y t ω) := by
  obtain ⟨hy0, hy1⟩ := hy
  have hσ1 : p.σ ≠ 0 := p.σ_pos.ne'
  have hσ : p.σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ1
  have hδ : p.δ0 ≠ 0 := p.δ0_pos.ne'
  set E : ℝ := p.σ * st.B t ω + (p.r - p.δ0 * D st y ω) * (t : ℝ) - (t : ℝ) * p.σ ^ 2 / 2
    with hE
  have hS : S p st x y t ω = x * Real.exp E := rfl
  have hSpos : 0 < S p st x y t ω := by rw [hS]; positivity
  set l : ℝ := ell p st x y t ω with hl
  have hlpos : 0 < l := Real.exp_pos _
  have hlogl : Real.log l = -(p.δ0 / p.σ ^ 2) * E
      + p.δ0 / (2 * p.σ ^ 2) * (2 * p.r - p.δ0 - p.σ ^ 2) * (t : ℝ) := by
    rw [hl, ell, Real.log_exp, hS, mul_div_cancel_left₀ _ hx.ne', Real.log_exp]
  have hY : Y p st x y t ω = y * l / (y * l + (1 - y)) := rfl
  have h1y : 0 < 1 - y := by linarith
  have hden : 0 < y * l + (1 - y) := by positivity
  have hYpos : 0 < Y p st x y t ω := by rw [hY]; positivity
  have h1Y : 1 - Y p st x y t ω = (1 - y) / (y * l + (1 - y)) := by
    rw [hY]; field_simp; ring
  have h1Ypos : 0 < 1 - Y p st x y t ω := by rw [h1Y]; positivity
  have hratio : Y p st x y t ω / (1 - Y p st x y t ω) = y / (1 - y) * l := by
    rw [h1Y, hY, div_div_div_cancel_right₀ hden.ne']; field_simp
  have hlogS : Real.log (S p st x y t ω) = Real.log x + E := by
    rw [hS, Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hfirst : Real.log (S p st x y t ω)
        + p.σ ^ 2 / p.δ0 * Real.log (Y p st x y t ω / (1 - Y p st x y t ω))
      = Real.log x + p.σ ^ 2 / p.δ0 * Real.log (y / (1 - y)) + k p * (t : ℝ) := by
    rw [hratio, Real.log_mul (div_pos hy0 h1y).ne' hlpos.ne', hlogl, hlogS, k]
    field_simp
    ring
  refine ⟨hfirst, ?_⟩
  rw [← hfirst, F]
  set Yt := Y p st x y t ω
  set a := p.σ ^ 2 / p.δ0
  have hw : 0 < Yt / (1 - Yt) := div_pos hYpos h1Ypos
  rw [Real.exp_add, Real.exp_log hSpos, ← Real.log_rpow hw, Real.exp_log (Real.rpow_pos_of_pos hw _),
    mul_assoc, ← Real.mul_rpow hw.le (div_pos h1Ypos hYpos).le]
  have : Yt / (1 - Yt) * ((1 - Yt) / Yt) = 1 := by field_simp
  rw [this, Real.one_rpow, mul_one]
