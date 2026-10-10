-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.odeKoop_chartW
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:47:18.09934+00:00
-- url     : https://prove2.me/submissions/1070cafd-e18c-45ca-a969-f9c2ea1dc120

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.odeKoop_chartW
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
import Theorems.Thm_BookProof_OdeUnitaryFlow_invMap_mob
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) (ψ : ℝ → ℂ) {x : ℝ} (hx : x ≠ 0) (h : 1 + t * x ≠ 0) :
    odeKoop t (chartW ψ) x = chartW (transl t ψ) x := by

  have hmob : mob t x ≠ 0 := by
    simp only [mob]
    exact div_ne_zero hx h
  have hmobval : ((mob t x : ℝ) : ℂ)⁻¹ = ((1 + t * x : ℝ) : ℂ) * ((x : ℝ) : ℂ)⁻¹ := by
    have : mob t x = x / (1 + t * x) := rfl
    rw [this]
    push_cast
    have hxc : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
    have hc : ((1 + t * x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
    push_cast at hc ⊢
    field_simp
  have hxc : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
  have hc : ((1 + t * x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
  simp only [odeKoop, chartW, transl, invMap_mob hx, hmobval]
  field_simp
