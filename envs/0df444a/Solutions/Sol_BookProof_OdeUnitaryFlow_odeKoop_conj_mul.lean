-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.odeKoop_conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:59:00.434197+00:00
-- url     : https://prove2.me/submissions/7dd891c6-0a3a-4e17-aed0-4dcb2fed39c9

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.odeKoop_conj_mul
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
import Theorems.Thm_BookProof_OdeUnitaryFlow_one_add_neg_mul_mob
import Theorems.Thm_BookProof_OdeUnitaryFlow_mob_neg_mob
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) (ρ ψ : ℝ → ℂ) (x : ℝ) (hx : x ∈ flowDom t) :
    odeKoop t (fun y => ρ y * odeKoop (-t) ψ y) x = ρ (mob t x) * ψ x := by

  have h : 1 + t * x ≠ 0 := hx
  have hc : ((1 + t * x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
  have hback : mob (-t) (mob t x) = x := mob_neg_mob t x hx
  have hden : ((1 + (-t) * mob t x : ℝ) : ℂ) = (((1 + t * x)⁻¹ : ℝ) : ℂ) := by
    rw [one_add_neg_mul_mob t x hx]
  have hc' : (1 + (t : ℂ) * (x : ℂ)) ≠ 0 := by push_cast at hc; exact hc
  simp only [odeKoop, hback, hden]
  push_cast
  field_simp
