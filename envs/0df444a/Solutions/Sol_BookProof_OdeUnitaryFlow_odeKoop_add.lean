-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.odeKoop_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:47:09.522999+00:00
-- url     : https://prove2.me/submissions/c561bd62-030b-4e69-b6e6-85292ffab8c8

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.odeKoop_add
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
import Theorems.Thm_BookProof_OdeUnitaryFlow_one_add_mul_mob
import Theorems.Thm_BookProof_OdeUnitaryFlow_mob_mob
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (s t : ℝ) (ψ : ℝ → ℂ) (x : ℝ) (hs : 1 + s * x ≠ 0)
    (hst : 1 + (s + t) * x ≠ 0) :
    odeKoop s (odeKoop t ψ) x = odeKoop (s + t) ψ x := by

  have hts : 1 + (t + s) * x ≠ 0 := by rwa [add_comm t s]
  have hmob : mob t (mob s x) = mob (s + t) x := by
    rw [mob_mob t s x hs hts, add_comm t s]
  have hcast : ((1 + t * mob s x : ℝ) : ℂ)
      = ((1 + (s + t) * x : ℝ) : ℂ) / ((1 + s * x : ℝ) : ℂ) := by
    rw [one_add_mul_mob t s x hs, add_comm t s]
    push_cast
    ring
  have h1 : ((1 + s * x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have h2 : ((1 + (s + t) * x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hst
  simp only [odeKoop]
  rw [hmob, hcast]
  field_simp
