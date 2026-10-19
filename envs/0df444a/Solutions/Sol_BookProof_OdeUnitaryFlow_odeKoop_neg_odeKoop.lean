-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.odeKoop_neg_odeKoop
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:22:55.752027+00:00
-- url     : https://prove2.me/submissions/238a37f5-d17b-49e1-9fb9-12bd7159073e

import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.odeKoop_neg_odeKoop
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal


theorem solution (t : ℝ) (ψ : ℝ → ℂ) (x : ℝ) (hx : x ∈ flowDom (-t)) :
    odeKoop (-t) (odeKoop t ψ) x = ψ x := by
  have h1 : (1 - t * x) ≠ 0 := by
    have : (1 + -t * x) ≠ 0 := hx
    intro h; apply this; linarith
  have hmv : mob (-t) x = x / (1 - t * x) := by unfold mob; ring_nf
  have hm : mob t (mob (-t) x) = x := by
    rw [hmv]; unfold mob
    have : 1 + t * (x / (1 - t * x)) = 1 / (1 - t * x) := by field_simp; ring
    rw [this]; have h1' : 1 - x * t ≠ 0 := by rwa [mul_comm]
    field_simp
  unfold odeKoop
  rw [hm]
  rw [← mul_assoc, ← mul_inv]
  have : ((1 + -t * x : ℝ) : ℂ) * ((1 + t * mob (-t) x : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hmv]
    have : (1 + -t * x) * (1 + t * (x / (1 - t * x))) = 1 := by field_simp; ring
    rw [this]; simp
  rw [this, inv_one, one_mul]

