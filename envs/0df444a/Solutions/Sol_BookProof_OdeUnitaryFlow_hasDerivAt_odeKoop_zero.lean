-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.hasDerivAt_odeKoop_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:23:08.183923+00:00
-- url     : https://prove2.me/submissions/d4c37db0-0e96-4bd7-95f9-9d63f178227c

import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.hasDerivAt_odeKoop_zero
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal


theorem solution (ψ : ℝ → ℂ) (x : ℝ) (d : ℂ) (hψ : HasDerivAt ψ d x) :
    HasDerivAt (fun t : ℝ => odeKoop t ψ x) (-((x : ℂ) ^ 2 * d + (x : ℂ) * ψ x)) 0 := by
  have hden : HasDerivAt (fun t : ℝ => 1 + t * x) x 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const x).const_add 1
  have hmob : HasDerivAt (fun t : ℝ => mob t x) (-(x ^ 2)) 0 := by
    have := (hasDerivAt_const (0:ℝ) x).div hden (by simp)
    exact this.congr_deriv (by simp; ring)
  have hm0 : mob 0 x = x := by simp [mob]
  have hψ' : HasDerivAt ψ d (mob 0 x) := by rw [hm0]; exact hψ
  have hcomp : HasDerivAt (fun t : ℝ => ψ (mob t x)) ((-(x ^ 2) : ℝ) • d) 0 :=
    hψ'.scomp (0:ℝ) hmob
  have hinv : HasDerivAt (fun t : ℝ => (((1 + t * x : ℝ) : ℂ))⁻¹) (-((x:ℂ))) 0 := by
    have hc : HasDerivAt (fun t : ℝ => ((1 + t * x : ℝ) : ℂ)) (x : ℂ) 0 := hden.ofReal_comp
    have := hc.inv (by simp)
    exact this.congr_deriv (by simp)
  have := hinv.mul hcomp
  unfold odeKoop
  refine this.congr_deriv ?_
  rw [hm0]; simp only [Complex.real_smul]; push_cast; ring

