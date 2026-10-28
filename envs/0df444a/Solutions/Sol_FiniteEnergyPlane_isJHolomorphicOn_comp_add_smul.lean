-- Prove2me | solution 1 for FiniteEnergyPlane.isJHolomorphicOn_comp_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T21:05:56.213387+00:00
-- url     : https://prove2.me/submissions/e3178328-8c22-4051-a893-c808904eadf8

import Definitions.Def_FiniteEnergyPlane_Setting

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (U : Set ℂ) (u : ℂ → E)
    (hhol : JHolomorphic.IsJHolomorphicOn J U u) (c : ℂ) (a : ℝ) :
    JHolomorphic.IsJHolomorphicOn J {w | c + a • w ∈ U} (fun w => u (c + a • w)) ∧
      ∀ w : ℂ, c + a • w ∈ U →
        fderiv ℝ (fun w => u (c + a • w)) w = a • fderiv ℝ u (c + a • w) := by
  have hinner : ∀ w : ℂ, HasFDerivAt (fun w : ℂ => c + a • w)
      (a • ContinuousLinearMap.id ℝ ℂ) w := fun w =>
    ((hasFDerivAt_id w).const_smul a).const_add c
  have key : ∀ w : ℂ, c + a • w ∈ U →
      HasFDerivAt (fun w => u (c + a • w)) (a • fderiv ℝ u (c + a • w)) w := by
    intro w hw
    have h := ((hhol _ hw).1.hasFDerivAt).comp w (hinner w)
    have e : a • fderiv ℝ u (c + a • w) =
        (fderiv ℝ u (c + a • w)).comp (a • ContinuousLinearMap.id ℝ ℂ) := by
      refine ContinuousLinearMap.ext fun x => ?_
      simp
    rw [e]; exact h
  refine ⟨fun w hw => ⟨(key w hw).differentiableAt, ?_⟩, fun w hw => (key w hw).fderiv⟩
  have hd := (hhol _ hw).2
  unfold JHolomorphic.dbarJ at hd ⊢
  rw [(key w hw).fderiv]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply]
  rw [map_smul, ← smul_add, hd, smul_zero]
