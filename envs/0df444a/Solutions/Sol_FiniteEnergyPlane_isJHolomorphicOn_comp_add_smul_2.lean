-- Prove2me | solution 2 for FiniteEnergyPlane.isJHolomorphicOn_comp_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-24T21:08:19.543402+00:00
-- url     : https://prove2.me/submissions/5b70c178-174a-485c-85d9-48d13e325146

import Definitions.Def_FiniteEnergyPlane_Setting



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Real affine reparametrisations of the domain preserve `J`-holomorphicity. If `u` is
`J`-holomorphic on `U ⊆ ℂ`, `c ∈ ℂ` and `a ∈ ℝ`, then `w ↦ u (c + a w)` is `J`-holomorphic on
`{w | c + a w ∈ U}`, and its derivative there is `a • Du(c + a w)`. -/
theorem isJHolomorphicOn_comp_add_smul_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (U : Set ℂ) (u : ℂ → E)
    (hhol : JHolomorphic.IsJHolomorphicOn J U u) (c : ℂ) (a : ℝ) :
    JHolomorphic.IsJHolomorphicOn J {w | c + a • w ∈ U} (fun w => u (c + a • w)) ∧
      ∀ w : ℂ, c + a • w ∈ U →
        fderiv ℝ (fun w => u (c + a • w)) w = a • fderiv ℝ u (c + a • w) := by
  have key : ∀ w : ℂ, c + a • w ∈ U →
      HasFDerivAt (fun w => u (c + a • w)) (a • fderiv ℝ u (c + a • w)) w := by
    intro w hw
    have hf : HasFDerivAt (fun w : ℂ => c + a • w) (a • ContinuousLinearMap.id ℝ ℂ) w :=
      ((hasFDerivAt_id w).const_smul a).const_add c
    have hu := ((hhol _ hw).1).hasFDerivAt
    have h := hu.comp w hf
    have e : (fderiv ℝ u (c + a • w)).comp (a • ContinuousLinearMap.id ℝ ℂ) =
        a • fderiv ℝ u (c + a • w) := by
      ext v
      simp [map_smul]
    rw [e] at h
    exact h
  refine ⟨fun w hw => ⟨(key w hw).differentiableAt, ?_⟩, fun w hw => (key w hw).fderiv⟩
  have hd := (hhol _ hw).2
  unfold JHolomorphic.dbarJ at hd ⊢
  rw [(key w hw).fderiv]
  simp only [ContinuousLinearMap.smul_apply, map_smul]
  rw [← smul_add, hd, smul_zero]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (U : Set ℂ) (u : ℂ → E)
    (hhol : JHolomorphic.IsJHolomorphicOn J U u) (c : ℂ) (a : ℝ) :
    JHolomorphic.IsJHolomorphicOn J {w | c + a • w ∈ U} (fun w => u (c + a • w)) ∧
      ∀ w : ℂ, c + a • w ∈ U →
        fderiv ℝ (fun w => u (c + a • w)) w = a • fderiv ℝ u (c + a • w) :=
  FiniteEnergyPlane.isJHolomorphicOn_comp_add_smul_aux J U u hhol c a
