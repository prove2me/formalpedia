-- Prove2me | solution 1 for ChanceStateCtrl.Robust.polar_measure_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:29:31.835056+00:00
-- url     : https://prove2.me/submissions/58a406bb-efa1-4388-a027-65e93f15d3bc

import Mathlib
import Definitions.Def_ChanceStateCtrl_Robust_Setting

open MeasureTheory
open scoped CompactlySupported
open ChanceStateCtrl.Robust

/-- Riesz–Markov–Kakutani on a compact space, for a positive continuous linear functional. -/
private lemma rmk_compact {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (Λ : StrongDual ℝ C(X, ℝ))
    (hpos : ∀ z : C(X, ℝ), (∀ q, 0 ≤ z q) → 0 ≤ Λ z) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ ∀ z : C(X, ℝ), ∫ q, z q ∂μ = Λ z := by
  let Lc : C_c(X, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => Λ (f : C(X, ℝ))
      map_add' := fun f g => by
        rw [← map_add]; rfl
      map_smul' := fun c f => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← smul_eq_mul, ← map_smul]; rfl }
  let Λc : C_c(X, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ Lc (fun f hf => hpos _ (fun q => hf q))
  refine ⟨RealRMK.rieszMeasure Λc, inferInstance, fun z => ?_⟩
  have := RealRMK.integral_rieszMeasure Λc (CompactlySupportedContinuousMap.continuousMapEquiv z)
  exact this.trans (congrArg Λ (ContinuousMap.ext fun _ => rfl))

theorem solution {d m : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))}
    {Ξ : Set (EuclideanSpace ℝ (Fin m))}
    [CompactSpace (closure D)] [CompactSpace Ξ]
    (lamStar : StrongDual ℝ C(closure D × Ξ, ℝ)) (hlam : lamStar ∈ KhatPolar D Ξ) :
    ∃ μ : Measure (closure D × Ξ), IsFiniteMeasure μ ∧
      ∀ r : C(closure D × Ξ, ℝ), lamStar r = ∫ q, r q ∂μ := by
  obtain ⟨μ, hμ, hint⟩ := rmk_compact lamStar (fun z hz => by
    have := hlam (-z) (fun q => by simp; exact hz q)
    rw [map_neg] at this
    linarith)
  exact ⟨μ, hμ, fun r => (hint r).symm⟩
