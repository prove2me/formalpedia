-- Prove2me | solution 1 for ChanceStateCtrl.AlmostSure.splitting_3_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:26:32.312489+00:00
-- url     : https://prove2.me/submissions/aed0fb93-f268-43cc-a243-457fe9f02fbe

import Mathlib
import Definitions.Def_ChanceStateCtrl_AlmostSure_Setting

open MeasureTheory
open ChanceStateCtrl.AlmostSure

theorem solution {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace (closure D)]
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (lamStar lamA lamSing : StrongDual ℝ (Linf D P)) (lam : Ω → StrongDual ℝ C(closure D, ℝ))
    (hlam : lam ∈ Lambda1 C(closure D, ℝ) P)
    (hrep : ∀ y : Linf D P, lamA y = ∫ ω, lam ω (y ω) ∂P)
    (hsing : IsSingular P lamSing) (hsplit : lamStar = lamA + lamSing) :
    ∀ h : ChanceStateCtrl.PDE.L2 D, lamStar (Ainv.compLp (Bconst P h)) =
      ∫ ω, lam ω (Ainv h) ∂P + lamSing (Ainv.compLp (Bconst P h)) := by
  intro h
  have hae : ∀ᵐ ω ∂P, (Ainv.compLp (Bconst P h) : Linf D P) ω = Ainv h := by
    filter_upwards [Ainv.coeFn_compLp (Bconst P h), Lp.coeFn_const (p := ⊤) (μ := P) h]
      with ω h1 h2
    rw [h1]
    simp only [Bconst] at *
    rw [h2]; rfl
  rw [hsplit, ContinuousLinearMap.add_apply, hrep]
  congr 1
  apply integral_congr_ae
  filter_upwards [hae] with ω hω
  rw [hω]
