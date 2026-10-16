-- Prove2me | solution 1 for Esgk.maximallyCircular_pairSeparation
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-16T05:39:58.608824+00:00
-- url     : https://prove2.me/submissions/7f8dae91-52c8-4fcd-ac29-76428f19d16a

import Theorems.Thm_Esgk_maximallyCircular_twoSamplePairSeparation
import Definitions.Def_Esgk_DistanceNewtonFactorSaturation
import Definitions.Def_Esgk_IrreduciblePlaneDistanceImageInfiniteCorrespondence
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
import Definitions.Def_Esgk_PlaneCircleFactor
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim

open Esgk
open PachDeZeeuw (PreparedBipartiteInput)
open PachDeZeeuw.Algebraic (PlanePoly PlaneCurveZeroSet)
open IrreduciblePlanePolynomial


theorem solution
    {G : PlanePoly} (hGirreducible : Irreducible G)
    (hmax : IsMaximallyCircular G) (hnotCircle : ¬ IsCircleFactor G)
    (S : Finset PachDeZeeuw.Algebraic.Point2) (hS : (S : Set PachDeZeeuw.Algebraic.Point2) ⊆ PlaneCurveZeroSet G) :
    ∃ Δ : Finset (S × S),
      Δ.card ≤ 8 * G.totalDegree ^ 2 * S.card ∧
      ∀ ij, ij ∉ Δ → ∀ kl, kl ∉ Δ → ij ≠ kl →
        (twoPairDistanceCommonZeroSet
          ⟨G, hGirreducible⟩
          (ij.1 : PachDeZeeuw.Algebraic.Point2) (kl.1 : PachDeZeeuw.Algebraic.Point2)
          (ij.2 : PachDeZeeuw.Algebraic.Point2) (kl.2 : PachDeZeeuw.Algebraic.Point2)).Finite := by
  obtain ⟨Δ₁, Δ₂, hcard₁, hcard₂, hfinite₁, hfinite₂⟩ :=
    Esgk.maximallyCircular_twoSamplePairSeparation hGirreducible hmax hnotCircle S S hS hS
  exact ⟨Δ₁, hcard₁, hfinite₁⟩
