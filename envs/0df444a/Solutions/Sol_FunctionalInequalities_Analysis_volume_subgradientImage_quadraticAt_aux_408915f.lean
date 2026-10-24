-- Prove2me | solution 1 for FunctionalInequalities.Analysis.volume_subgradientImage_quadraticAt_aux_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:15:51.582535+00:00
-- url     : https://prove2.me/submissions/965ff0a2-54e8-4824-a99d-d313e12059d2

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_quadraticAt_subgradient_iff_408915f

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT12C1QuadraticSubgradientImage
open MeasureTheory Set Matrix
open scoped RealInnerProductSpace ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
 lemma solution
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    {G : Set (EuclideanSpace ℝ (Fin n))} :
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (FunctionalInequalities.Analysis.subgradientImage (FunctionalInequalities.Analysis.quadraticAt A x₀ b c) G) =
      ENNReal.ofReal A.det *
        (volume : Measure (EuclideanSpace ℝ (Fin n))) G := by
  let E := EuclideanSpace ℝ (Fin n)
  let T : E →ₗ[ℝ] E := Matrix.toEuclideanLin A
  let g : E → E := fun x => b + T (x - x₀)
  have himage :
      FunctionalInequalities.Analysis.subgradientImage (FunctionalInequalities.Analysis.quadraticAt A x₀ b c) G = g '' G := by
    ext p
    constructor
    · rintro ⟨x, hx, hp⟩
      refine ⟨x, hx, ?_⟩
      have heq :=
        (FunctionalInequalities.Analysis.quadraticAt_subgradient_iff_408915f hA.posSemidef x₀ b c x p).mp hp
      simpa [g] using heq.symm
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      apply (FunctionalInequalities.Analysis.quadraticAt_subgradient_iff_408915f hA.posSemidef x₀ b c x (g x)).mpr
      rfl
  let d : E := b - T x₀
  have hg (x : E) : g x = d + T x := by
    dsimp [g, d]
    rw [map_sub]
    abel
  have haffine :
      g '' G = (fun z : E => d + z) '' (T '' G) := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨T x, ⟨x, hx, rfl⟩, ?_⟩
      exact (hg x).symm
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, hg x⟩
  have htrans :
      (volume : Measure E) ((fun z : E => d + z) '' (T '' G)) =
        (volume : Measure E) (T '' G) := by
    rw [image_add_left]
    exact measure_preimage_add volume (-d) (T '' G)
  have hdet : LinearMap.det T = A.det := by
    change LinearMap.det (Matrix.toLpLin 2 2 A) = A.det
    rw [Matrix.toLpLin_eq_toLin]
    exact LinearMap.det_toLin (PiLp.basisFun 2 ℝ (Fin n)) A
  have hdetpos : 0 < A.det := Matrix.PosDef.det_pos hA
  calc
    (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage (FunctionalInequalities.Analysis.quadraticAt A x₀ b c) G) =
        (volume : Measure E) (g '' G) := by rw [himage]
    _ = (volume : Measure E) ((fun z : E => d + z) '' (T '' G)) := by
      rw [haffine]
    _ = (volume : Measure E) (T '' G) := htrans
    _ = ENNReal.ofReal |LinearMap.det T| * (volume : Measure E) G :=
      Measure.addHaar_image_linearMap volume T G
    _ = ENNReal.ofReal A.det * (volume : Measure E) G := by
      rw [hdet, abs_of_pos hdetpos]
