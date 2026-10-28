-- Prove2me | solution 1 for FunctionalInequalities.Analysis.volume_subgradientImage_quadraticAt_aux_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:34:38.37218+00:00
-- url     : https://prove2.me/submissions/edd32007-9bd0-4bcc-a84b-71bacd767a8b

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov
import Theorems.Thm_FunctionalInequalities_Analysis_quadraticAt_subgradient_iff_readable

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT12C1QuadraticSubgradientImage
open MeasureTheory Set Matrix
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
        (FunctionalInequalities.Analysis.quadraticAt_subgradient_iff_readable hA.posSemidef x₀ b c x p).mp hp
      simpa [g] using heq.symm
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      apply (FunctionalInequalities.Analysis.quadraticAt_subgradient_iff_readable hA.posSemidef x₀ b c x (g x)).mpr
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
