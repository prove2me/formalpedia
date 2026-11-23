-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x2.posSemidef_of_isPSD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:57.977961+00:00
-- url     : https://prove2.me/submissions/4a32cbfb-c94b-4628-bfac-adf3551bd509

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PosSemidefEntryBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x2
namespace Formalism.FourierDecayAlt.P.A6x2
theorem _root_.solution {X : Type} (F : Finset X) (k : X → X → ℂ) (h : IsPSD F k) :
    (Matrix.of fun x y : F => conj (k x y)).PosSemidef := by
  classical
  rw [← Matrix.isPositive_toEuclideanLin_iff, LinearMap.isPositive_iff_complex]
  intro v
  have hv : inner ℂ ((Matrix.of fun x y : F => conj (k x y)).toEuclideanLin v) v =
      ∑ x ∈ F, ∑ y ∈ F, (fun x => if hx : x ∈ F then v ⟨x, hx⟩ else 0) x *
        conj ((fun x => if hx : x ∈ F then v ⟨x, hx⟩ else 0) y) * k x y := by
    rw [← Finset.sum_coe_sort F]
    simp_rw [← Finset.sum_coe_sort F (fun y => _ * k _ y)]
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [hv]
  obtain ⟨h1, h2⟩ := h (fun x => if hx : x ∈ F then v ⟨x, hx⟩ else 0)
  refine ⟨?_, h2⟩
  apply Complex.ext
  · simp
  · simpa using h1.symm
end Formalism.FourierDecayAlt.P.A6x2
