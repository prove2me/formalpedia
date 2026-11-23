-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.cutSet_compact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:29.56227+00:00
-- url     : https://prove2.me/submissions/d5171780-4e6c-43a9-8e5c-ac90c3abaae6

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices

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
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution (m : ℕ) {Om : Set K} (hOm : IsCompact Om) (t : Kˣ) :
    IsCompact (cutSet m Om t) := by
  have h : cutSet m Om t = (fun z : K => ((((-t) ^ m)⁻¹ : Kˣ) : K) * z ^ (m + 1)) '' Om := by
    ext c
    constructor
    · rintro ⟨z, hz, hzc⟩
      refine ⟨z, hz, ?_⟩
      have : (-(t : K)) ^ m = (((-t) ^ m : Kˣ) : K) := by push_cast; rfl
      simp only
      rw [hzc, this, ← mul_assoc, Units.inv_mul, one_mul]
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z, hz, ?_⟩
      have : (-(t : K)) ^ m = (((-t) ^ m : Kˣ) : K) := by push_cast; rfl
      rw [this, ← mul_assoc, Units.mul_inv, one_mul]
  rw [h]
  exact hOm.image (by fun_prop)
end Formalism.FourierDecayAlt.P.GermSumLattices
