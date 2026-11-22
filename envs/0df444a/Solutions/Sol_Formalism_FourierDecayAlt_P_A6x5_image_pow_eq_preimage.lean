-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x5.image_pow_eq_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:19.651968+00:00
-- url     : https://prove2.me/submissions/b5dd1ac0-69a5-4dff-9cce-b74238fb5c6c

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x5
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x5
theorem _root_.solution (ϖ : Kˣ) (N : ℕ) (S : Set K) :
    (fun r => (ϖ : K) ^ N * r) '' S = (fun x => ((ϖ⁻¹ : Kˣ) : K) ^ N * x) ⁻¹' S := by
  have h1 : ((ϖ⁻¹ : Kˣ) : K) ^ N * (ϖ : K) ^ N = 1 := by
    rw [← mul_pow, Units.inv_mul, one_pow]
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    change ((ϖ⁻¹ : Kˣ) : K) ^ N * ((ϖ : K) ^ N * r) ∈ S
    rwa [← mul_assoc, h1, one_mul]
  · intro hx
    refine ⟨_, hx, ?_⟩
    change (ϖ : K) ^ N * (((ϖ⁻¹ : Kˣ) : K) ^ N * x) = x
    rw [← mul_assoc, mul_comm ((ϖ : K) ^ N), h1, one_mul]
end Formalism.FourierDecayAlt.P.A6x5
