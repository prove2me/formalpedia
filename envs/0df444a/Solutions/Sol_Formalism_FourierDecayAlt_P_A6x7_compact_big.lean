-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.compact_big
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:45.742799+00:00
-- url     : https://prove2.me/submissions/bbf331a6-e085-4715-985a-959182b3ba98

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x7
theorem _root_.solution (hD : LocalDatum K R ψ) (ϖ : Kˣ) (n : ℕ) :
    IsCompact {y : K | (ϖ : K) ^ n * y ∈ R} := by
  have : {y : K | (ϖ : K) ^ n * y ∈ R} = (fun r => (((ϖ ^ n)⁻¹ : Kˣ) : K) * r) '' (R : Set K) := by
    ext y
    constructor
    · intro hy
      refine ⟨_, hy, ?_⟩
      show (((ϖ ^ n)⁻¹ : Kˣ) : K) * ((ϖ : K) ^ n * y) = y
      rw [← mul_assoc, ← Units.val_pow_eq_pow_val, Units.inv_mul, one_mul]
    · rintro ⟨r, hr, rfl⟩
      show (ϖ : K) ^ n * ((((ϖ ^ n)⁻¹ : Kˣ) : K) * r) ∈ R
      rw [← mul_assoc, ← Units.val_pow_eq_pow_val, Units.mul_inv, one_mul]; exact hr
  rw [this]
  exact hD.isCompact.image (continuous_const.mul continuous_id)
end Formalism.FourierDecayAlt.P.A6x7
