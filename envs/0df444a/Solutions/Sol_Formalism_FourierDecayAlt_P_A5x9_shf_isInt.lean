-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.shf_isInt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:18.080801+00:00
-- url     : https://prove2.me/submissions/523f4ee9-38ee-4676-9dea-cce93edf2a88

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_vecMul_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (Z₀ p : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det) (hp : IsPP R k p)
    (hZ : IsInt R (Z₀ * p)) (m : Fin n → R) (β : Fin n → K) (hβi : ∀ b, β b ∈ R)
    (hβ : ∀ b : Fin n, b.val ≤ k → β b = 0) :
    IsInt R (Z₀ * ((1 + vecMulVec (Z₀⁻¹ *ᵥ coeLin R m) β) * p)) := by
  rw [shf_mul R Z₀ p hd m β]
  intro a b
  rw [Matrix.add_apply, vecMulVec_apply, Formalism.DoubleCosetMeasures.P.coeLin_apply]
  exact R.add_mem (hZ a b) (R.mul_mem (m a).2 (shf_vecMul_int R k hp.1 β hβi hβ b))
end Formalism.FourierDecayAlt.P.A5x9
