-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.shf_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:02.006876+00:00
-- url     : https://prove2.me/submissions/432fe4c8-c2d5-4056-a0fb-3a47ece30e3a

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_mem_latZ_rank1
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_dot_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_vecMul_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_dot
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_Lam_zero

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
    (m : Fin n → R) (hm : abelian₂ R k Z₀ m = 0) (β : Fin n → K) (hβi : ∀ b, β b ∈ R)
    (hβ : ∀ b : Fin n, b.val ≤ k → β b = 0) (x : Fin n → R) :
    x ∈ latZ R (Z₀ * ((1 + vecMulVec (Z₀⁻¹ *ᵥ coeLin R m) β) * p)) ↔
      ∃ r : R, (r : K) = β ⬝ᵥ (Z₀⁻¹ *ᵥ coeLin R x) ∧ x - r • m ∈ latZ R (Z₀ * p) := by
  have hdp : IsUnit (Z₀ * p).det := by
    rw [Matrix.det_mul, isUpUni_det K hp.1.1, mul_one]; exact hd
  rw [shf_mul R Z₀ p hd m β, mem_latZ_rank1 R (Z₀ * p) hdp m (β ᵥ* p)
    (shf_vecMul_int R k hp.1 β hβi hβ)
    (by rw [shf_dot Z₀ p hp.1.1]; exact shf_dot_zero k _ β (shf_Lam_zero R k Z₀ m hm) hβ) x,
    shf_dot Z₀ p hp.1.1]
end Formalism.FourierDecayAlt.P.A5x9
