-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftDerivativeCurves.lie_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:55:39.805643+00:00
-- url     : https://prove2.me/submissions/7d5b534b-ba03-4e1c-bfcf-9996a5697a84

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_unitary_hermitian_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_unitary_inv_conjTranspose_hermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LeftDerivativeCurves
open Qx2 (Good)
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}
namespace Formalism.FourierDecayAlt.P.LeftDerivativeCurves
theorem _root_.solution {g X : Mx k r} (hg : g ∈ Glev k r i) (hX : inLieLev k r i X) :
    inLieLev k r i (g⁻¹ * X * g) := by
  obtain ⟨hgU, hfix⟩ := hg
  obtain ⟨hXs, hXk⟩ := hX
  refine ⟨?_, fun a ha => ?_⟩
  · rw [conjTranspose_mul, conjTranspose_mul]
    have e1 : gᴴ * (Xᴴ * (g⁻¹)ᴴ) * Hpk k r = gᴴ * (Xᴴ * Hpk k r) * g := by
      simp only [Matrix.mul_assoc]
      rw [unitary_inv_conjTranspose_hermitian hgU]
    have e2 : Hpk k r * (g⁻¹ * X * g) = gᴴ * (Hpk k r * X) * g := by
      simp only [← Matrix.mul_assoc]
      rw [unitary_hermitian_inv hgU]
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hXs, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨h1, h2⟩ := hfix a ha
    obtain ⟨h3, h4⟩ := hXk a ha
    refine ⟨?_, ?_⟩
    · rw [← Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, h3, Matrix.mulVec_zero]
    · rw [← Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec, h4, Matrix.mulVec_zero]
end Formalism.FourierDecayAlt.P.LeftDerivativeCurves
