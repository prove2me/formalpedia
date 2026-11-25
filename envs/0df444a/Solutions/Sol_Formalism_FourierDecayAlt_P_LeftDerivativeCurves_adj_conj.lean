-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftDerivativeCurves.adj_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:25.286275+00:00
-- url     : https://prove2.me/submissions/33c5a1df-4aec-4168-bf55-489fd463ca66

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_unitary_inv_conjTranspose_hermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_unitary_hermitian_conjTranspose
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx2_hpk_sq__e1ad91698796


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
theorem _root_.solution {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (Z : Mx k r) :
    (Hpk k r)⁻¹ * (g⁻¹ * Z * g)ᴴ * Hpk k r = g⁻¹ * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) * g := by
  rw [Matrix.inv_eq_left_inv Qx2.hpk_sq', conjTranspose_mul, conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [unitary_inv_conjTranspose_hermitian hg, ← Matrix.mul_assoc (Hpk k r) gᴴ, unitary_hermitian_conjTranspose hg]
  simp only [Matrix.mul_assoc]
end Formalism.FourierDecayAlt.P.LeftDerivativeCurves
