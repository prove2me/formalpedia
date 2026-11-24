-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.sum_xb_y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:46:34.952681+00:00
-- url     : https://prove2.me/submissions/430fa225-89a4-4166-8962-642e38641e16

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx2_hpk_sq__e1ad91698796
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_sum_posL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_herm_expand
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_herm_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_herm_uh
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_herm_bvec_out

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
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {i : Fin (r + 1)}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') {g : Mx k r}
    (hg : g ∈ UH (Hpk k r)) : ∑ j, xbv k r z' i j * yv k r z i g j = star (zetaL k r z z' i g) := by
  have hdet : IsUnit g.det := by
    have h1 : (g)ᴴ * Hpk k r * g = Hpk k r := hg
    have h2 : (Hpk k r).det * (Hpk k r).det = 1 := by
      rw [← Matrix.det_mul, hpk_sq', Matrix.det_one]
    have h3 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul] at h3
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, mul_zero] at h3
    rw [← h3, zero_mul] at h2
    exact zero_ne_one h2
  have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hdet
  have e1 : ∑ j, xbv k r z' i j * yv k r z i g j =
      herm (Hpk k r) (g⁻¹ *ᵥ fvec k r z i) (fvec k r z' i) := by
    have hx := herm_expand (k := k) (r := r) 1 (g⁻¹ *ᵥ fvec k r z i) (fvec k r z' i)
    simp only [Matrix.one_mulVec] at hx
    rw [hx, ← sum_posL (i := i)]
    · rfl
    · intro p hp
      rw [herm_bvec_out hz' hp, zero_mul]
  rw [e1, zetaL, herm_star, ← herm_uh hg (g⁻¹ *ᵥ fvec k r z i) (fvec k r z' i), Matrix.mulVec_mulVec, hgi,
    Matrix.one_mulVec]
end Formalism.FourierDecayAlt.P.Qx2
