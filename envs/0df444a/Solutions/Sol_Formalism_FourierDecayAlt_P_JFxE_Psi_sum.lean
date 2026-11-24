-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.Psi_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:42:43.293895+00:00
-- url     : https://prove2.me/submissions/cb41d855-175e-41d6-a021-170fe7cfef3e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EHcChange
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem psi_add_hermitian_curvature (D : Mat k r →L[ℝ] E) (g A B : Mat k r) :
    Psi D g (A + B) = Psi D g A + Psi D g B := by
  have h1 : hpart1 (Hpk k r) (A + B) = hpart1 (Hpk k r) A + hpart1 (Hpk k r) B := by
    simp only [hpart1, Matrix.conjTranspose_add, mul_add, add_mul]
    rw [← smul_add]
    congr 1
    abel
  have h2 : hpart2 (Hpk k r) (A + B) = hpart2 (Hpk k r) A + hpart2 (Hpk k r) B := by
    simp only [hpart2, Matrix.conjTranspose_add, mul_add, add_mul]
    rw [← smul_add]
    congr 1
    abel
  simp only [Psi, h1, h2, mul_add, map_add, smul_add]
  abel
end Formalism.FourierDecayAlt.P.JFxE
end
end

set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution {ι : Type*} (s : Finset ι) (D : Mat k r →L[ℝ] E) (g : Mat k r) (Z : ι → Mat k r) :
    Psi D g (∑ i ∈ s, Z i) = ∑ i ∈ s, Psi D g (Z i) := by
  exact map_sum (AddMonoidHom.mk' (Psi D g) (psi_add_hermitian_curvature D g)) Z s
end Formalism.FourierDecayAlt.P.JFxE
