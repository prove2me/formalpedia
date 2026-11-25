-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.one_add_projection_mem_isotropic_set
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:27:15.659553+00:00
-- url     : https://prove2.me/submissions/74b88004-9fdf-48c5-933a-ddc676f54fbf

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangularFactorMiddleRow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_HermitianOrthogonalProjectionVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneAddProjectionMemIsotropicSet
import Theorems.Thm_NFOne_P_rowS
import Theorems.Thm_NFOne_P_rowWS_colW
import Theorems.Thm_NFOne_cols_X
import Theorems.Thm_NFOne_unitary_P
import Theorems.Thm_NFOne_z_fix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants
noncomputable section
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (j : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z') (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (V0 : ∀ c, j ≤ c → V c = 0)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val → V b q = if (NFOne.sg k r q).val = b then 1 else 0)
    (Viso : ∀ b c, b < j → c < j → herm (Hpk k r) (V b) (V c) = 0)
    (Vz : ∀ c, herm (Hpk k r) z' (V c) = 0) :
    (1 + NFOne.Pm k r j V) ∈ N0set k r z' := by
  refine ⟨NFOne.unitary_P k r j V V0 Vs Viso, fun a => NFOne.cols_X k r j V a,
    NFOne.z_fix k r j V z' hz Vz, fun p q hq1 hq2 hp => ?_, fun p q hq hp => ?_⟩
  · rw [Matrix.add_apply, NFOne.P_rowWS_colW k r j V p q hp hq2, add_zero, Matrix.one_apply]
  · rw [Matrix.add_apply, NFOne.P_rowS k r j V p q hp, add_zero, Matrix.one_apply]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
