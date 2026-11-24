-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_rho_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:31:38.500941+00:00
-- url     : https://prove2.me/submissions/3926b8f2-afc7-474e-90f0-f498d077974d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_ofIcc
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_rho_bounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution (Q : M.Par) (hg : ∀ i ∈ Icc 1 (Q.k - 1), Q.lo i ≤ Q.hi i) (π : M.Ty Q) :
    ∀ i, 1 ≤ i → i + 1 ≤ Q.k - 1 → M.rho Q π (i + 1) < M.rho Q π i := by
  intro i h1 h2
  obtain ⟨j, rfl⟩ := cb_ofIcc (n := Q.k - 1) h1 (by omega)
  have b1 := (cb_rho_bounds Q hg π ⟨j.1 + 1, by omega⟩).2
  have b0 := (cb_rho_bounds Q hg π j).1
  have hm := min_le_max (a := Q.u (j.1 + 1 + 1)) (b := Q.u' (j.1 + 1 + 1))
  have e1 : Q.hi (j.1 + 1 + 1) = min (Q.u (j.1 + 1 + 1)) (Q.u' (j.1 + 1 + 1)) - 1 / 2 := rfl
  have e2 : Q.lo (j.1 + 1) = max (Q.u (j.1 + 1 + 1)) (Q.u' (j.1 + 1 + 1)) + 1 / 2 := rfl
  simp only at b1
  linarith
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
