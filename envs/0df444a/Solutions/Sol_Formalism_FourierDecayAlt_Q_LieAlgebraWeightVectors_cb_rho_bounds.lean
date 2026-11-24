-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_rho_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:11:06.74022+00:00
-- url     : https://prove2.me/submissions/859146cc-753a-42ef-a66a-c4dc215dbaa5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_rho_eq__0ffcd36dceb3

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
theorem _root_.solution (Q : M.Par) (hg : ∀ i ∈ Icc 1 (Q.k - 1), Q.lo i ≤ Q.hi i) (π : M.Ty Q)
    (j : Fin (Q.k - 1)) : Q.lo (j.1 + 1) ≤ M.rho Q π (j.1 + 1) ∧ M.rho Q π (j.1 + 1) ≤ Q.hi (j.1 + 1) := by
  rw [cb_rho_eq' Q π j]
  have hj := j.2
  have hw : ((π j : Fin _) : ℕ) ≤ Q.wid (j.1 + 1) := by have := (π j).2; omega
  have hg' := hg (j.1 + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hf : ((Q.wid (j.1 + 1) : ℕ) : ℝ) ≤ Q.hi (j.1 + 1) - Q.lo (j.1 + 1) :=
    Nat.floor_le (sub_nonneg.mpr hg')
  have hw' : (((π j : Fin _) : ℕ) : ℝ) ≤ (Q.wid (j.1 + 1) : ℝ) := by exact_mod_cast hw
  have h0 : (0 : ℝ) ≤ (((π j : Fin _) : ℕ) : ℝ) := Nat.cast_nonneg _
  constructor <;> linarith
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
