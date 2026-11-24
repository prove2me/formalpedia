-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_eq_of_prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:33:50.196797+00:00
-- url     : https://prove2.me/submissions/2fb74760-3db2-484a-a1f4-3d7acf6a062d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_mem_of_prod_eq
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_range_sub_of_mem
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_strictMono_of_anti
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
theorem _root_.solution {n : ℕ} {a b : ℕ → ℝ}
    (ha : ∀ i, 1 ≤ i → i + 1 ≤ n → a (i + 1) < a i) (hb : ∀ i, 1 ≤ i → i + 1 ≤ n → b (i + 1) < b i)
    (h : ∀ Y : ℂ, ∏ i ∈ Icc 1 n, (Y + (a i : ℂ)) = ∏ i ∈ Icc 1 n, (Y + (b i : ℂ))) :
    ∀ i ∈ Icc 1 n, a i = b i := by
  have hr : Set.range (fun j : Fin n => -a (j.1 + 1)) = Set.range (fun j : Fin n => -b (j.1 + 1)) :=
    Set.Subset.antisymm (cb_range_sub_of_mem (cb_mem_of_prod_eq h))
      (cb_range_sub_of_mem (cb_mem_of_prod_eq (fun Y => (h Y).symm)))
  have hf := ((cb_strictMono_of_anti ha).range_inj (cb_strictMono_of_anti hb)).mp hr
  intro i hi
  have h1 := (Finset.mem_Icc.mp hi).1
  have h1' := (Finset.mem_Icc.mp hi).2
  have h2 : -a (i - 1 + 1) = -b (i - 1 + 1) := congrFun hf ⟨i - 1, by omega⟩
  rw [Nat.sub_add_cancel h1] at h2
  linarith
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
