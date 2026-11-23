-- Prove2me | solution 1 for DensInertW.cg_gram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:05.648892+00:00
-- url     : https://prove2.me/submissions/1e49364f-75e7-4ccb-a6c2-9e29aff1983d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_RepCountCongruenceInvariant
import Theorems.Thm_DensInertW_cg_hf_left
import Theorems.Thm_DensInertW_cg_hf_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open DensInertW
namespace DensInertW
theorem _root_.solution (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] {m n : ℕ}
    (M : Matrix (Fin n) (Fin n) L) (Q G : Matrix (Fin m) (Fin m) L) (X : Fin m → Fin n → L)
    (hX : ∀ k l, hf (Fintype.card K) M (X k) (X l) = G k l) (i j : Fin m) :
    hf (Fintype.card K) M (cgComb Q X i) (cgComb Q X j) =
      (Q * G * (Q.map (fun y => y ^ Fintype.card K)).transpose) i j := by
  show hf (Fintype.card K) M (∑ k, Q i k • X k) (∑ l, Q j l • X l) = _
  rw [cg_hf_left]
  simp only [cg_hf_right K L, hX, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ l, ∑ k, Q i k * (Q j l ^ Fintype.card K * G k l) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
end DensInertW
