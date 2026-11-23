-- Prove2me | solution 1 for DensInertW.cg_hf_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:28.980193+00:00
-- url     : https://prove2.me/submissions/6f83cac5-843a-4fee-90c8-5dec8872f32b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_RepCountCongruenceInvariant

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
theorem _root_.solution {L : Type} [Field L] {m n : ℕ} (q : ℕ) (M : Matrix (Fin n) (Fin n) L)
    (c : Fin m → L) (x : Fin m → Fin n → L) (y : Fin n → L) :
    hf q M (∑ k, c k • x k) y = ∑ k, c k * hf q M (x k) y := by
  have e1 : ∀ a b, (∑ k, c k * x k a) * M a b * y b ^ q =
      ∑ k, c k * (x k a * M a b * y b ^ q) := fun a b => by
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e1, Finset.mul_sum]
  calc _ = ∑ a, ∑ k, ∑ b, c k * (x k a * M a b * y b ^ q) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm
end DensInertW
