-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.lastCoord_upUni
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:28.331778+00:00
-- url     : https://prove2.me/submissions/857a77f0-07f6-48ae-a547-b578e6a093c2

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_lastCoord_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution {M : Matrix (Fin n) (Fin n) K} (h : IsUpUni M) (w : Fin n → K) :
    lastCoord R (M *ᵥ w) = lastCoord R w := by
  rw [lastCoord_apply, lastCoord_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs with hj
  · simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single j]
    · rw [h.2 j, one_mul]
    · intro k _ hk
      have hne : k.val ≠ j.val := fun e => hk (Fin.ext e)
      have hkj : k < j := Fin.lt_def.mpr (by have := k.isLt; omega)
      rw [h.1 hkj, zero_mul]
    · intro hj'
      exact absurd (Finset.mem_univ j) hj'
  · rfl
end Formalism.DoubleCosetMeasures.P
