-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.lowUni_mulVec_eLast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:28.65177+00:00
-- url     : https://prove2.me/submissions/39b52c74-4337-4335-89af-149aa5785189

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast

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
theorem _root_.solution {M : Matrix (Fin n) (Fin n) K} (h : IsLowUni M) :
    M *ᵥ coeLin R (eLast R) = coeLin R (eLast R) := by
  have hw : ∀ j : Fin n, coeLin R (eLast R) j = if j.val + 1 = n then 1 else 0 := by
    intro j
    rw [coeLin_apply]
    unfold eLast
    split_ifs <;> simp
  funext i
  rw [hw i]
  simp only [Matrix.mulVec, dotProduct, hw, mul_ite, mul_one, mul_zero]
  by_cases hi : i.val + 1 = n
  · rw [if_pos hi, Finset.sum_eq_single i]
    · rw [if_pos hi, h.2 i]
    · intro j _ hj
      rw [if_neg]
      intro hj'
      exact hj (Fin.ext (by omega))
    · intro hi'
      exact absurd (Finset.mem_univ i) hi'
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with hj
    · have hij : i < j := Fin.lt_def.mpr (by have := i.isLt; omega)
      exact h.1 hij
    · rfl
end Formalism.DoubleCosetMeasures.P
