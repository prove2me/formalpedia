-- Prove2me | solution 1 for Formalism.HC.Der.Rd.mul_mem_KK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:57.112796+00:00
-- url     : https://prove2.me/submissions/9bd86aca-eaf6-4fe8-80df-11bc99422120

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Theorems.Thm_Formalism_HC_Der_Rd_mem_ker_iff
import Theorems.Thm_Formalism_HC_Der_Rd_mem_KK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ArithmeticFunction Finset
noncomputable section
namespace Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N]
private theorem mem_KK_iff_mem_ker_unitsMap {f : ℕ} (hf : f ∣ N) {u : (ZMod N)ˣ} :
    u ∈ KK N f ↔ u ∈ (ZMod.unitsMap hf).ker := by
  rw [mem_KK, mem_ker_iff hf]
end Formalism.HC.Der.Rd
end
end

set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N]
namespace Formalism.HC.Der.Rd
theorem _root_.solution {f : ℕ} (hf : f ∣ N) {u v : (ZMod N)ˣ} (hu : u ∈ KK N f) (hv : v ∈ KK N f) : u * v ∈ KK N f := by
  rw [mem_KK_iff_mem_ker_unitsMap hf] at hu hv ⊢
  exact mul_mem hu hv
end Formalism.HC.Der.Rd
