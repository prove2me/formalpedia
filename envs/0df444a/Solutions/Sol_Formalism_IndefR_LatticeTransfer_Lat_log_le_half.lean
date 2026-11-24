-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.Lat.log_le_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:59.33282+00:00
-- url     : https://prove2.me/submissions/ac268836-e399-4aaf-b49e-d6652b8f89c7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_MemSpanOfSmulMem
import Definitions.Def_Formalism_BranchSandwichDivisors_DivFromPassageAndNorm
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransferOfFacts
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement Formalism.HN _root_.Formalism.IndefR.LatticeTransfer.Lat
namespace Formalism.IndefR.LatticeTransfer
namespace Lat
theorem _root_.solution {n N : ℕ} (h : n ^ 2 ≤ N) :
    Real.log n ≤ Real.log N / 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := Real.log_natCast_nonneg N
    simp only [Nat.cast_zero, Real.log_zero]
    linarith
  · have h1 : Real.log ((n : ℝ) ^ 2) ≤ Real.log N :=
      Real.log_le_log (by positivity) (by exact_mod_cast h)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
end Lat
end Formalism.IndefR.LatticeTransfer
