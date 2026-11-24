-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.pow_pred_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:33.711479+00:00
-- url     : https://prove2.me/submissions/dd4f4b1a-6a7c-4c4f-b20f-abb5574abe45

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_AffineFibreCountComparison
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_InvariantKernelTraceVanishes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedLatticeOperators Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
open Module Finset Matrix
variable {F : Type} [Field F] [Fintype F]
namespace Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
theorem _root_.solution {q a e : ℕ} (hq : 1 < q) (h : q * a = q ^ e) :
    1 ≤ e ∧ a = q ^ (e - 1) := by
  rcases e with _ | e
  · rw [pow_zero] at h
    have h1 : q ∣ 1 := ⟨a, h.symm⟩
    have h2 := Nat.le_of_dvd one_pos h1
    omega
  · refine ⟨by omega, ?_⟩
    rw [pow_succ'] at h
    simpa using Nat.eq_of_mul_eq_mul_left (by omega) h
end Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
