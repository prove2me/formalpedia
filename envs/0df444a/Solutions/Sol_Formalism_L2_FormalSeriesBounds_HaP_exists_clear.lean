-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.HaP.exists_clear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:14.207432+00:00
-- url     : https://prove2.me/submissions/50cca3f6-6555-4337-ac2a-f6ee20f918de

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
namespace Formalism.L2.FormalSeriesBounds.HaP
theorem _root_.solution (s : Type) [Fintype s] (u : s → ℚ) :
    ∃ N : ℕ, N ≠ 0 ∧ ∃ z : s → ℤ, ∀ b, (z b : ℚ) = N * u b := by
  refine ⟨∏ b, (u b).den, Finset.prod_ne_zero_iff.mpr fun b _ => (u b).den_nz,
    fun b => (∏ b' ∈ Finset.univ.erase b, ((u b').den : ℤ)) * (u b).num, fun b => ?_⟩
  have hq : u b * ((u b).den : ℚ) = ((u b).num : ℚ) := Rat.mul_den_eq_num (u b)
  rw [← Finset.mul_prod_erase Finset.univ (fun b' => (u b').den) (Finset.mem_univ b)]
  push_cast
  rw [← hq]
  ring
end Formalism.L2.FormalSeriesBounds.HaP
