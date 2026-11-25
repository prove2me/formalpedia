-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.valuation_nonneg_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:34:24.263434+00:00
-- url     : https://prove2.me/submissions/314f3907-c99a-4519-83e1-ae279a489446

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_valuation_nonneg_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
theorem _root_.solution {a : C} {n : ℕ} (h : V.Ge 0 (a ^ n)) (hn : n ≠ 0) : V.Ge 0 a := by
  rw [valuation_nonneg_iff] at *
  rw [V.v.map_pow] at h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_contra hlt
  push_neg at hlt
  rw [succ_nsmul] at h
  have h1 : m • V.v a ≤ 0 := nsmul_nonpos hlt.le m
  exact absurd h (not_le.mpr (lt_of_le_of_lt (le_of_le_of_eq (add_le_add h1 le_rfl) (zero_add _)) hlt))
end Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
