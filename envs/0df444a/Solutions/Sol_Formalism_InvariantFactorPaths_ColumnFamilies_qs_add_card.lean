-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_add_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:07.64223+00:00
-- url     : https://prove2.me/submissions/0334ac60-adf8-4534-9ad2-2bef4ebc3106

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_colH_strip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mem_D
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_add_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_add_not


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (J : ℤ → Finset (Fin n)) (hJ : ∀ c, (J c).card = colH lam c) (a : ↥(qs_D lam kap) → Fin n)
    (ha : ∀ c : ↥(qs_D lam kap), a c ∉ J c.1) (c : ℤ) : (qs_add (qs_D lam kap) J a c).card = colH kap c := by
  by_cases hc : c ∈ qs_D lam kap
  · have h5 := (qs_mem_D hl hk c).1 hc
    have h6 := qs_add_mem (qs_D lam kap) J a ⟨c, hc⟩
    simp only at h6
    rw [h6, Finset.card_insert_of_notMem (ha ⟨c, hc⟩), hJ, h5]
  · rw [qs_add_not _ _ _ hc, hJ]
    have h7 := qs_colH_strip hl hk hs c
    have h8 := (qs_mem_D hl hk c).not.1 hc
    omega
end Formalism.InvariantFactorPaths.ColumnFamilies
