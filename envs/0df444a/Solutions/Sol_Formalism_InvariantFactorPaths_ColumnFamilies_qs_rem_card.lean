-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_rem_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:09.599772+00:00
-- url     : https://prove2.me/submissions/94ed21ac-ffed-40ee-93d5-a1d1a5b5140e

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_colH_strip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mem_D
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_rem_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_rem_not


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
    (K : ℤ → Finset (Fin n)) (hK : ∀ c, (K c).card = colH kap c) (m : ↥(qs_D lam kap) → Fin n)
    (hm : ∀ c : ↥(qs_D lam kap), m c ∈ K c.1) (c : ℤ) : (qs_rem (qs_D lam kap) K m c).card = colH lam c := by
  by_cases hc : c ∈ qs_D lam kap
  · have h5 := (qs_mem_D hl hk c).1 hc
    have h6 := qs_rem_mem (qs_D lam kap) K m ⟨c, hc⟩
    simp only at h6
    rw [h6, Finset.card_erase_of_mem (hm ⟨c, hc⟩), hK, h5]; rfl
  · rw [qs_rem_not _ _ _ hc, hK]
    have h7 := qs_colH_strip hl hk hs c
    have h8 := (qs_mem_D hl hk c).not.1 hc
    omega
end Formalism.InvariantFactorPaths.ColumnFamilies
