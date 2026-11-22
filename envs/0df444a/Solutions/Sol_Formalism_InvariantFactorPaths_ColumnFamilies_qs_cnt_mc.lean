-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_cnt_mc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:54:38.616298+00:00
-- url     : https://prove2.me/submissions/64e0e25f-14d2-4bc1-ab70-45c044efb2cf

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_colH_strip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mem_D
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_lt_colH_iff


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
    (x : Fin n) : ((qs_cnt (qs_mc lam kap) x : ℕ) : ℤ) = kap x - lam x := by
  have h1 : (univ.filter fun c : ↥(qs_D lam kap) => qs_mc lam kap c = x).map (Function.Embedding.subtype _) =
      Finset.Ioc (lam x) (kap x) := by
    ext c
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype, Subtype.exists,
      exists_and_right, exists_eq_right, mem_Ioc]
    have e1 := qb_lt_colH_iff hl c x
    have e2 := qb_lt_colH_iff hk c x
    constructor
    · rintro ⟨hc, hx⟩
      have h3 := (qs_mem_D hl hk c).1 hc
      have h4 : colH lam c = x.1 := congrArg Fin.val hx
      constructor
      · by_contra hcon; have := e1.2 (not_lt.1 hcon); omega
      · exact e2.1 (by omega)
    · rintro ⟨h3, h4⟩
      have h5 := e2.2 h4
      have h6 : ¬ x.1 < colH lam c := fun h => absurd (e1.1 h) (not_le.2 h3)
      have h7 := qs_colH_strip hl hk hs c
      exact ⟨(qs_mem_D hl hk c).2 (by omega), Fin.ext (by simp only [qs_mc]; omega)⟩
  rw [qs_cnt, ← Finset.card_map (Function.Embedding.subtype _), h1, Int.card_Ioc,
    Int.toNat_of_nonneg (by have := hs.1 x; omega)]
end Formalism.InvariantFactorPaths.ColumnFamilies
