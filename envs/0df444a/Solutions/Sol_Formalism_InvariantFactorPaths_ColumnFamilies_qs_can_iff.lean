-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_can_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:02.967837+00:00
-- url     : https://prove2.me/submissions/58046b1e-36f0-4bdd-9301-911de2a7ff21

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_colH_strip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mem_D
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ini_erase
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ext_can
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
    (m : ↥(qs_D lam kap) → Fin n) :
    ((∀ c : ↥(qs_D lam kap), m c ∈ qs_ext kap (canT kap) c.1) ∧
      qs_ext lam (canT lam) = qs_rem (qs_D lam kap) (qs_ext kap (canT kap)) m) ↔ m = qs_mc lam kap := by
  constructor
  · rintro ⟨h1, h2⟩
    funext c
    have h3 := h1 c
    have h4 := congrFun h2 c.1
    have h5 := (qs_mem_D hl hk c.1).1 c.2
    rw [qs_rem_mem, qs_ext_can hl, qs_ext_can hk] at h4
    rw [qs_ext_can hk] at h3
    have h6 : m c ∉ (qs_ini (colH lam c.1) : Finset (Fin n)) := by rw [h4]; simp
    simp only [qs_ini, mem_filter, mem_univ, true_and] at h3 h6
    exact Fin.ext (by simp only [qs_mc]; omega)
  · rintro rfl
    refine ⟨fun c => ?_, ?_⟩
    · have h5 := (qs_mem_D hl hk c.1).1 c.2
      rw [qs_ext_can hk]
      simp only [qs_ini, qs_mc, mem_filter, mem_univ, true_and]; omega
    · funext c
      by_cases hc : c ∈ qs_D lam kap
      · have h5 := (qs_mem_D hl hk c).1 hc
        have h6 := qs_rem_mem (qs_D lam kap) (qs_ext kap (canT kap)) (qs_mc lam kap) ⟨c, hc⟩
        simp only at h6
        rw [h6, qs_ext_can hl, qs_ext_can hk, h5]
        exact (qs_ini_erase _ _).symm
      · rw [qs_rem_not _ _ _ hc, qs_ext_can hl, qs_ext_can hk]
        have h7 := qs_colH_strip hl hk hs c
        have h8 := (qs_mem_D hl hk c).not.1 hc
        congr 1; omega
end Formalism.InvariantFactorPaths.ColumnFamilies
