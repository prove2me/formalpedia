-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.indexBasic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:22.092888+00:00
-- url     : https://prove2.me/submissions/382db56f-d831-4f3b-8f96-fe6be32e95f9

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_finLen
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_locLen_self
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_lidx_via
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_denom
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_locS_top
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_dual_le_fg
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_inf
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : IndexBasic := by
  intro R K V _ _ _ _ _ _ _ _ _ _ _ h hs hnd hstar p _ A B C hA hB hC
  have hfin : ∀ X Y : Submodule R V, X.FG → locS (nonZeroDivisors R) Y = ⊤ →
      Module.length R (↥(localization₂ p X) ⧸ (localization₂ p Y).comap (localization₂ p X).subtype) ≠ ⊤ := by
    intro X Y hX hY
    obtain ⟨d, hd, hdY⟩ :=
      indexBasic_denom (nonZeroDivisors R) X Y hX (by rw [hY]; exact le_top)
    exact Module.length_ne_top_iff.mpr (indexBasic_finLen p X Y hX hd hdY)
  have hAt := indexBasic_locS_top (K := K) A (Submodule.IsLattice.span_eq_top (self := hA))
  have hBt := indexBasic_locS_top (K := K) B (Submodule.IsLattice.span_eq_top (self := hB))
  have hCt := indexBasic_locS_top (K := K) C (Submodule.IsLattice.span_eq_top (self := hC))
  have hAfg : A.FG := Submodule.IsLattice.fg (self := hA)
  have hBfg : B.FG := Submodule.IsLattice.fg (self := hB)
  have hCfg : C.FG := Submodule.IsLattice.fg (self := hC)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold lidx
    exact sub_self _
  · unfold lidx
    rw [inf_comm]
    ring
  · have hDt : locS (nonZeroDivisors R) (A ⊓ B ⊓ C) = ⊤ := by
      rw [locBasic_locS_inf, locBasic_locS_inf, hAt, hBt, hCt]
      simp
    have hAD := hfin A _ hAfg hDt
    have hBD := hfin B _ hBfg hDt
    have hCD := hfin C _ hCfg hDt
    rw [indexBasic_lidx_via p A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right
        hAD hCD,
      indexBasic_lidx_via p A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
        (le_trans inf_le_left inf_le_right) hAD hBD,
      indexBasic_lidx_via p B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right) inf_le_right
        hBD hCD]
    ring
  · intro hBA
    unfold lidx
    rw [inf_eq_right.mpr hBA, indexBasic_locLen_self]
    simp
  · intro hU
    unfold jIdx
    rw [show dual h A = A from hU]
    unfold lidx
    exact sub_self _
  · intro hI
    have hle : A ≤ dual h A := by
      intro x hx
      rw [dualBasic_mem_dual]
      intro y hy
      exact hI y hy x hx
    have hDfg : (dual h A).FG := by
      obtain ⟨F, hF, hDF⟩ :=
        indexBasic_dual_le_fg h hnd A (Submodule.IsLattice.span_eq_top (self := hA))
      exact hF.of_le hDF
    have hDfin := hfin (dual h A) A hDfg hAt
    unfold jIdx lidx
    rw [inf_eq_left.mpr hle, indexBasic_locLen_self]
    refine ⟨by simp, ?_⟩
    rw [Nat.cast_zero, zero_sub, neg_eq_zero, Nat.cast_eq_zero]
    unfold locLen
    rw [ENat.toNat_eq_zero]
    constructor
    · rintro (h0 | htop)
      · rw [Module.length_eq_zero_iff] at h0
        apply le_antisymm
        · intro x hx
          have h1 : (Submodule.Quotient.mk ⟨x, hx⟩ : ↥(localization₂ p (dual h A)) ⧸
              (localization₂ p A).comap (localization₂ p (dual h A)).subtype) = 0 := Subsingleton.elim _ _
          rw [Submodule.Quotient.mk_eq_zero] at h1
          exact h1
        · exact locBasic_locS_mono _ hle
      · exact absurd htop hDfin
    · intro heq
      left
      rw [Module.length_eq_zero_iff]
      have htop' : (localization₂ p A).comap (localization₂ p (dual h A)).subtype = ⊤ := by
        rw [eq_top_iff]
        rintro ⟨x, hx⟩ -
        rw [heq] at hx
        exact hx
      rw [htop']
      infer_instance
end Formalism.HermitianLatticesTheory
