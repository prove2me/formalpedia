-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.gal_cmF_cases
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:26.449454+00:00
-- url     : https://prove2.me/submissions/33659e27-13cc-41a9-9863-92377a9d26bb

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjF_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_star_ne
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_finrank_cmF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable (K : Type) [Field K] [NumberField K] [StarRing K]
variable {K}
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (g : K ≃ₐ[cmF K] K) : g = 1 ∨ g = conjF K := by
  classical
  have h1c : (1 : K ≃ₐ[cmF K] K) ≠ conjF K := by
    intro e
    obtain ⟨a, ha⟩ := exists_star_ne hK
    apply ha
    have := DFunLike.congr_fun e a
    rw [AlgEquiv.one_apply, conjF_apply] at this
    exact this.symm
  by_contra h
  push_neg at h
  have h2 : Fintype.card (K ≃ₐ[cmF K] K) ≤ 2 := by
    convert (AlgEquiv.card_le (F := cmF K) (K := K)).trans (finrank_cmF hK).le
  have hle : ({g, 1, conjF K} : Finset (K ≃ₐ[cmF K] K)).card ≤ 2 := (Finset.card_le_univ _).trans h2
  rw [Finset.card_insert_of_notMem (by simp [h.1, h.2]), Finset.card_pair h1c] at hle
  omega
end Formalism.HermitianLattices.Ext.L3
