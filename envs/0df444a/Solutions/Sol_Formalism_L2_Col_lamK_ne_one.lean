-- Prove2me | solution 1 for Formalism.L2.Col.lamK_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:14:12.310704+00:00
-- url     : https://prove2.me/submissions/6ac4ef22-2706-488e-9d69-5dd1b1922862

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
import Theorems.Thm_Formalism_L2_Col_dGL_mem_HK
import Theorems.Thm_Formalism_L2_Col_detChar_dGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
namespace Formalism.L2.Col
theorem _root_.solution (χ : ℕ → κˣ →* Kˣ) {r : ℕ} (bl : List ℕ) (i₀ : Fin n) {s : ℕ} (hs : s < bl.length)
    (h₀ : coarse r bl i₀.val = s + 1) (hχ : χ s ≠ 1) : lamK χ n r bl ≠ 1 := by
  intro h
  obtain ⟨u, hu⟩ : ∃ u, χ s u ≠ 1 := by
    by_contra hcon; push_neg at hcon; exact hχ (MonoidHom.ext hcon)
  have hr : r ≤ i₀.val := by
    by_contra hh
    have : coarse r bl i₀.val = 0 := by simp only [coarse, blkIdx, if_pos (by omega : i₀.val < r)]
    omega
  have h1 := congrArg (fun f => f ⟨dGL i₀ u, dGL_mem_HK bl i₀ hr u⟩) h
  simp only [MonoidHom.one_apply] at h1
  unfold lamK at h1
  rw [MonoidHom.comp_apply] at h1
  have e : Subgroup.inclusion (HK_le_blockUT n κ r bl) ⟨dGL i₀ u, dGL_mem_HK bl i₀ hr u⟩ = ⟨dGL i₀ u, dGL_mem_btG _ i₀ u⟩ := rfl
  rw [e, detChar_dGL χ bl i₀ hs h₀ u] at h1
  exact hu h1
end Formalism.L2.Col
