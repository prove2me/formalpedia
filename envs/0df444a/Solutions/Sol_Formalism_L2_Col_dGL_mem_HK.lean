-- Prove2me | solution 1 for Formalism.L2.Col.dGL_mem_HK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:54:15.551863+00:00
-- url     : https://prove2.me/submissions/bc27b02d-c087-4202-83bc-eab506905093

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount

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
theorem _root_.solution {r : ℕ} (bl : List ℕ) (i₀ : Fin n) (h₀ : r ≤ i₀.val) (u : κˣ) : dGL i₀ u ∈ HK n κ r bl := by
  refine ⟨⟨dGL i₀ u, dGL_mem_btG _ i₀ u⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  ext i j
  rw [blkHom_apply, dGL_val]
  have hi : (i.1 : Fin n).val < r := by
    by_contra hh
    exact absurd i.2 (by simp only [coarse, blkIdx, if_neg hh]; omega)
  by_cases hij : i = j
  · subst hij
    have hne : (i.1 : Fin n) ≠ i₀ := fun e => by rw [← e] at h₀; omega
    simp [Function.update_apply, hne]
  · have hne : (i.1 : Fin n) ≠ j.1 := fun e => hij (Subtype.ext e)
    simp [hij, hne]
end Formalism.L2.Col
