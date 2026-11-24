-- Prove2me | solution 1 for Formalism.L2.Col.lamQ_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:14:14.916183+00:00
-- url     : https://prove2.me/submissions/1e1fad47-5393-417a-b01a-da05650cedb2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
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
theorem _root_.solution {ξ : κˣ →* Kˣ} {a b : ℕ} (hb : 0 < b) (hn : a + b ≤ n) (hξ : ξ ≠ 1) : lamQ ξ n a b ≠ 1 := by
  intro h
  obtain ⟨u, hu⟩ : ∃ u, ξ u ≠ 1 := by
    by_contra hcon; push_neg at hcon; exact hξ (MonoidHom.ext hcon)
  have hc : coarse a [b] (⟨a, by omega⟩ : Fin n).val = 0 + 1 := by
    simp [coarse, blkIdx, hb]
  have h1 := congrArg (fun f => f ⟨dGL (⟨a, by omega⟩ : Fin n) u, dGL_mem_btG _ _ u⟩) h
  simp only [MonoidHom.one_apply] at h1
  unfold lamQ at h1
  rw [detChar_dGL (fun _ => ξ) [b] _ (by simp) hc u] at h1
  exact hu h1
end Formalism.L2.Col
