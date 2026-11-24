-- Prove2me | solution 1 for Formalism.L2.Col.detChar_dGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:10:27.997785+00:00
-- url     : https://prove2.me/submissions/9ede6391-8e9c-420b-a435-7927227592e7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
import Theorems.Thm_Formalism_L2_Col_blkDet_dGL

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
theorem _root_.solution (χ : ℕ → κˣ →* Kˣ) {a : ℕ} (bl : List ℕ) (i₀ : Fin n) {s : ℕ} (hs : s < bl.length)
    (h₀ : coarse a bl i₀.val = s + 1) (u : κˣ) : detChar χ n a bl ⟨dGL i₀ u, dGL_mem_btG _ i₀ u⟩ = χ s u := by
  unfold detChar
  rw [MonoidHom.finset_prod_apply, Finset.prod_eq_single s]
  · rw [MonoidHom.comp_apply, blkDet_dGL, if_pos h₀]
  · intro c _ hc
    rw [MonoidHom.comp_apply, blkDet_dGL, if_neg (by omega), map_one]
  · intro h; exact absurd (Finset.mem_range.mpr hs) h
end Formalism.L2.Col
