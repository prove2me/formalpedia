-- Prove2me | solution 1 for Formalism.L2.Col.blkDet_dGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:54:17.372837+00:00
-- url     : https://prove2.me/submissions/2d3d5ebb-f22f-4efb-99f2-9648d46ab6e5

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
theorem _root_.solution (β : ℕ → ℕ) (c : ℕ) (i₀ : Fin n) (u : κˣ) :
    blkDet n κ β c ⟨dGL i₀ u, dGL_mem_btG β i₀ u⟩ = if β i₀.val = c then u else 1 := by
  apply Units.ext
  change Matrix.det ((dGL i₀ u : Matrix (Fin n) (Fin n) κ).toSquareBlock (fun i => β i.val) c) = _
  rw [dGL_val]
  have hd : (Matrix.diagonal fun i => ((Function.update (1 : Fin n → κˣ) i₀ u i : κˣ) : κ)).toSquareBlock (fun i => β i.val) c =
      Matrix.diagonal (fun i : {i : Fin n // β i.val = c} => ((Function.update (1 : Fin n → κˣ) i₀ u i.1 : κˣ) : κ)) := by
    ext i j
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.diagonal_apply, Subtype.ext_iff]
  rw [hd, Matrix.det_diagonal]
  split_ifs with hc
  · rw [Finset.prod_eq_single ⟨i₀, hc⟩]
    · simp
    · intro b _ hb
      rw [Function.update_apply, if_neg (fun e => hb (Subtype.ext e))]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Units.val_one]
    apply Finset.prod_eq_one
    intro b _
    rw [Function.update_apply, if_neg (fun e => hc (by rw [← e]; exact b.2))]
    simp
end Formalism.L2.Col
