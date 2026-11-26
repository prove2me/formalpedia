-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.interpWithFill_extend_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:24:03.45698+00:00
-- url     : https://prove2.me/submissions/787baca1-b0a3-4608-b047-f1524f6c7981

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_pathMin_eq_of_forall
import Theorems.Thm_BKAR_Forest_le_pathMin_of_mem_forall
import Theorems.Thm_BKAR_Forest_pathMin_le_of_mem_eq
import Theorems.Thm_BKAR_Forest_EdgeExtension_paramValue_extend_new
import Theorems.Thm_BKAR_Forest_EdgeExtension_paramValue_extend_old
import Theorems.Thm_BKAR_Forest_EdgeExtension_paramValue_extend_le
import Theorems.Thm_BKAR_Forest_edge_mem_of_isSimplePath
import Theorems.Thm_BKAR_Forest_pathInF_isSimple


set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e₀ : Edge V}
namespace BKAR.Forest.EdgeExtension
theorem _root_.solution (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) {s : ℝ}
    (hu : ∀ e : F.EdgeParam, s ≤ u e) :
    F.interpWithFill u s = F'.interpWithFill (h.extendParam u s) s := by
  funext e
  by_cases hF : F.inSameComponent e.left e.right
  · rw [interpWithFill, dif_pos hF, interpWithFill,
      dif_pos (h.old_component hF), h.old_path hF]
    apply pathMin_eq_of_forall
    intro e' he'
    have heF : e' ∈ F.edges :=
      F.edge_mem_of_isSimplePath (F.pathInF_isSimple hF) e' he'
    exact (h.paramValue_extend_old u s heF).symm
  · by_cases hF' : F'.inSameComponent e.left e.right
    · rw [interpWithFill, dif_neg hF, interpWithFill, dif_pos hF']
      have huse : e₀ ∈ F'.pathInF e.left e.right hF' :=
        h.new_path_uses hF hF'
      have hlower :
          s ≤ F'.pathMin (h.extendParam u s)
            (F'.pathInF e.left e.right hF') :=
        F'.le_pathMin_of_mem_forall (h.extendParam u s) huse
          (fun e' he' => by
            have heF' : e' ∈ F'.edges :=
              F'.edge_mem_of_isSimplePath (F'.pathInF_isSimple hF') e' he'
            exact h.paramValue_extend_le u hu heF')
      have hupper :
          F'.pathMin (h.extendParam u s)
            (F'.pathInF e.left e.right hF') ≤ s :=
        F'.pathMin_le_of_mem_eq (h.extendParam u s) huse
          (h.paramValue_extend_new u s)
      exact (le_antisymm hupper hlower).symm
    · rw [interpWithFill, dif_neg hF, interpWithFill, dif_neg hF']
end BKAR.Forest.EdgeExtension
