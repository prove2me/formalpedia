-- Prove2me | solution 1 for BKAR.Forest.le_standardInterp_iff_thresholdConnected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:10:19.984292+00:00
-- url     : https://prove2.me/submissions/d9cf793c-9c0e-42f9-b2c8-d9ca41948ec9

import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_Threshold
import Theorems.Thm_BKAR_Forest_thresholdConnected_iff_exists_le_pathMin
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathInF_eq_of_edges_eq
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil



set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (e : Edge V) :
    s ≤ F.standardInterp u e ↔
      F.thresholdConnected u s e.left e.right := by
  by_cases hcomp : F.inSameComponent e.left e.right
  · rw [standardInterp, dif_pos hcomp]
    constructor
    · intro hmin
      exact (F.thresholdConnected_iff_exists_le_pathMin u hs1 e.left e.right).mpr
        ⟨hcomp, hmin⟩
    · intro hconn
      rcases (F.thresholdConnected_iff_exists_le_pathMin u hs1 e.left e.right).mp
          hconn with
        ⟨hcomp', hmin⟩
      have hpath :
          F.pathInF e.left e.right hcomp' =
            F.pathInF e.left e.right hcomp :=
        F.pathInF_eq_of_edges_eq F rfl hcomp' hcomp
      simpa [hpath] using hmin
  · rw [standardInterp, dif_neg hcomp]
    constructor
    · intro hle
      exact False.elim ((not_le_of_gt hs0) hle)
    · intro hconn
      rcases hconn with ⟨γ, hγ, _hall⟩
      exact False.elim (hcomp (F.inSameComponent_of_isSimplePath hγ))
end BKAR.Forest
