-- Prove2me | solution 1 for BKAR.Forest.thresholdConnected_iff_exists_le_pathMin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:09:37.810975+00:00
-- url     : https://prove2.me/submissions/0c51a011-9d59-4398-a521-fcfc8c1955fb

import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_Threshold
import Theorems.Thm_BKAR_Forest_le_pathMin_of_forall_edges
import Theorems.Thm_BKAR_Forest_forall_edges_of_le_pathMin
import Theorems.Thm_BKAR_Forest_pathInF_isSimple
import Theorems.Thm_BKAR_Forest_pathInF_unique


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} (hs : s ≤ 1) (i j : V) :
    F.thresholdConnected u s i j ↔
      ∃ h : F.inSameComponent i j,
        s ≤ F.pathMin u (F.pathInF i j h) := by
  constructor
  · rintro ⟨γ, hγ, hall⟩
    let hcomp : F.inSameComponent i j := F.inSameComponent_of_isSimplePath hγ
    refine ⟨hcomp, ?_⟩
    have hpath : γ = F.pathInF i j hcomp :=
      F.pathInF_unique hcomp γ hγ
    rw [← hpath]
    exact F.le_pathMin_of_forall_edges u hs γ hall
  · rintro ⟨hcomp, hmin⟩
    refine ⟨F.pathInF i j hcomp, F.pathInF_isSimple hcomp, ?_⟩
    exact F.forall_edges_of_le_pathMin u (F.pathInF i j hcomp) hmin
end BKAR.Forest
