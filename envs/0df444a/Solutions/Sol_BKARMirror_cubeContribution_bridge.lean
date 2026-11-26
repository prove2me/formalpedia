-- Prove2me | solution 1 for BKARMirror.cubeContribution_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:21:46.592713+00:00
-- url     : https://prove2.me/submissions/991fc3a0-c3ad-47ac-9a89-9b979931be97

import Mathlib
import Definitions.Def_BKAR
import Definitions.Def_Audit_ForestFormula_SolutionBasic
import Theorems.Thm_BKARMirror_standardInterp_bridge
import Theorems.Thm_BKARMirror_mixedPartial_bridge
import Theorems.Thm_BKAR_ForestIndex_cubeContribution_eq_canonicalGrownForestForSupport
import Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_edges
import Theorems.Thm_BKAR_Forest_cubeContribution_eq_of_edges_eq
import Theorems.Thm_BKAR_Forest_nonempty_activeExtensionChoice


set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
open BKARMirror
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKARMirror
theorem _root_.solution (J : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : ContDiffHyp ρ) :
    cubeContribution J ρ = (indexEquiv J).cubeContribution ρ := by
  classical
  obtain ⟨data⟩ := (acyclic_bridge J.edges).mp J.acyclic
  obtain ⟨choices⟩ := BKAR.Forest.nonempty_activeExtensionChoice V
  -- Core: the mirror integral equals the repository cube contribution.
  have hcore : cubeContribution J ρ = (data.toForest).cubeContribution ρ := by
    unfold cubeContribution BKAR.Forest.cubeContribution
    apply setIntegral_congr_fun
      (MeasurableSet.univ_pi fun _ => measurableSet_Icc)
    intro u hu
    have hu' : ∀ e : {e : Edge V // e ∈ J.edges}, 0 ≤ u e ∧ u e ≤ 1 :=
      fun e => Set.mem_Icc.mp (Set.mem_univ_pi.mp hu e)
    show mixedPartial J ρ (standardInterp J u)
      = (data.toForest).mixedPartial ρ ((data.toForest).standardInterp u)
    rw [standardInterp_bridge J data u hu']
    exact congrFun (mixedPartial_bridge J data ρ) _
  rw [hcore,
    BKAR.ForestIndex.cubeContribution_eq_canonicalGrownForestForSupport
      (indexEquiv J) choices ρ hρ]
  apply BKAR.Forest.cubeContribution_eq_of_edges_eq
  · rw [BKAR.Forest.canonicalGrownForestForSupport_edges]
    rfl
  · exact hρ
end BKARMirror
