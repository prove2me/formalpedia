-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.example_exists_slopeBound_conditions_of_jacobiSym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:20:34.734537+00:00
-- url     : https://prove2.me/submissions/fab644ab-9342-451a-9448-aab36f987739

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_IndefiniteTreeX
import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeFullAssemblyWeighted
import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_SlopeBoundSingleLiftOfDefinitions
import Theorems.Thm_Formalism_L2_Indef_Tree_leaves_satisfiable
import Theorems.Thm_Formalism_L2_Indef_Tree_exampleSingleLift_ne_bot
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_main
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_UpperTheory_Reformulated_B_SelectionLemmas_main
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Finset Module NumberField Formalism.HN
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
attribute [instance] SlopeBoundParameters.fPl SlopeBoundParameters.dimNeZero
attribute [instance] SlopeBoundLiftData.fι SlopeBoundLiftData.nι
namespace Formalism.L2.Indef.Tree
theorem _root_.solution (v0 : InfinitePlace Examples₂.K3) (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n)
    (hχ : (∀ k : ℕ, χ k = ((jacobiSym k n : ℤ) : ℂ)) ∧ χ.IsPrimitive ∧ χ.Odd) (hper : PeriodIdentity n χ) :
    ∃ (P : SlopeBoundParameters) (F : (Examples₂.one.base Examples₂.K3 v0).J → SlopeBoundLiftData Examples₂.K3 P)
      (Zs : IndefScale (Examples₂.one.base Examples₂.K3 v0)),
      LeafKL P ∧ LeafCN P ∧ LeafFE P ∧ LeafDiff P ∧ LeafNorm P ∧ PageParams P ∧
      (∀ j, FacParams 0 (F j) ∧ LeafDegFlat 0 (F j) ∧ LeafExport 0 (F j) ∧ LeafCut (F j) ∧ LeafShareBad (F j) ∧
        LeafBadRows (F j) ∧ LeafMuN (F j) ∧ LeafLam (F j) ∧
        LeafRecord ((Examples₂.one.dat Examples₂.K3 v0).XW j) ((Examples₂.one.dat Examples₂.K3 v0).M j) (F j) ∧ LeafNote2 0 (F j) ∧
        LeafMeasure 0 (D := (Examples₂.one.dat Examples₂.K3 v0).D) ((Examples₂.one.dat Examples₂.K3 v0).XW j)
          ((Examples₂.one.dat Examples₂.K3 v0).XW j) ((Examples₂.one.dat Examples₂.K3 v0).M j) P ∧
        (F j).q' = 0 ∧ LeafDef 0 0 (F j)) ∧
      ScaleTies Zs P F := by
  have hfr := Examples₂.one.frames Examples₂.K3 v0
  obtain ⟨P, F, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩ :=
    leaves_satisfiable (D := (Examples₂.one.dat Examples₂.K3 v0).D) ((Examples₂.one.dat Examples₂.K3 v0).XW ())
      ((Examples₂.one.dat Examples₂.K3 v0).M ()) (hfr.2.1 ()) (hfr.2.2 ()).fg exampleSingleLift_ne_bot n χ hχ hper
  refine ⟨P, fun _ => F,
    { F0 := fun _ _ => 0, J0 := fun _ _ _ => 0, E1u := 0, l3m := fun _ => F.main, l3u := P.B0 * P.llx,
      l6m := fun _ => 0, l6u := 0, x := P.x, b := P.b, la := 0, de := 0 },
    h1, h2, h3, h4, h5, h6, fun _ => ⟨h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩,
    rfl, rfl, ?_, fun _ => rfl, rfl, ?_, fun _ => ⟨?_, h21⟩⟩
  · show ((Fintype.card Unit : ℕ) : ℝ) = P.m
    rw [h20]; simp
  · intro a b _
    exact Subsingleton.elim (α := Unit) a b
  · show ((F.q' : ℕ) : ℝ) + 1 ≤ P.m
    rw [h18, h20]; simp
end Formalism.L2.Indef.Tree
