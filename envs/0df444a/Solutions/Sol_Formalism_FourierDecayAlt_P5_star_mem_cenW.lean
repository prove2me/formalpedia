-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.star_mem_cenW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:09:46.100368+00:00
-- url     : https://prove2.me/submissions/8c2ad5d6-b21b-424b-98df-bb655701bee6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtFsvOther
import Theorems.Thm_Formalism_FourierDecayAlt_P5_star_mkP
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_add_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_add_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_alg_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_alg_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_mul_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_mul_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_one_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_one_snd
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P5_mkPair_fst__c1fc473b1221
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P5_mkPair_snd__1d131e24d74e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_add_fst
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_add_snd
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_alg_fst
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_alg_snd
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_mul_fst
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_mul_snd
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_one_fst
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_one_snd
attribute [local simp] P2M_Formalism_FourierDecayAlt_P5_mkPair_fst__c1fc473b1221
attribute [local simp] P2M_Formalism_FourierDecayAlt_P5_mkPair_snd__1d131e24d74e



set_option autoImplicit false
open scoped ComplexConjugate ContDiff
open Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution {Wv Wv' : Module.End ℂ V} {x : Pr V} (hx : x ∈ cenW Wv Wv') : star x ∈ cenW Wv Wv' := by
  rw [cenW, Subalgebra.mem_centralizer_iff] at hx ⊢
  intro g hg
  have hg' : star g ∈ ({mkP Wv Wv', mkP Wv' Wv} : Set (Pr V)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    rcases hg with rfl | rfl
    · right; exact star_mkP _ _
    · left; exact star_mkP _ _
  have e := congrArg star (hx _ hg')
  simp only [star_mul, star_star] at e
  exact e.symm
end Formalism.FourierDecayAlt.P5
