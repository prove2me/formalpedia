-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.depth_nonneg_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:23:04.430886+00:00
-- url     : https://prove2.me/submissions/374c07e3-6af8-469a-bdc8-c6cc4abb7c92

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_weight_rowWeights_eq_rowDeg
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylDominanceZ
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution : DepthNonneg := by
  intro r c ν μ hν hne
  obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.2 hf0
  have hdom := dualWeylDominanceZ r r ν le_rfl hν f h1 m hm
  have hw : Finsupp.weight (rowW r r) m = μ :=
    ((mem_weightedHomogeneousSubmodule _ _ _ _).1 h2) (MvPolynomial.mem_support_iff.1 hm)
  have hrd : ∀ a : Fin r, rowDeg m a = μ a := fun a => by rw [← hw, weight_rowWeights_eq_rowDeg]
  have hrn : ∀ a : Fin r, rowNu (r := r) ν a = ν a := fun a => by simp [rowNu]
  simp only [hrd, hrn] at hdom
  refine ⟨hdom.2, ?_⟩
  have h3 := hdom.1 c
  unfold depth2 res varpi
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, Finset.sum_sub_distrib]
  have h4 : ((∑ a : Fin r with a.val < c, μ a : ℕ) : ℤ) ≤ ((∑ a : Fin r with a.val < c, ν a : ℕ) : ℤ) := by
    exact_mod_cast h3
  push_cast at h4
  linarith
end Formalism.CohomologicalDescent.DepthNonnegative
