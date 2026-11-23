-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.mfact_add_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:22.953162+00:00
-- url     : https://prove2.me/submissions/0717d033-8a95-48e0-9376-634b8e4d869d

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {K : Type u} [Field K] {ι : Type}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (κ : ι →₀ ℕ) (i : ι) :
    mfact (κ + Finsupp.single i 1) = mfact κ * (κ i + 1) := by
  classical
  unfold mfact
  have key : ∀ (μ : ι →₀ ℕ) (s : Finset ι), μ.support ⊆ s →
      (μ.prod fun _ k => k.factorial) = ∏ j ∈ s, (μ j).factorial :=
    fun μ s h => Finsupp.prod_of_support_subset μ h (fun _ k => k.factorial)
      (fun _ _ => Nat.factorial_zero)
  have h1 : κ.support ⊆ insert i (κ.support.erase i) :=
    Finset.subset_insert_iff.mpr (Finset.Subset.refl _)
  have hsub : (κ + Finsupp.single i 1).support ⊆ insert i (κ.support.erase i) := by
    intro j hj
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply] at hj
    by_cases h : i = j
    · rw [← h]; exact Finset.mem_insert_self _ _
    · rw [if_neg h, add_zero] at hj
      exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Ne.symm h, Finsupp.mem_support_iff.mpr hj⟩)
  have hnot : i ∉ κ.support.erase i := by simp
  rw [key κ _ h1, key _ _ hsub, Finset.prod_insert hnot, Finset.prod_insert hnot]
  have hrest : ∏ j ∈ κ.support.erase i, ((κ + Finsupp.single i 1 : ι →₀ ℕ) j).factorial =
      ∏ j ∈ κ.support.erase i, (κ j).factorial := by
    refine Finset.prod_congr rfl (fun j hj => ?_)
    rw [Finsupp.add_apply, Finsupp.single_apply,
      if_neg (fun h => (Finset.ne_of_mem_erase hj) h.symm), add_zero]
  rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  ring
end Formalism.DworkPowerSeriesWeights
