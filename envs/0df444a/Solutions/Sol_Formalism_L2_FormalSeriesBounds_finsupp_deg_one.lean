-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.finsupp_deg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:32:30.639377+00:00
-- url     : https://prove2.me/submissions/05465a7e-fd8a-44de-8a15-b9727ec3e0f5

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValNonnegLeadingCoeffOfMemTySet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {σ : Type} (e : σ →₀ ℕ) (h : e.degree = 1) : ∃ i, e = Finsupp.single i 1 := by
  classical
  have hdeg : ∑ j ∈ e.support, e j = 1 := h
  have hne : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.sum_empty] at hdeg
    exact absurd hdeg (by norm_num)
  obtain ⟨i, hi⟩ := hne
  have hle : ∀ j ∈ e.support, e j ≤ 1 := fun j hj =>
    hdeg ▸ Finset.single_le_sum (f := fun k => e k) (fun _ _ => Nat.zero_le _) hj
  have hei : e i = 1 := by
    have h1 := hle i hi
    have h2 := Finsupp.mem_support_iff.mp hi
    omega
  refine ⟨i, ?_⟩
  ext j
  by_cases hj : j = i
  · subst hj
    simp [hei]
  · rw [Finsupp.single_apply, if_neg (Ne.symm hj)]
    by_contra hc
    have hjs : j ∈ e.support := Finsupp.mem_support_iff.mpr hc
    have h2 : e i + e j ≤ ∑ k ∈ e.support, e k := by
      rw [← Finset.sum_pair (f := fun k => e k) (Ne.symm hj)]
      apply Finset.sum_le_sum_of_subset
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact hjs
    omega
end Formalism.L2.FormalSeriesBounds
