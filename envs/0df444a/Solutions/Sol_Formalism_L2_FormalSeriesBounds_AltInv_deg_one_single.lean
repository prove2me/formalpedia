-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.deg_one_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:23:57.076039+00:00
-- url     : https://prove2.me/submissions/86f42f21-1b90-41f8-8594-7793ac5b97c0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv

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
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.AltInv
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
variable {σ τ : Type*}
namespace Formalism.L2.FormalSeriesBounds.AltInv
theorem _root_.solution (d : σ →₀ ℕ) (h : d.degree = 1) : ∃ y, d = Finsupp.single y 1 := by
  have hdeg : ∑ i ∈ d.support, d i = 1 := h
  have h1 : ∀ x ∈ d.support, d x = 1 := by
    intro x hx
    have hle := Finset.single_le_sum (f := fun i => d i) (fun i _ => Nat.zero_le _) hx
    have h0 : d x ≠ 0 := Finsupp.mem_support_iff.1 hx
    omega
  have hcard : d.support.card = 1 := by
    rw [← hdeg, Finset.sum_congr rfl h1]
    simp
  obtain ⟨y, hy⟩ := Finset.card_eq_one.1 hcard
  refine ⟨y, Finsupp.ext fun x => ?_⟩
  by_cases hx : x = y
  · subst hx
    rw [Finsupp.single_eq_same]
    exact h1 x (by rw [hy]; exact Finset.mem_singleton_self x)
  · have hxs : x ∉ d.support := by
      rw [hy]
      simpa using hx
    have hdx : d x = 0 := by
      by_contra h'
      exact hxs (Finsupp.mem_support_iff.2 h')
    rw [hdx, Finsupp.single_apply, if_neg (Ne.symm hx)]
end Formalism.L2.FormalSeriesBounds.AltInv
