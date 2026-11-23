-- Prove2me | solution 1 for Formalism.FG.InvIntVAux.eq_single_of_degree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:21.089458+00:00
-- url     : https://prove2.me/submissions/fc73b2c9-5034-4d6d-8ef0-5513a64623a9

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.InvIntVAux
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K]
namespace Formalism.FG.InvIntVAux
theorem _root_.solution {ι : Type*} [Fintype ι] (e : ι →₀ ℕ)
    (he : e.degree = 1) : ∃ i, e = Finsupp.single i 1 := by
  classical
  have hd : e.degree = ∑ j ∈ e.support, e j := by
    first
      | rfl
      | simp [Finsupp.degree]
  rw [hd] at he
  have hcard : e.support.card ≤ 1 := by
    have h1 : ∑ j ∈ e.support, (1 : ℕ) ≤ ∑ j ∈ e.support, e j :=
      Finset.sum_le_sum fun j hj => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
    rw [he, Finset.sum_const, smul_eq_mul, mul_one] at h1
    exact h1
  have hpos : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    rw [h0, Finset.sum_empty] at he
    omega
  have hc1 : e.support.card = 1 := by
    have := Finset.card_pos.mpr hpos
    omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc1
  refine ⟨i, ?_⟩
  rw [hi, Finset.sum_singleton] at he
  ext j
  by_cases hj : j = i
  · rw [hj, he, Finsupp.single_eq_same]
  · have hz : e j = 0 := by
      by_contra hne
      have hmem : j ∈ e.support := Finsupp.mem_support_iff.mpr hne
      rw [hi, Finset.mem_singleton] at hmem
      exact hj hmem
    rw [hz]
    simp [Finsupp.single_apply, Ne.symm hj]
end Formalism.FG.InvIntVAux
