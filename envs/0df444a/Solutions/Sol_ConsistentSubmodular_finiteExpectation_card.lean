-- Prove2me | solution 1 for ConsistentSubmodular.finiteExpectation_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:35.288892+00:00
-- url     : https://prove2.me/submissions/71f9ec25-ba15-4556-b1d8-7d8e40c0b6e8

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation
import Theorems.Thm_ConsistentSubmodular_sum_weight_disjoint

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteExpectation_sum {β : Type*} [Fintype β] (p : ι → ℝ)
    (v : β → Finset ι → ℝ) :
    finiteExpectation p (fun S => ∑ a, v a S) = ∑ a, finiteExpectation p (v a) := by
  simp only [finiteExpectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem finiteExpectation_hit (p : ι → ℝ) (L : Finset ι) :
    finiteExpectation p (fun S => if (L ∩ S).Nonempty then 1 else 0) =
      1 - ∏ i ∈ L, (1 - p i) := by
  have hterm (S : Finset ι) : bernoulliWeight p S * (if (L ∩ S).Nonempty then 1 else 0) =
      bernoulliWeight p S - (if Disjoint S L then bernoulliWeight p S else 0) := by
    have hiff : (L ∩ S).Nonempty ↔ ¬Disjoint S L := by
      rw [Finset.inter_comm, Finset.not_disjoint_iff_nonempty_inter]
    by_cases hd : Disjoint S L <;> simp [hiff, hd]
  unfold finiteExpectation
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, sum_bernoulliWeight, sum_weight_disjoint]

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular

theorem solution {n : ℕ} (p : Fin n → ℝ) :
    finiteExpectation p (fun S => (S.card : ℝ)) = ∑ e, p e := by
  have hcard : (fun S : Finset (Fin n) => (S.card : ℝ)) =
      (fun S => ∑ e : Fin n, if e ∈ S then (1 : ℝ) else 0) := by
    funext S
    simp
  rw [hcard, finiteExpectation_sum]
  apply Finset.sum_congr rfl
  intro e _
  have hmem (S : Finset (Fin n)) : ({e} ∩ S).Nonempty ↔ e ∈ S := by
    constructor
    · rintro ⟨x, hx⟩
      have hxe := Finset.mem_singleton.mp (Finset.mem_inter.mp hx).1
      simpa [hxe] using (Finset.mem_inter.mp hx).2
    · intro he
      exact ⟨e, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self e, he⟩⟩
  simpa only [hmem, Finset.prod_singleton, sub_sub_cancel] using finiteExpectation_hit p {e}

end
