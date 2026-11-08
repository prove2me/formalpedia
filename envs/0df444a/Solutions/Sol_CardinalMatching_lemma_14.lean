-- Prove2me | solution 1 for CardinalMatching.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:49:06.617092+00:00
-- url     : https://prove2.me/submissions/f98d3925-40c9-4ab2-bf16-bf072a8dfd31

import Mathlib
import Definitions.Def_CardinalMatching_ModParams
import Definitions.Def_CardinalMatching_ModParams_IsStep2Context

open CardinalMatching in
theorem solution {n : ℕ} (P : CardinalMatching.ModParams n) (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ)
    (p : P.Good → ℝ) (q : P.Agent → ℝ) (hC : P.IsStep2Context x α p q) (j j' : P.Good)
    (h : P.SameGoodType j j') : p j = p j' := by
  classical
  obtain ⟨_, _, _, _, _, _, ⟨hfeas, hopt⟩, _, _⟩ := hC
  have key : ∀ a b : P.Good, P.SameGoodType a b → p a ≤ p b := by
    intro a b hab
    by_contra hlt
    push_neg at hlt
    have hf' : ∀ i g, α i * P.util i g ≤ q i + Function.update p a (p b) g := by
      intro i g
      by_cases hg : g = a
      · rw [hg, Function.update_self, hab i]
        exact hfeas i b
      · rw [Function.update_of_ne hg]
        exact hfeas i g
    have h1 := hopt _ q hf'
    rw [Finset.sum_update_of_mem (Finset.mem_univ a)] at h1
    have h3 := Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ a) p
    linarith
  exact le_antisymm (key j j' h) (key j' j (fun ag => (h ag).symm))
