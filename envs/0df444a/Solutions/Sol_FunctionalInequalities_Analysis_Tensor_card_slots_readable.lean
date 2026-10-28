-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.card_slots_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:28:54.630318+00:00
-- url     : https://prove2.me/submissions/79ed9c26-5b4e-4103-9c4f-dbdd3518b967

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coordinate

noncomputable section
open Finset
/-- The number of positions `a ≤ p < b` among `k` positions, for `b ≤ k`. -/
theorem solution {k a b : ℕ} (hb : b ≤ k) : (FunctionalInequalities.Analysis.Tensor.slots k a b).card = b - a := by
    have hmap : (FunctionalInequalities.Analysis.Tensor.slots k a b).map Fin.valEmbedding = Ico a b := by
      ext x
      constructor
      · intro hx
        rcases mem_map.mp hx with ⟨p, hp, rfl⟩
        apply mem_Ico.mpr
        simpa [FunctionalInequalities.Analysis.Tensor.slots] using hp
      · intro hx
        have hx' : a ≤ x ∧ x < b := mem_Ico.mp hx
        let p : Fin k := ⟨x, lt_of_lt_of_le hx'.2 hb⟩
        apply mem_map.mpr
        refine ⟨p, ?_, ?_⟩
        · simpa [FunctionalInequalities.Analysis.Tensor.slots, p] using hx'
        · simp [p]
    calc
      (FunctionalInequalities.Analysis.Tensor.slots k a b).card = ((FunctionalInequalities.Analysis.Tensor.slots k a b).map Fin.valEmbedding).card := by simp
      _ = (Ico a b).card := by rw [hmap]
      _ = b - a := by simp
