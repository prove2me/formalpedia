-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.card_slots_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:59:10.719987+00:00
-- url     : https://prove2.me/submissions/8fd3ce7b-6381-4352-b5bf-e43340080742

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic

noncomputable section
open Finset
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Tensor
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Analysis.Tensor in
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
