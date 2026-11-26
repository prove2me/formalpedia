-- Prove2me | solution 1 for Eden.nonneg_of_card_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:58:19.741264+00:00
-- url     : https://prove2.me/submissions/c81ff6e4-3eee-4149-9d90-f671969e9d18

import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_NeutralDimensionBounds
import Theorems.Thm_Eden_card_filter_eq_of_multiset_eq


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {n : ℕ} {a f : Fin n → ℝ} (ha : Antitone a)
    (hm : Finset.univ.val.map a = Finset.univ.val.map f) (i : Fin n)
    (hi : i.val < (Finset.univ.filter (fun j => 0 ≤ f j)).card) : 0 ≤ a i := by
  classical
  by_contra h
  have hcard : (Finset.univ.filter (fun j => 0 ≤ a j)).card ≤ i.val := by
    calc
      _ ≤ (Finset.Iio i).card := Finset.card_le_card (by
        intro j hj
        apply Finset.mem_Iio.mpr
        by_contra hji
        have hle := ha (le_of_not_gt hji)
        exact h ((Finset.mem_filter.mp hj).2.trans hle))
      _ = i.val := Fin.card_Iio i
  rw [card_filter_eq_of_multiset_eq hm (fun x => 0 ≤ x)] at hcard
  omega
end Eden
