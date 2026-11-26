-- Prove2me | solution 1 for Eden.antitone_le_of_matched_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:03:07.525924+00:00
-- url     : https://prove2.me/submissions/9f0f895e-db59-405a-adde-fd3fd187ef70

import Definitions.Def_Eden_OrderedStationarySpectrum
import Mathlib.Data.Multiset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.MetricSpace.Lipschitz
import Definitions.Def_Eden_Sorting
import Theorems.Thm_Eden_card_filter_eq_of_multiset_eq

set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {n : ℕ} {a b f g : Fin n → ℝ} {δ : ℝ}
    (ha : Antitone a) (hb : Antitone b)
    (haf : Finset.univ.val.map a = Finset.univ.val.map f)
    (hbg : Finset.univ.val.map b = Finset.univ.val.map g)
    (hfg : ∀ j, f j ≤ g j + δ) (i : Fin n) : a i ≤ b i + δ := by
  classical
  by_contra h
  have hlt : b i + δ < a i := lt_of_not_ge h
  have hleft : i.val + 1 ≤ (Finset.univ.filter (fun j => a i ≤ a j)).card := by
    calc
      i.val + 1 = (Finset.Iic i).card := (Fin.card_Iic i).symm
      _ ≤ _ := Finset.card_le_card (by
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, ha (Finset.mem_Iic.mp hj)⟩)
  have hright : (Finset.univ.filter (fun j => b i < b j)).card ≤ i.val := by
    calc
      _ ≤ (Finset.Iio i).card := Finset.card_le_card (by
        intro j hj
        apply Finset.mem_Iio.mpr
        by_contra hji
        exact (not_lt_of_ge (hb (le_of_not_gt hji))) (Finset.mem_filter.mp hj).2)
      _ = i.val := Fin.card_Iio i
  have hmiddle : (Finset.univ.filter (fun j => a i ≤ f j)).card ≤
      (Finset.univ.filter (fun j => b i < g j)).card := by
    apply Finset.card_le_card
    intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ j, ?_⟩
    have hj' := (Finset.mem_filter.mp hj).2
    have := hfg j
    linarith
  rw [card_filter_eq_of_multiset_eq haf (fun x => a i ≤ x)] at hleft
  rw [card_filter_eq_of_multiset_eq hbg (fun x => b i < x)] at hright
  omega
end Eden
