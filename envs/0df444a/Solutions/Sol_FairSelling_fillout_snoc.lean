-- Prove2me | solution 1 for FairSelling.fillout_snoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:11:30.59707+00:00
-- url     : https://prove2.me/submissions/7955f76e-e97a-409f-bfb8-adcfd177a8a5

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsBagFilling
import Definitions.Def_RequestProject_TwoThirdsProp6

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (ε : ℝ) {m : ℕ}
    {Res Res' : Finset G} {d r d' r' : ℝ} {f₀ f₀' : Option G}
    (F : FillOut w p ε m Res' d' r' f₀') (hRes' : Res' ⊆ Res)
    (hf₀' : ∀ f, f₀' = some f → f ∈ Res ∪ f₀.toFinset)
    (Enew : Finset G) (srcnew : Option G) (dnew snew : ℝ)
    (hEnew : Enew ⊆ Res)
    (hEdisj : Disjoint Enew (Res' ∪ f₀'.toFinset ∪ srcnew.toFinset))
    (hdnew : 0 ≤ dnew) (hsnew : 0 ≤ snew) (hd : d' + dnew ≤ d)
    (hacc : 2 * ε ≤ vbarSum w p Enew + dnew + snew)
    (hps : srcnew = none ∨ ∃ e, Enew = {e})
    (hsd : srcnew ≠ none → dnew = 0)
    (hsl : srcnew ≠ none → ∀ e ∈ Enew, ε ≤ vbar w p e)
    (hsz : srcnew = none → snew = 0)
    (hsnotin : ∀ f, srcnew = some f → f ∉ Res' ∧ ε ≤ p f ∧ f ∈ Res ∪ f₀.toFinset)
    (hmoney : ∀ f, (if srcnew = some f then snew else 0)
      + (if f ∈ F.sell then (if f₀' = some f then r' else p f) else 0)
      ≤ (if f₀ = some f then r else p f)) :
    Nonempty (FillOut w p ε (m + 1) Res d r f₀) := by
  classical
  -- the recursive parts never contain the new part's goods
  have hgoodsRes' : ∀ j, F.goods j ⊆ Res' := F.goods_subset
  have hEdisjRes' : Disjoint Enew Res' :=
    Finset.disjoint_of_subset_right (by intro x hx; simp [hx]) hEdisj
  refine ⟨{ goods := fun j => if j = m then Enew else F.goods j
            sell := F.sell ∪ srcnew.toFinset
            src := fun j => if j = m then srcnew else F.src j
            dcash := fun j => if j = m then dnew else F.dcash j
            scash := fun j => if j = m then snew else F.scash j
            goods_subset := ?_
            goods_disj := ?_
            goods_zero := ?_
            sell_subset := ?_
            sell_disj := ?_
            src_mem := ?_
            src_zero := ?_
            dcash_nonneg := ?_
            scash_nonneg := ?_
            dcash_zero := ?_
            dcash_sum := ?_
            scash_sum := ?_
            scash_zero := ?_
            price_large := ?_
            acceptable := ?_
            pure_or_singleton := ?_
            singleton_dcash := ?_
            singleton_large := ?_ }⟩
  · intro j
    by_cases h : j = m
    · simpa [h] using hEnew
    · simp only [if_neg h]; exact (F.goods_subset j).trans hRes'
  · intro j j' hjj
    by_cases h : j = m
    · have h' : j' ≠ m := fun hh => hjj (by rw [h, hh])
      simp only [if_pos h, if_neg h']
      exact Finset.disjoint_of_subset_right (F.goods_subset j') hEdisjRes'
    · by_cases h' : j' = m
      · simp only [if_neg h, if_pos h']
        exact (Finset.disjoint_of_subset_right (F.goods_subset j) hEdisjRes').symm
      · simp only [if_neg h, if_neg h']; exact F.goods_disj j j' hjj
  · intro j hj
    have h : j ≠ m := by omega
    simp only [if_neg h]
    exact F.goods_zero j (by omega)
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp (F.sell_subset hx) with hx' | hx'
      · exact Finset.mem_union_left _ (hRes' hx')
      · exact hf₀' x (Option.mem_toFinset.mp hx')
    · exact hsnotin x (Option.mem_toFinset.mp hx) |>.2.2
  · intro j
    by_cases h : j = m
    · simp only [if_pos h]
      refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp (F.sell_subset hx) with hy | hy
        · exact Finset.disjoint_left.mp hEdisj hx' (by simp [hy])
        · exact Finset.disjoint_left.mp hEdisj hx' (by simp [hy])
      · exact Finset.disjoint_left.mp hEdisj hx' (by simp [hx])
    · simp only [if_neg h]
      refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.disjoint_left.mp (F.sell_disj j) hx hx'
      · exact (hsnotin x (Option.mem_toFinset.mp hx)).1 (F.goods_subset j hx')
  · intro j f hf
    by_cases h : j = m
    · rw [if_pos h] at hf
      exact Finset.mem_union_right _ (by simp [hf])
    · rw [if_neg h] at hf
      exact Finset.mem_union_left _ (F.src_mem j f hf)
  · intro j hj
    have h : j ≠ m := by omega
    simp only [if_neg h]
    exact F.src_zero j (by omega)
  · intro j; by_cases h : j = m
    · simpa [h] using hdnew
    · simp only [if_neg h]; exact F.dcash_nonneg j
  · intro j; by_cases h : j = m
    · simpa [h] using hsnew
    · simp only [if_neg h]; exact F.scash_nonneg j
  · intro j hj
    have h : j ≠ m := by omega
    simp only [if_neg h]
    exact F.dcash_zero j (by omega)
  · rw [Finset.sum_range_succ]
    have : ∑ j ∈ Finset.range m, (if j = m then dnew else F.dcash j)
        = ∑ j ∈ Finset.range m, F.dcash j := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [if_neg (by simp at hj; omega)]
    rw [this, if_pos rfl]
    linarith [F.dcash_sum]
  · intro f
    have hsplit : ∑ j ∈ (Finset.range (m + 1)).filter
          (fun j => (if j = m then srcnew else F.src j) = some f),
          (if j = m then snew else F.scash j)
        = (if srcnew = some f then snew else 0)
          + ∑ j ∈ (Finset.range m).filter (fun j => F.src j = some f), F.scash j := by
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hnew : srcnew = some f
      · rw [if_pos (by simpa using hnew)]
        rw [Finset.sum_insert (by simp)]
        rw [if_pos rfl, if_pos hnew]
        congr 1
        rw [Finset.filter_congr (fun j hj => by
          simp only [Finset.mem_range] at hj
          rw [if_neg (by omega)])]
        exact Finset.sum_congr rfl (fun j hj => by
          simp only [Finset.mem_filter, Finset.mem_range] at hj
          rw [if_neg (by omega)])
      · rw [if_neg (by simpa using hnew), if_neg hnew, zero_add]
        rw [Finset.filter_congr (fun j hj => by
          simp only [Finset.mem_range] at hj
          rw [if_neg (by omega)])]
        exact Finset.sum_congr rfl (fun j hj => by
          simp only [Finset.mem_filter, Finset.mem_range] at hj
          rw [if_neg (by omega)])
    rw [hsplit]
    have hrec : ∑ j ∈ (Finset.range m).filter (fun j => F.src j = some f), F.scash j
        ≤ (if f ∈ F.sell then (if f₀' = some f then r' else p f) else 0) := by
      by_cases hf : f ∈ F.sell
      · rw [if_pos hf]; exact F.scash_sum f
      · rw [if_neg hf]
        have : (Finset.range m).filter (fun j => F.src j = some f) = ∅ := by
          refine Finset.filter_eq_empty_iff.mpr (fun j _ hj => hf (F.src_mem j f hj))
        rw [this, Finset.sum_empty]
    calc (if srcnew = some f then snew else 0)
          + ∑ j ∈ (Finset.range m).filter (fun j => F.src j = some f), F.scash j
        ≤ (if srcnew = some f then snew else 0)
          + (if f ∈ F.sell then (if f₀' = some f then r' else p f) else 0) := by linarith
      _ ≤ _ := hmoney f
  · intro j hj
    by_cases h : j = m
    · rw [if_pos h] at hj ⊢; exact hsz hj
    · rw [if_neg h] at hj ⊢; exact F.scash_zero j hj
  · intro f hf
    rcases Finset.mem_union.mp hf with hf | hf
    · exact F.price_large f hf
    · exact (hsnotin f (Option.mem_toFinset.mp hf)).2.1
  · intro j hj
    by_cases h : j = m
    · simp only [if_pos h]; exact hacc
    · simp only [if_neg h]; exact F.acceptable j (by omega)
  · intro j hj0 hj
    by_cases h : j = m
    · simp only [if_pos h]; exact hps
    · simp only [if_neg h]; exact F.pure_or_singleton j hj0 (by omega)
  · intro j hj0 hj
    by_cases h : j = m
    · rw [if_pos h] at hj ⊢; exact hsd hj
    · rw [if_neg h] at hj ⊢; exact F.singleton_dcash j hj0 hj
  · intro j hj0 hj e he
    by_cases h : j = m
    · rw [if_pos h] at hj he; exact hsl hj e he
    · rw [if_neg h] at hj he; exact F.singleton_large j hj0 hj e he
end FairSelling
