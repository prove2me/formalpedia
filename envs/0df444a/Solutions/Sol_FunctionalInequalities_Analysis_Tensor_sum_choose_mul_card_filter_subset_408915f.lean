-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.sum_choose_mul_card_filter_subset_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:59:39.011844+00:00
-- url     : https://prove2.me/submissions/81c5cfbe-90f2-4f03-9400-c740feefc461

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.Basic
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
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
section SubsetSum
variable {α : Type*} [DecidableEq α]
private theorem FunctionalInequalities.Analysis.Tensor.sum_choose_mul_choose (d r : ℕ) :
    ∑ s ∈ range (d + 1), d.choose s * r.choose s = (d + r).choose d := by
  have hv := Nat.add_choose_eq d r d
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
  have hv' :
      (d + r).choose d =
        ∑ s ∈ range (d + 1), d.choose s * r.choose (d - s) := by
    simpa using hv
  let f : ℕ → ℕ := fun s => d.choose s * r.choose s
  have hr :
      (∑ s ∈ range (d + 1), f s) =
        ∑ s ∈ range (d + 1), f (d - s) := by
    have h := Finset.sum_range_reflect (f := f) (n := d + 1)
    simpa using h.symm
  calc
    ∑ s ∈ range (d + 1), d.choose s * r.choose s =
        ∑ s ∈ range (d + 1), d.choose (d - s) * r.choose (d - s) := by
          simpa [f] using hr
    _ = ∑ s ∈ range (d + 1), d.choose s * r.choose (d - s) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hs' : s ≤ d := by
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hs)
      rw [Nat.choose_symm hs']
    _ = (d + r).choose d := hv'.symm
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Analysis.Tensor in
/-- Counting subsets with Vandermonde's identity: for `d`-subsets `F, F'` of `U`,
`∑_{s ≤ d} C(d, s) · #{S ⊆ U : |S| = s, S ⊆ F ∩ F'} = C(d + |F ∩ F'|, d)`. -/
theorem solution (U : Finset α) {d : ℕ} {F F' : Finset α}
    (hF : F ∈ U.powersetCard d) (hF' : F' ∈ U.powersetCard d) :
    ∑ s ∈ range (d + 1), d.choose s * ((U.powersetCard s).filter fun S => S ⊆ F ∩ F').card =
      (d + (F ∩ F').card).choose d := by
    have hFU : F ⊆ U := (Finset.mem_powersetCard.mp hF).1
    have hF'U : F' ⊆ U := (Finset.mem_powersetCard.mp hF').1
    have hInterU : F ∩ F' ⊆ U := inter_subset_left.trans hFU
    have hcard (s : ℕ) :
        ((U.powersetCard s).filter (fun S => S ⊆ F ∩ F')).card =
          (F ∩ F').card.choose s := by
      have heq :
          (U.powersetCard s).filter (fun S => S ⊆ F ∩ F') =
            (F ∩ F').powersetCard s := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨_, hS⟩, hsubset⟩
          exact ⟨hsubset, hS⟩
        · rintro ⟨hsubset, hS⟩
          exact ⟨⟨hsubset.trans hInterU, hS⟩, hsubset⟩
      rw [heq, Finset.card_powersetCard]
    simp_rw [hcard]
    exact sum_choose_mul_choose d (F ∩ F').card
