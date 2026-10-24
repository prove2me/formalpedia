-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_subset_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:00:58.981742+00:00
-- url     : https://prove2.me/submissions/06749386-b1fa-45f4-a0ae-d60045d9967a

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_card_filter_union_subset_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_choose_mul_card_filter_subset_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_norm_sq_sum_filter_408915f

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
/-- For `E ⊆ U`, the `d`-subsets of `E` are the `d`-subsets of `U` contained in `E`. -/
theorem FunctionalInequalities.Analysis.Tensor.powersetCard_eq_filter_subset {U E : Finset α} (hE : E ⊆ U) (d : ℕ) :
    E.powersetCard d = (U.powersetCard d).filter (· ⊆ E) := by
    ext F
    simp only [Finset.mem_powersetCard, Finset.mem_filter]
    constructor
    · rintro ⟨hFE, hcard⟩
      exact ⟨⟨Finset.Subset.trans hFE hE, hcard⟩, hFE⟩
    · rintro ⟨⟨hFU, hcard⟩, hFE⟩
      exact ⟨hFE, hcard⟩
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Analysis.Tensor in
/-- **BKL (25), equality.** For any family `x` of vectors indexed by the `d`-subsets of a set
`U` with `3d` elements,
`∑_{|E| = 2d} ‖∑_{F ⊆ E} x_F‖² = ∑_{s=0}^{d} C(d, s) ∑_{|S| = s} ‖∑_{S ⊆ F} x_F‖²`,
all subsets being subsets of `U` and `F` ranging over `d`-subsets. -/
theorem solution (U : Finset α) {d : ℕ} (hU : U.card = 3 * d)
    (x : Finset α → V) :
    ∑ E ∈ U.powersetCard (2 * d), ‖∑ F ∈ E.powersetCard d, x F‖ ^ 2 =
      ∑ s ∈ range (d + 1), (d.choose s : ℝ) *
        ∑ S ∈ U.powersetCard s, ‖∑ F ∈ (U.powersetCard d).filter (S ⊆ ·), x F‖ ^ 2 := by
    classical
    let P := U.powersetCard d
    let Q := U.powersetCard (2 * d)

    have hL :
        (∑ E ∈ Q, ‖∑ F ∈ E.powersetCard d, x F‖ ^ 2) =
          ∑ F ∈ P, ∑ F' ∈ P,
            ((d + (F ∩ F').card).choose d : ℝ) *
              inner ℝ (x F) (x F') := by
      calc
        (∑ E ∈ Q, ‖∑ F ∈ E.powersetCard d, x F‖ ^ 2) =
            ∑ E ∈ Q, ‖∑ F ∈ P.filter (fun F => F ⊆ E), x F‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro E hE
              rw [FunctionalInequalities.Analysis.Tensor.powersetCard_eq_filter_subset
                ((Finset.mem_powersetCard.mp hE).1) d]
        _ = ∑ F ∈ P, ∑ F' ∈ P,
            ((Q.filter fun E => F ⊆ E ∧ F' ⊆ E).card : ℝ) *
              inner ℝ (x F) (x F') := by
              exact FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_filter_408915f Q P (fun F E => F ⊆ E) x
        _ = ∑ F ∈ P, ∑ F' ∈ P,
            ((d + (F ∩ F').card).choose d : ℝ) *
              inner ℝ (x F) (x F') := by
              apply Finset.sum_congr rfl
              intro F hF
              apply Finset.sum_congr rfl
              intro F' hF'
              have hu :
                  Q.filter (fun E => F ⊆ E ∧ F' ⊆ E) =
                    Q.filter (fun E => F ∪ F' ⊆ E) := by
                ext E
                simp [Finset.union_subset_iff]
              rw [hu, FunctionalInequalities.Analysis.Tensor.card_filter_union_subset_408915f U hU hF hF']

    have hS (s : ℕ) :
        (∑ S ∈ U.powersetCard s,
            ‖∑ F ∈ P.filter (fun F => S ⊆ F), x F‖ ^ 2) =
          ∑ F ∈ P, ∑ F' ∈ P,
            (((U.powersetCard s).filter
                (fun S => S ⊆ F ∩ F')).card : ℝ) *
              inner ℝ (x F) (x F') := by
      calc
        (∑ S ∈ U.powersetCard s,
            ‖∑ F ∈ P.filter (fun F => S ⊆ F), x F‖ ^ 2) =
            ∑ F ∈ P, ∑ F' ∈ P,
              (((U.powersetCard s).filter
                  (fun S => S ⊆ F ∧ S ⊆ F')).card : ℝ) *
                inner ℝ (x F) (x F') := by
              exact FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_filter_408915f
                (U.powersetCard s) P (fun F S => S ⊆ F) x
        _ = ∑ F ∈ P, ∑ F' ∈ P,
            (((U.powersetCard s).filter
                (fun S => S ⊆ F ∩ F')).card : ℝ) *
              inner ℝ (x F) (x F') := by
              apply Finset.sum_congr rfl
              intro F hF
              apply Finset.sum_congr rfl
              intro F' hF'
              have hi :
                  (U.powersetCard s).filter
                      (fun S => S ⊆ F ∧ S ⊆ F') =
                    (U.powersetCard s).filter
                      (fun S => S ⊆ F ∩ F') := by
                ext S
                simp [Finset.subset_inter_iff]
              rw [hi]

    have hcoef {F F' : Finset α} (hF : F ∈ P) (hF' : F' ∈ P) :
        ∑ s ∈ range (d + 1), (d.choose s : ℝ) *
            (((U.powersetCard s).filter
                (fun S => S ⊆ F ∩ F')).card : ℝ) =
          ((d + (F ∩ F').card).choose d : ℝ) := by
      exact_mod_cast FunctionalInequalities.Analysis.Tensor.sum_choose_mul_card_filter_subset_408915f U hF hF'

    have hR :
        (∑ s ∈ range (d + 1), (d.choose s : ℝ) *
          ∑ S ∈ U.powersetCard s,
            ‖∑ F ∈ P.filter (fun F => S ⊆ F), x F‖ ^ 2) =
          ∑ F ∈ P, ∑ F' ∈ P,
            ((d + (F ∩ F').card).choose d : ℝ) *
              inner ℝ (x F) (x F') := by
      calc
        (∑ s ∈ range (d + 1), (d.choose s : ℝ) *
          ∑ S ∈ U.powersetCard s,
            ‖∑ F ∈ P.filter (fun F => S ⊆ F), x F‖ ^ 2) =
            ∑ s ∈ range (d + 1), (d.choose s : ℝ) *
              (∑ F ∈ P, ∑ F' ∈ P,
                (((U.powersetCard s).filter
                    (fun S => S ⊆ F ∩ F')).card : ℝ) *
                  inner ℝ (x F) (x F')) := by
              apply Finset.sum_congr rfl
              intro s hs
              rw [hS s]
        _ = ∑ F ∈ P, ∑ F' ∈ P,
            (∑ s ∈ range (d + 1), (d.choose s : ℝ) *
              (((U.powersetCard s).filter
                  (fun S => S ⊆ F ∩ F')).card : ℝ)) *
                inner ℝ (x F) (x F') := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro F hF
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro F' hF'
              simp_rw [← mul_assoc]
              rw [← Finset.sum_mul]
        _ = ∑ F ∈ P, ∑ F' ∈ P,
            ((d + (F ∩ F').card).choose d : ℝ) *
              inner ℝ (x F) (x F') := by
              apply Finset.sum_congr rfl
              intro F hF
              apply Finset.sum_congr rfl
              intro F' hF'
              rw [hcoef hF hF']

    exact hL.trans hR.symm
