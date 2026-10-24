-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.sum_norm_sq_le_sum_norm_sq_sum_subset_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:01:56.15115+00:00
-- url     : https://prove2.me/submissions/3e151040-e711-473a-a821-c597dbe39190

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_norm_sq_sum_subset_eq_408915f

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
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Analysis.Tensor in
/-- **BKL (25), inequality.** Under the same assumptions,
`∑_{|F| = d} ‖x_F‖² ≤ ∑_{|E| = 2d} ‖∑_{F ⊆ E} x_F‖²`. -/
theorem solution (U : Finset α) {d : ℕ} (hU : U.card = 3 * d)
    (x : Finset α → V) :
    ∑ F ∈ U.powersetCard d, ‖x F‖ ^ 2 ≤
      ∑ E ∈ U.powersetCard (2 * d), ‖∑ F ∈ E.powersetCard d, x F‖ ^ 2 := by
    have hfilter (S : Finset α) (hS : S ∈ U.powersetCard d) :
        (U.powersetCard d).filter (S ⊆ ·) = {S} := by
      ext F
      constructor
      · intro hF
        have hFU : F ∈ U.powersetCard d := (mem_filter.mp hF).1
        have hSF : S ⊆ F := (mem_filter.mp hF).2
        have hScard : S.card = d := (Finset.mem_powersetCard.mp hS).2
        have hFcard : F.card = d := (Finset.mem_powersetCard.mp hFU).2
        have hEq : S = F :=
          Finset.eq_of_subset_of_card_le hSF (by omega)
        simp [hEq]
      · intro hF
        have hEq : F = S := by simpa using hF
        subst F
        exact mem_filter.mpr ⟨hS, subset_rfl⟩
    have hinner :
        (∑ S ∈ U.powersetCard d,
            ‖∑ F ∈ (U.powersetCard d).filter (S ⊆ ·), x F‖ ^ 2) =
          ∑ S ∈ U.powersetCard d, ‖x S‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro S hS
      rw [hfilter S hS]
      simp
    have hbase :
        (∑ F ∈ U.powersetCard d, ‖x F‖ ^ 2) =
          (d.choose d : ℝ) *
            ∑ S ∈ U.powersetCard d,
              ‖∑ F ∈ (U.powersetCard d).filter (S ⊆ ·), x F‖ ^ 2 := by
      simp [hinner]
    have hnonneg :
        ∀ s ∈ range (d + 1),
          0 ≤ (d.choose s : ℝ) *
            ∑ S ∈ U.powersetCard s,
              ‖∑ F ∈ (U.powersetCard d).filter (S ⊆ ·), x F‖ ^ 2 := by
      intro s hs
      apply mul_nonneg
      · exact_mod_cast Nat.zero_le (d.choose s)
      · apply Finset.sum_nonneg
        intro S hS
        exact sq_nonneg _
    calc
      ∑ F ∈ U.powersetCard d, ‖x F‖ ^ 2 =
          (d.choose d : ℝ) *
            ∑ S ∈ U.powersetCard d,
              ‖∑ F ∈ (U.powersetCard d).filter (S ⊆ ·), x F‖ ^ 2 := hbase
      _ ≤ ∑ s ∈ range (d + 1), (d.choose s : ℝ) *
            ∑ S ∈ U.powersetCard s,
              ‖∑ F ∈ (U.powersetCard d).filter (S ⊆ ·), x F‖ ^ 2 :=
        Finset.single_le_sum (fun s hs => hnonneg s hs)
          (mem_range.mpr (Nat.lt_succ_self d))
      _ = ∑ E ∈ U.powersetCard (2 * d),
            ‖∑ F ∈ E.powersetCard d, x F‖ ^ 2 :=
        (FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_subset_eq_408915f U hU x).symm
