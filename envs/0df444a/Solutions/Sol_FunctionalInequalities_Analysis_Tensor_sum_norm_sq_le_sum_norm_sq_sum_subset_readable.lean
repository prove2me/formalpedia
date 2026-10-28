-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.sum_norm_sq_le_sum_norm_sq_sum_subset_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:30:44.922016+00:00
-- url     : https://prove2.me/submissions/f4840a9f-ca1b-410c-9d2f-5613d325307b

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_norm_sq_sum_subset_eq_readable

noncomputable section
open Finset
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
section SubsetSum
variable {α : Type*} [DecidableEq α]
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
        (FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_subset_eq_readable U hU x).symm
