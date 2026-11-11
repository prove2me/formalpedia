-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_count_mark_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T19:58:30.098225+00:00
-- url     : https://prove2.me/submissions/f17295ea-65fb-4887-9642-6a320d2e7120

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
import Theorems.Thm_levy_foundations_iIndepFun_setRestrict_pairwiseDisjoint
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_jumpCount_measurable_public
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- The original interarrival count is independent of the complete mark stream. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) (u : ℝ≥0) :
    IndepFun (fun ω => LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) (u : ℝ))
      (fun ω (i : ℕ) => Y i ω) P := by
  let blk : Bool → Set (ℕ ⊕ ℕ) := fun b =>
    if b then Set.range Sum.inl else Set.range Sum.inr
  have hall : ∀ i : ℕ ⊕ ℕ, Measurable (Sum.elim τ Y i) := by
    intro i
    cases i with
    | inl n => exact hd.measurable_interarrival n
    | inr n => exact hd.measurable_mark n
  have hS : Pairwise (Function.onFun Disjoint blk) := by
    intro i j hij
    cases i <;> cases j
    · exact absurd rfl hij
    · refine Set.disjoint_left.2 ?_
      rintro x ⟨a, rfl⟩ ⟨c, hc⟩
      cases hc
    · refine Set.disjoint_left.2 ?_
      rintro x ⟨a, rfl⟩ ⟨c, hc⟩
      cases hc
    · exact absurd rfl hij
  have hgroup := levy_foundations_iIndepFun_setRestrict_pairwiseDisjoint
    hall hd.indep hS
  have hTT := hgroup.indepFun (by decide : true ≠ false)
  have hGτm : Measurable (fun (x : ↥(blk true) → ℝ) (i : ℕ) =>
      x ⟨Sum.inl i, (show Sum.inl i ∈ blk true from ⟨i, rfl⟩)⟩) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hGYm : Measurable (fun (x : ↥(blk false) → ℝ) (i : ℕ) =>
      x ⟨Sum.inr i, (show Sum.inr i ∈ blk false from ⟨i, rfl⟩)⟩) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hTY : IndepFun (fun ω (i : ℕ) => τ i ω)
      (fun ω (i : ℕ) => Y i ω) P :=
    hTT.comp hGτm hGYm
  have hj : Measurable (fun x : ℕ → ℝ =>
      LevyFoundations.jumpCount
        (fun n => LevyFoundations.arrival (fun i y => y i) n x) (u : ℝ)) :=
    AvramDividend.Classical.avram_a06_compound_jumpCount_measurable_public
      (fun i (x : ℕ → ℝ) => x i)
      (fun i => measurable_pi_apply i) (u : ℝ)
  exact hTY.comp hj measurable_id
