-- Prove2me | solution 1 for AvramDividend.Classical.esscher_weighted_positive_tail_real_kernel_package
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T19:20:00.900456+00:00
-- url     : https://prove2.me/submissions/fbf2e3ee-09f5-4504-9178-59eab48ce6b8

import Theorems.Thm_AvramDividend_Classical_continuousOn_esscher_weighted_positive_tail_of_ac
import Mathlib.Data.ENNReal.Real

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution
    (μ : Measure ℝ) (hac : μ ≪ volume) (φ : ℝ)
    (hfin : ∀ x : ℝ, 0 < x →
      (μ.withDensity
        (fun z : ℝ => ENNReal.ofReal (Real.exp (-(φ * z))))) (Ici x) ≠ ⊤) :
    ∃ κ : ℝ → ℝ,
      (∀ x : ℝ, κ x =
        if 0 < x then
          (μ.withDensity
            (fun z : ℝ => ENNReal.ofReal (Real.exp (-(φ * z))))).real (Ioi x)
        else 0) ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, x ≤ 0 → κ x = 0) ∧
      (∀ x : ℝ, 0 ≤ κ x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M) := by
  set ν := μ.withDensity (fun z : ℝ => ENNReal.ofReal (Real.exp (-(φ * z)))) with hν
  set κ : ℝ → ℝ := fun x => if 0 < x then ν.real (Ioi x) else 0 with hκ
  have hpos : ∀ x, 0 < x → κ x = ν.real (Ioi x) := fun x hx => by simp [hκ, hx]
  have hnn : ∀ x, 0 ≤ κ x := by
    intro x; simp only [hκ]; split_ifs
    · exact measureReal_nonneg
    · exact le_rfl
  have hanti : AntitoneOn κ (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    rw [hpos x hx, hpos y hy]
    have hfx : ν (Ioi x) ≠ ⊤ :=
      ne_top_of_le_ne_top (hfin x hx) (measure_mono Ioi_subset_Ici_self)
    exact measureReal_mono (Ioi_subset_Ioi hxy) hfx
  refine ⟨κ, fun x => rfl, ?_, hanti, fun x hx => by simp [hκ, not_lt.2 hx], hnn, ?_⟩
  · exact (continuousOn_esscher_weighted_positive_tail_of_ac μ hac φ hfin).congr
      fun x hx => hpos x hx
  · intro ε hε
    refine ⟨κ ε, fun x hx => ?_⟩
    rw [abs_of_nonneg (hnn x)]
    exact hanti hε (lt_of_lt_of_le hε hx) hx
