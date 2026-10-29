-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_actual_real_clock_firstRecord_H_drawdown_reset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T22:01:07.185269+00:00
-- url     : https://prove2.me/submissions/6820628c-7b63-4e15-8d49-6df2a1552fef

import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_firstRecord_drawdown_normalised_at_clock
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (hb : 0 ≤ b) (β : ℝ)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hShift : ∀ (ω : Ω) (u t : ℝ≥0),
      H t (fun s : ℝ≥0 => X.X (u + s) ω - X.X u ω) =
        ENNReal.ofReal (Real.exp (-β *
          (sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) ''
            Set.Icc 0 t) - (X.X (u + t) ω - X.X u ω)))))
    (z : Ω × ℝ) (hFinite : twoSidedExitUpTime X b z.1 < ⊤)
    (hObs : ((twoSidedExitUpTime X b z.1).toNNReal : ℝ) ≤ z.2) :
    H (Real.toNNReal (z.2 - ((twoSidedExitUpTime X b z.1).toNNReal : ℝ)))
      (fun s : ℝ≥0 =>
        X.X ((twoSidedExitUpTime X b z.1).toNNReal + s) z.1 -
          X.X (twoSidedExitUpTime X b z.1).toNNReal z.1) =
      ENNReal.ofReal (Real.exp (-β *
        (runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1))) := by
  let u : ℝ≥0 := (twoSidedExitUpTime X b z.1).toNNReal
  let e : ℝ≥0 := Real.toNNReal z.2
  have hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b z.1 := by
    dsimp [u]
    exact ENNReal.coe_toNNReal (ne_top_of_lt hFinite)
  have hPos : 0 ≤ z.2 := le_trans (NNReal.coe_nonneg _) hObs
  have he : (e : ℝ) = z.2 := Real.coe_toNNReal _ hPos
  have hObsNN : u ≤ e := by
    exact_mod_cast (show (u : ℝ) ≤ (e : ℝ) by
      rw [he]
      exact hObs)
  have hDelta : Real.toNNReal (z.2 - (u : ℝ)) = e - u := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hObsNN,
      Real.coe_toNNReal _ (sub_nonneg.mpr hObs), he]
  have hAdd : u + (e - u) = e := add_tsub_cancel_of_le hObsNN
  have hFutureBdd :
      BddAbove ((fun r : ℝ≥0 => X.X (u + r) z.1) '' Set.Icc 0 (e - u)) := by
    apply (levyPath_bddAbove_Icc X z.1 e).mono
    rintro y ⟨r, hr, rfl⟩
    refine ⟨u + r, ⟨by positivity, ?_⟩, rfl⟩
    calc
      u + r ≤ u + (e - u) := add_le_add_right hr.2 u
      _ = e := hAdd
  have hDReset := avram_ws01e_b_firstRecord_drawdown_normalised_at_clock
    X b hb z.1 u hu (levyPath_bddAbove_Icc X z.1 u)
    (fun _ : Unit => e) () hObsNN hFutureBdd
  change H (Real.toNNReal (z.2 - (u : ℝ)))
      (fun s : ℝ≥0 => X.X (u + s) z.1 - X.X u z.1) =
    ENNReal.ofReal (Real.exp (-β * (runningSup X e z.1 - X.X e z.1)))
  rw [hDelta, hShift]
  rw [hAdd]
  exact (congrArg (fun d : ℝ => ENNReal.ofReal (Real.exp (-β * d))) hDReset).symm
