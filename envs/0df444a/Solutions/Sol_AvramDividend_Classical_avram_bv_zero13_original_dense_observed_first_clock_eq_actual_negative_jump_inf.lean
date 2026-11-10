-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_original_dense_observed_first_clock_eq_actual_negative_jump_inf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:59:08.505636+00:00
-- url     : https://prove2.me/submissions/35ef2df3-f151-4506-a01e-99855fb4b6dc

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_negative_band_count_real_positive_iff_exists_jump
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A dense deterministic clock detects exactly the first original negative jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℕ → ℝ≥0)
    (hr : ∀ u v : ℝ≥0, u < v → ∃ k : ℕ, u < r k ∧ r k < v)
    (ω : Ω) :
    let pastCount : ℕ → ℕ → Ω → ℝ :=
      fun n k ξ =>
        (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ξ -
            Function.leftLim (fun v : ℝ≥0 => X.X v ξ) u ≠ 0}).map
          (fun u : ℝ≥0 =>
            (u, X.X u ξ -
              Function.leftLim (fun v : ℝ≥0 => X.X v ξ) u)))
          (Ioc 0 (r k) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
    (⨅ n : ℕ, ⨅ k : ℕ,
        if 0 < pastCount n k ω then (r k : WithTop ℝ≥0) else ⊤) =
      ⨅ u : ℝ≥0,
        if 0 < u ∧
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
        then (u : WithTop ℝ≥0) else ⊤ := by
  classical
  let pc : ℕ → ℕ → Ω → ℝ := fun n k ξ =>
    (((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ξ -
        Function.leftLim (fun v : ℝ≥0 => X.X v ξ) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ξ -
          Function.leftLim (fun v : ℝ≥0 => X.X v ξ) u)))
      (Ioc 0 (r k) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
  let jump : ℝ≥0 → Prop := fun u =>
    0 < u ∧
      X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
  let observed : WithTop ℝ≥0 :=
    ⨅ n : ℕ, ⨅ k : ℕ,
      if 0 < pc n k ω then (r k : WithTop ℝ≥0) else ⊤
  let actual : WithTop ℝ≥0 :=
    ⨅ u : ℝ≥0, if jump u then (u : WithTop ℝ≥0) else ⊤
  change observed = actual
  apply le_antisymm
  · refine le_iInf ?_
    intro u
    by_cases hu : jump u
    · rw [if_pos hu]
      have hBound (v0 : ℝ≥0) (huv0 : u < v0) :
          observed < (v0 : WithTop ℝ≥0) := by
        obtain ⟨k, huk, hkv⟩ := hr u v0 huv0
        obtain ⟨n, hn⟩ :=
          exists_nat_one_div_lt
            (show 0 <
              -(X.X u ω -
                  Function.leftLim (fun z : ℝ≥0 => X.X z ω) u) from
                neg_pos.mpr hu.2)
        have hcut :
            X.X u ω -
                Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≤
              -(1 / ((n : ℝ) + 1)) := by
          linarith
        have hpc : 0 < pc n k ω := by
          change 0 < (((Measure.count.restrict {s : ℝ≥0 |
            0 < s ∧ X.X s ω -
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) s ≠ 0}).map
            (fun s : ℝ≥0 =>
              (s, X.X s ω -
                Function.leftLim (fun z : ℝ≥0 => X.X z ω) s)))
            (Ioc 0 (r k) ×ˢ
              Iic (-(1 / ((n : ℝ) + 1))))).toReal
          exact
            (avram_bv_zero13_original_negative_band_count_real_positive_iff_exists_jump
              X ω (r k) n).2 ⟨u, hu.1, huk.le, hcut⟩
        have hle : observed ≤ (r k : WithTop ℝ≥0) := by
          calc
            observed ≤ ⨅ k : ℕ,
                if 0 < pc n k ω then (r k : WithTop ℝ≥0) else ⊤ :=
              iInf_le _ n
            _ ≤ if 0 < pc n k ω then (r k : WithTop ℝ≥0) else ⊤ :=
              iInf_le _ k
            _ = (r k : WithTop ℝ≥0) := if_pos hpc
        exact lt_of_le_of_lt hle (WithTop.coe_lt_coe.mpr hkv)
      refine le_of_forall_gt ?_
      intro v huv
      cases v with
      | top =>
          have huplus : u < u + 1 := by
            exact lt_add_of_pos_right u (by norm_num)
          exact lt_trans (hBound (u + 1) huplus) (WithTop.coe_lt_top _)
      | coe v =>
          exact hBound v (WithTop.coe_lt_coe.mp huv)
    · rw [if_neg hu]
      exact le_top
  · refine le_iInf ?_
    intro n
    refine le_iInf ?_
    intro k
    by_cases hpc : 0 < pc n k ω
    · have hphysical :
          ∃ u : ℝ≥0, 0 < u ∧ u ≤ r k ∧
            X.X u ω -
                Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≤
              -(1 / ((n : ℝ) + 1)) := by
          exact
            (avram_bv_zero13_original_negative_band_count_real_positive_iff_exists_jump
              X ω (r k) n).1 hpc
      obtain ⟨u, hu0, huk, hcut⟩ := hphysical
      have hnegative : X.X u ω -
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u < 0 := by
        have hcutpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by
          positivity
        linarith
      have hju : jump u := ⟨hu0, hnegative⟩
      have hle : actual ≤ (u : WithTop ℝ≥0) := by
        calc
          actual ≤ if jump u then (u : WithTop ℝ≥0) else ⊤ :=
            iInf_le _ u
          _ = (u : WithTop ℝ≥0) := if_pos hju
      have hmain : actual ≤ (r k : WithTop ℝ≥0) :=
        hle.trans (WithTop.coe_le_coe.mpr huk)
      simpa only [if_pos hpc] using hmain
    · simp only [if_neg hpc]
      exact le_top
