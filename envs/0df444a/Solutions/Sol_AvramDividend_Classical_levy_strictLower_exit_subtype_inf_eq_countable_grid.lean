-- Prove2me | solution 1 for AvramDividend.Classical.levy_strictLower_exit_subtype_inf_eq_countable_grid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:48:53.338876+00:00
-- url     : https://prove2.me/submissions/448800e6-9ec9-4a94-80e6-7677a2235f2f

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_lower_before_horizon_countable_grid_iff
import Theorems.Thm_AvramDividend_Classical_firstPassage_iInf_eq_of_strict_horizon_witness_iff

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (lower : ℝ) :
    (⨅ i : {t : ℝ≥0 // X.X t ω < lower}, (i.1 : ℝ≥0∞)) =
      (⨅ j : {p : ℕ × ℕ //
        0 < p.1 ∧
          X.X ((p.2 : ℝ≥0) * (p.1 : ℝ≥0)⁻¹) ω < lower},
        (((j.1.2 : ℝ≥0) * (j.1.1 : ℝ≥0)⁻¹) : ℝ≥0∞)) := by
  apply AvramDividend.Classical.firstPassage_iInf_eq_of_strict_horizon_witness_iff
  intro T
  induction T using ENNReal.recTopCoe with
  | top =>
    constructor
    · rintro ⟨⟨t, ht⟩, -⟩
      obtain ⟨n, hn, k, -, hX⟩ :=
        (AvramDividend.Classical.chat03_lower_before_horizon_countable_grid_iff X ω lower (t + 1)).1
          ⟨t, lt_add_one t, ht⟩
      exact ⟨⟨(n, k), hn, hX⟩, ENNReal.coe_lt_top⟩
    · rintro ⟨⟨p, hp, hX⟩, -⟩
      exact ⟨⟨_, hX⟩, ENNReal.coe_lt_top⟩
  | coe T =>
    have h := AvramDividend.Classical.chat03_lower_before_horizon_countable_grid_iff X ω lower T
    constructor
    · rintro ⟨⟨t, ht⟩, htT⟩
      obtain ⟨n, hn, k, hk, hX⟩ := h.1 ⟨t, ENNReal.coe_lt_coe.1 htT, ht⟩
      exact ⟨⟨(n, k), hn, hX⟩, ENNReal.coe_lt_coe.2 hk⟩
    · rintro ⟨⟨p, hp, hX⟩, hpT⟩
      exact ⟨⟨_, hX⟩, hpT⟩
