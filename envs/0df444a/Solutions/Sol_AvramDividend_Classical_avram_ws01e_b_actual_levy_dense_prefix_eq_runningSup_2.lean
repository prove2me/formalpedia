-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01e_b_actual_levy_dense_prefix_eq_runningSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T17:55:49.240734+00:00
-- url     : https://prove2.me/submissions/94c8faae-474c-4666-b739-a49ac5551694

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_dense_prefix_toReal_eq_genuine_sup
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (samples : ℕ → ℝ≥0) (hdense : Dense (Set.range samples))
    (hzero : (0 : ℝ≥0) ∈ Set.range samples)
    (t : ℝ≥0) (ht : t ∈ Set.range samples) :
    (⨆ i : ℕ, if samples i ≤ t then
      ENNReal.ofReal (X.X (samples i) ω) else 0).toReal =
    runningSup X t ω := by
  classical
  letI : Nonempty (Set.Icc (0 : ℝ≥0) t) :=
    ⟨⟨0, ⟨le_rfl, zero_le⟩⟩⟩
  have hbimage := levyPath_bddAbove_Icc X ω t
  have hb : BddAbove
      (Set.range (fun s : Set.Icc (0 : ℝ≥0) t => X.X s.1 ω)) := by
    have hb_saved := hbimage
    obtain ⟨M, hM⟩ := hb_saved
    refine ⟨M, ?_⟩
    rintro y ⟨s, rfl⟩
    exact hM ⟨s.1, s.2, rfl⟩
  have hprefix :
      (⨆ i : ℕ, if samples i ≤ t then
        ENNReal.ofReal (X.X (samples i) ω) else 0).toReal =
      ⨆ s : Set.Icc (0 : ℝ≥0) t, X.X s.1 ω :=
    avram_ws01e_b_dense_prefix_toReal_eq_genuine_sup
      (fun r => X.X r ω) (X.rightCont ω) (X.X_zero ω)
      samples hdense hzero t ht hb
  exact hprefix.trans (runningSup_eq_rawSup_nonneg X t ω).1.symm
