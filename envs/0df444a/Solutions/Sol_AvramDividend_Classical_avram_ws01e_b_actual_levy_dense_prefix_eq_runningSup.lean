-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_actual_levy_dense_prefix_eq_runningSup
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:55:25.734265+00:00
-- url     : https://prove2.me/submissions/f900ac66-44ed-4b56-be5a-06d98b11bd50

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace S218AV

lemma approx (f : ℝ≥0 → ℝ) (hr : ∀ u, ContinuousWithinAt f (Set.Ici u) u)
    (samples : ℕ → ℝ≥0) (hdense : Dense (Set.range samples))
    (t : ℝ≥0) (ht : t ∈ Set.range samples) (s : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε) :
    ∃ i, samples i ≤ t ∧ f s < f (samples i) + ε := by
  rcases eq_or_lt_of_le hst with h | h
  · obtain ⟨j, hj⟩ := ht
    exact ⟨j, le_of_eq hj, by rw [hj, h]; linarith⟩
  · obtain ⟨δ, hδ, hδf⟩ := Metric.continuousWithinAt_iff.1 (hr s) ε hε
    set m : ℝ≥0 := min t (s + δ.toNNReal) with hm
    have hsm : s < m := lt_min h (by
      have : (0:ℝ≥0) < δ.toNNReal := Real.toNNReal_pos.2 hδ
      simpa using this)
    obtain ⟨u, ⟨i, rfl⟩, hu⟩ :=
      hdense.exists_mem_open isOpen_Ioo ⟨_, (exists_between hsm).choose_spec⟩
    have hut : samples i ≤ t := le_trans hu.2.le (min_le_left _ _)
    have hud : dist (samples i) s < δ := by
      rw [NNReal.dist_eq, abs_of_nonneg (by
        have := hu.1.le; rw [sub_nonneg]; exact_mod_cast this)]
      have h2 : samples i < s + δ.toNNReal := lt_of_lt_of_le hu.2 (min_le_right _ _)
      have h3 : ((samples i : ℝ≥0) : ℝ) < (s : ℝ) + δ := by
        have := (NNReal.coe_lt_coe.2 h2)
        rw [NNReal.coe_add, Real.coe_toNNReal _ hδ.le] at this
        exact this
      linarith
    have := hδf (Set.mem_Ici.2 hu.1.le) hud
    rw [Real.dist_eq, abs_lt] at this
    exact ⟨i, hut, by linarith⟩

lemma main (f : ℝ≥0 → ℝ) (hr : ∀ u, ContinuousWithinAt f (Set.Ici u) u)
    (hfzero : f 0 = 0) (samples : ℕ → ℝ≥0) (hdense : Dense (Set.range samples))
    (t : ℝ≥0) (ht : t ∈ Set.range samples) :
    (⨆ i : ℕ, if samples i ≤ t then
      ENNReal.ofReal (f (samples i)) else 0).toReal =
      ⨆ s : Set.Icc (0 : ℝ≥0) t, max (f s.1) 0 := by
  set F := ⨆ i : ℕ, if samples i ≤ t then ENNReal.ofReal (f (samples i)) else 0 with hF
  have hle : ∀ i, samples i ≤ t → ENNReal.ofReal (f (samples i)) ≤ F := by
    intro i hi
    have := le_iSup (fun i : ℕ => if samples i ≤ t then
      ENNReal.ofReal (f (samples i)) else 0) i
    simpa [hi] using this
  by_cases hb : BddAbove (Set.range (fun s : Set.Icc (0 : ℝ≥0) t => max (f s.1) 0))
  · set R := ⨆ s : Set.Icc (0 : ℝ≥0) t, max (f s.1) 0 with hR
    have hfle : ∀ s : Set.Icc (0 : ℝ≥0) t, max (f s.1) 0 ≤ R := fun s => le_ciSup hb s
    have hR0 : 0 ≤ R := le_trans (le_max_right _ _) (hfle ⟨0, le_rfl, zero_le⟩)
    have hFle : F ≤ ENNReal.ofReal R := by
      apply iSup_le
      intro i
      split_ifs with h
      · exact ENNReal.ofReal_le_ofReal (le_trans (le_max_left _ _) (hfle ⟨samples i, zero_le, h⟩))
      · exact zero_le
    have hFtop : F ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hFle
    have hsamp : ∀ i, samples i ≤ t → f (samples i) ≤ F.toReal := by
      intro i hi
      calc f (samples i) ≤ (ENNReal.ofReal (f (samples i))).toReal := by
            rw [ENNReal.toReal_ofReal']; exact le_max_left _ _
        _ ≤ F.toReal := ENNReal.toReal_mono hFtop (hle i hi)
    have hpt : ∀ s : Set.Icc (0 : ℝ≥0) t, max (f s.1) 0 ≤ F.toReal := by
      rintro ⟨s, hs0, hst⟩
      refine max_le ?_ ENNReal.toReal_nonneg
      apply le_of_forall_pos_lt_add
      intro ε hε
      obtain ⟨i, hi, hfi⟩ := approx f hr samples hdense t ht s hst ε hε
      linarith [hsamp i hi]
    apply le_antisymm
    · calc F.toReal ≤ (ENNReal.ofReal R).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hFle
        _ = R := ENNReal.toReal_ofReal hR0
    · have : Nonempty (Set.Icc (0 : ℝ≥0) t) := ⟨⟨0, le_rfl, zero_le⟩⟩
      exact ciSup_le hpt
  · rw [Real.iSup_of_not_bddAbove hb]
    have htop : F = ⊤ := by
      refine ENNReal.eq_top_of_forall_nnreal_le fun M => ?_
      obtain ⟨_, ⟨⟨s, hs0, hst⟩, rfl⟩, hs⟩ := not_bddAbove_iff.1 hb ((M : ℝ) + 1)
      simp only at hs
      have hfs : (M : ℝ) + 1 < f s := by
        rcases le_or_gt (f s) 0 with h0 | h0
        · rw [max_eq_right h0] at hs; linarith [M.2]
        · rwa [max_eq_left h0.le] at hs
      obtain ⟨i, hi, hfi⟩ := approx f hr samples hdense t ht s hst 1 one_pos
      calc (M : ℝ≥0∞) = ENNReal.ofReal (M : ℝ) := by simp
        _ ≤ ENNReal.ofReal (f (samples i)) := ENNReal.ofReal_le_ofReal (by linarith)
        _ ≤ F := hle i hi
    rw [htop, ENNReal.toReal_top]

end S218AV

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (samples : ℕ → ℝ≥0) (hdense : Dense (Set.range samples))
    (hzero : (0 : ℝ≥0) ∈ Set.range samples)
    (t : ℝ≥0) (ht : t ∈ Set.range samples) :
    (⨆ i : ℕ, if samples i ≤ t then
      ENNReal.ofReal (X.X (samples i) ω) else 0).toReal =
    runningSup X t ω :=
  S218AV.main (fun s => X.X s ω) (fun u => X.rightCont ω u) (X.X_zero ω) samples hdense t ht
