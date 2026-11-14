-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_uniform_jump_chord_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:24:46.982982+00:00
-- url     : https://prove2.me/submissions/b13fcbbb-b0fe-430f-9020-8016f07d121b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_chat24_source_cell_jump_chord_bound
import Theorems.Thm_AvramDividend_Classical_avram_chat24_marked_disjoint_cell_domination
import Theorems.Thm_avram_chat24_atomic_prefix_interval_core
import Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_mesh_cell_geometry
import Theorems.Thm_AvramDividend_Classical_avram_chat24_disjoint_cell_step_bound
import Theorems.Thm_avram_chat24_right_path_measurable_core
import Theorems.Thm_avram_chat24_left_limit_measurable_core
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (f K Y : ℝ≥0 → ℝ) (v d a b q T : ℝ) (hT : 0 ≤ T)
    (B : ℝ≥0) (hB : 0 < B) (hBT : B ≤ (⟨T, hT⟩ : ℝ≥0))
    (hd : 0 < d) (ha : 0 < a) (hq : 0 ≤ q)
    (hf_right : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hf_left : ∀ t : ℝ≥0, 0 < t → ∃ l, Tendsto f (𝓝[<] t) (nhds l))
    (hf_down : ∀ t : ℝ≥0, 0 < t → f t ≤ Function.leftLim f t)
    (hK : Monotone K)
    (hsum : Summable (fun t : ℝ≥0 =>
      if 0 < t ∧ t ≤ B then Function.leftLim f t - f t else 0))
    (hsource : ∀ t : ℝ≥0, t ≤ B → f t = (t : ℝ) * d -
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then Function.leftLim f u - f u else 0)
    (hband : ∀ t : ℝ≥0, t ≤ B → v + f t - K t ∈ Icc a b)
    (hpre : ∀ t : ℝ≥0, 0 < t → t ≤ B →
      Y t ∈ Icc a b ∧ Tendsto (fun s => v + f s - K s) (𝓝[<] t) (nhds (Y t)))
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 1 w (Ioi 0))
    (n0 : ℕ) (L : ℝ≥0)
    (hLip : LipschitzOnWith L w (Icc (a / 2) (b + 1)))
    (hsmall : ∀ n : ℕ, n0 ≤ n →
      d * ((B : ℝ) / ((n + 1 : ℕ) : ℝ)) < min (a / 2) 1) :
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ f u - Function.leftLim f u ≠ 0}).map
        (fun u : ℝ≥0 => (u, f u - Function.leftLim f u)))
    let μ : Measure ℝ≥0 := (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let h : ℕ → ℝ := fun n => (B : ℝ) / ((n + 1 : ℕ) : ℝ)
    let V : ℕ → ℕ → ℝ := fun n i => v + f (u n i) - K (u n i)
    let m : ℕ → ℕ → ℝ := fun n i =>
      d * h n - (f (u n (i + 1)) - f (u n i))
    let J : ℝ≥0 × ℝ → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0 then
        Real.exp (-(q * (p.1 : ℝ))) * (w (Y p.1 + p.2) - w (Y p.1)) else 0
    let A : ℝ≥0 → ℝ := fun t =>
      if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y t ∈ Icc a b then
        Real.exp (-(q * (t : ℝ))) * (d * deriv w (Y t)) else 0
    let F : ℕ → ℝ≥0 × ℝ → ℝ := fun n p => if n0 ≤ n then
      ∑ i ∈ Finset.range (n + 1),
        if u n i < p.1 ∧ p.1 ≤ u n (i + 1) then
          Real.exp (-(q * (u n (i + 1) : ℝ))) *
            ((w (V n i - m n i) - w (V n i)) / m n i) * (-p.2) else 0
      else 0
    let G : ℕ → ℝ≥0 → ℝ := fun n t => if n0 ≤ n then
      ∑ i ∈ Finset.range (n + 1),
        if u n i < t ∧ t ≤ u n (i + 1) then
          Real.exp (-(q * (u n (i + 1) : ℝ))) *
            ((w (V n i + d * h n - m n i) - w (V n i - m n i)) / h n) else 0
      else 0
    let Jdom : ℝ≥0 × ℝ → ℝ := fun p =>
      if 0 < p.1 ∧ p.1 ≤ B ∧ p.2 < 0 then (L : ℝ) * (-p.2) else 0
    (∀ n, AEStronglyMeasurable (F n) NX) ∧
      (∀ n, ∀ᵐ p ∂NX, ‖F n p‖ ≤ Jdom p) := by
  classical
  intro NX μ u h V m J A F G Jdom
  have geom := AvramDividend.Classical.avram_chat24_uniform_mesh_cell_geometry B hB
  let c : ℕ → ℕ → ℝ := fun n i => Real.exp (-(q * (u n (i + 1) : ℝ))) *
    ((w (V n i - m n i) - w (V n i)) / m n i)
  have hc (n : ℕ) (hn : n0 ≤ n) (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      ‖c n i‖ ≤ (L : ℝ) := by
    have hg := geom.2.2 n i hi
    exact AvramDividend.Classical.avram_chat24_source_cell_jump_chord_bound
      f K v d a b q B ha hq hf_down hK hsum hsource (u n i) (u n (i + 1))
      ((geom.1 n).monotone (by omega)) hg.2.1
      (hband (u n i) hg.1) (hband (u n (i + 1)) hg.2.1)
      (h n) (m n i) hg.2.2 rfl (hsmall n hn) w L hLip
  let Δ : ℝ≥0 → ℝ := fun t => f t - Function.leftLim f t
  have hΔ : Measurable Δ :=
    (avram_chat24_right_path_measurable_core f hf_right).sub
      (avram_chat24_left_limit_measurable_core f hf_left)
  have hS : MeasurableSet {t : ℝ≥0 | 0 < t ∧ Δ t ≠ 0} := by measurability
  have hsupport : ∀ᵐ p ∂NX, 0 < p.1 ∧ p.2 < 0 := by
    apply (ae_map_iff (measurable_id.prodMk hΔ).aemeasurable (by measurability)).2
    filter_upwards [ae_restrict_mem hS] with t ht
    refine ⟨ht.1, ?_⟩
    have hdlt : Δ t ≤ 0 := sub_nonpos.mpr (hf_down t ht.1)
    exact (lt_or_eq_of_le hdlt).resolve_right ht.2
  exact AvramDividend.Classical.avram_chat24_marked_disjoint_cell_domination
    NX B u geom.1 (fun n i hi => (geom.2.2 n i hi).2.1)
    c (L : ℝ) L.property n0 hc hsupport
