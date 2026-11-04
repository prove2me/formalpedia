-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_large_shrinking_cells_pinpoint_true_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:40:03.227851+00:00
-- url     : https://prove2.me/submissions/fc94f5e2-043b-48a6-9123-d9815a1f0355

import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_shrinking_cell_endpoints_common_subseq
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_cell_endpoint_sided_subsequence_trichotomy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_shrinking_large_cells_limit_is_actual_jump
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

/-- A persistent large shrinking mesh increment identifies a true original
jump and a cofinal subsequence of cells containing that jump. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (a b w : ℕ → ℝ≥0)
    (haT : ∀ n, a n ≤ T)
    (hab : ∀ n, a n ≤ b n)
    (hbw : ∀ n, b n ≤ a n + w n)
    (hw : Tendsto w atTop (𝓝 (0 : ℝ≥0)))
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hlarge : ∀ n, ρ ≤ |Y (b n) - Y (a n)|) :
    ∃ t : ℝ≥0, t ∈ Icc (0 : ℝ≥0) T ∧
      ρ ≤ |Y t - Function.leftLim Y t| ∧
      ∃ φ : ℕ → ℕ, Tendsto φ atTop (atTop : Filter ℕ) ∧
        (∀ n, a (φ n) < t ∧ t ≤ b (φ n)) := by
  obtain ⟨t, ht, φ, hφ, haφ, hbφ⟩ :=
    avram_p2_a_zero_rate_shrinking_cell_endpoints_common_subseq
      T a b w haT hab hbw hw
  have hjump :
      ρ ≤ |Y t - Function.leftLim Y t| :=
    avram_p2_a_zero_rate_shrinking_large_cells_limit_is_actual_jump
      Y t (fun n => a (φ n)) (fun n => b (φ n))
      (fun n => hab (φ n)) haφ hbφ (hL t) (hR t)
      ρ hρ (fun n => hlarge (φ n))
  obtain ⟨g, hs⟩ :=
    avram_p2_a_zero_rate_cell_endpoint_sided_subsequence_trichotomy
      (fun n => a (φ n)) (fun n => b (φ n)) t
  let j : ℕ → ℕ := fun n => φ (g n)
  have hg : Tendsto (fun n : ℕ => (g n : ℕ))
      atTop (atTop : Filter ℕ) := g.strictMono.tendsto_atTop
  have ha' : Tendsto (fun n => a (j n)) atTop (𝓝 t) := by
    simpa [j, Function.comp_def] using haφ.comp hg
  have hb' : Tendsto (fun n => b (j n)) atTop (𝓝 t) := by
    simpa [j, Function.comp_def] using hbφ.comp hg
  have hbig : ∀ n, ρ ≤ |Y (b (j n)) - Y (a (j n))| :=
    fun n => hlarge (j n)
  rcases hs with hl | hr | hx
  · have hla : Tendsto (fun n => a (j n)) atTop (𝓝[<] t) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨ha', Filter.Eventually.of_forall (fun n =>
          lt_of_le_of_lt (hab (j n)) (hl n))⟩
    have hlb : Tendsto (fun n => b (j n)) atTop (𝓝[<] t) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hb', Filter.Eventually.of_forall hl⟩
    have hz : Tendsto (fun n => Y (b (j n)) - Y (a (j n)))
        atTop (𝓝 (0 : ℝ)) := by
      simpa [Function.comp_def] using
        ((hL t).comp hlb).sub ((hL t).comp hla)
    have hcontra : ρ ≤ (0 : ℝ) := by
      simpa using (ge_of_tendsto hz.abs
        (Filter.Eventually.of_forall hbig))
    exact False.elim ((not_le_of_gt hρ) hcontra)
  · have hra : Tendsto (fun n => a (j n))
        atTop (nhdsWithin t (Ici t)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨ha', Filter.Eventually.of_forall hr⟩
    have hrb : Tendsto (fun n => b (j n))
        atTop (nhdsWithin t (Ici t)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hb', Filter.Eventually.of_forall (fun n =>
          le_trans (hr n) (hab (j n)))⟩
    have hz : Tendsto (fun n => Y (b (j n)) - Y (a (j n)))
        atTop (𝓝 (0 : ℝ)) := by
      simpa [Function.comp_def] using
        (((hR t).tendsto.comp hrb).sub ((hR t).tendsto.comp hra))
    have hcontra : ρ ≤ (0 : ℝ) := by
      simpa using (ge_of_tendsto hz.abs
        (Filter.Eventually.of_forall hbig))
    exact False.elim ((not_le_of_gt hρ) hcontra)
  · refine ⟨t, ht, hjump, j, hφ.tendsto_atTop.comp hg, ?_⟩
    intro n
    exact hx n
