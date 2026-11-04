-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_shrinking_large_cells_limit_is_actual_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:24:13.909194+00:00
-- url     : https://prove2.me/submissions/c18ebbef-86fa-4147-a545-a355c62df14f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_cell_endpoint_sided_subsequence_trichotomy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

/-- A persistently large original càdlàg shrinking-cell increment forces an
actual jump at its common endpoint limit. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (t : ℝ≥0) (a b : ℕ → ℝ≥0)
    (hab : ∀ n, a n ≤ b n)
    (ha : Tendsto a atTop (𝓝 t))
    (hb : Tendsto b atTop (𝓝 t))
    (hL : Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hlarge : ∀ n, ρ ≤ |Y (b n) - Y (a n)|) :
    ρ ≤ |Y t - Function.leftLim Y t| := by
  obtain ⟨g, hs⟩ :=
    avram_p2_a_zero_rate_cell_endpoint_sided_subsequence_trichotomy a b t
  have hg : Tendsto (fun n : ℕ => (g n : ℕ)) atTop (atTop : Filter ℕ) :=
    g.strictMono.tendsto_atTop
  have hag : Tendsto (fun n => a (g n)) atTop (𝓝 t) := ha.comp hg
  have hbg : Tendsto (fun n => b (g n)) atTop (𝓝 t) := hb.comp hg
  have hbig : ∀ n, ρ ≤ |Y (b (g n)) - Y (a (g n))| :=
    fun n => hlarge (g n)
  rcases hs with hl | hr | hx
  · have hla : Tendsto (fun n => a (g n)) atTop (𝓝[<] t) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hag, Filter.Eventually.of_forall (fun n =>
          lt_of_le_of_lt (hab (g n)) (hl n))⟩
    have hlb : Tendsto (fun n => b (g n)) atTop (𝓝[<] t) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hbg, Filter.Eventually.of_forall hl⟩
    have hz : Tendsto (fun n => Y (b (g n)) - Y (a (g n)))
        atTop (𝓝 (0 : ℝ)) := by
      simpa [Function.comp_def] using (hL.comp hlb).sub (hL.comp hla)
    have hh : ρ ≤ (0 : ℝ) := by
      simpa using (ge_of_tendsto hz.abs
        (Filter.Eventually.of_forall hbig))
    exact False.elim ((not_le_of_gt hρ) hh)
  · have hra : Tendsto (fun n => a (g n))
        atTop (nhdsWithin t (Ici t)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hag, Filter.Eventually.of_forall hr⟩
    have hrb : Tendsto (fun n => b (g n))
        atTop (nhdsWithin t (Ici t)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hbg, Filter.Eventually.of_forall (fun n =>
          le_trans (hr n) (hab (g n)))⟩
    have hz : Tendsto (fun n => Y (b (g n)) - Y (a (g n)))
        atTop (𝓝 (0 : ℝ)) := by
      simpa [Function.comp_def] using
        (hR.tendsto.comp hrb).sub (hR.tendsto.comp hra)
    have hh : ρ ≤ (0 : ℝ) := by
      simpa using (ge_of_tendsto hz.abs
        (Filter.Eventually.of_forall hbig))
    exact False.elim ((not_le_of_gt hρ) hh)
  · have hla : Tendsto (fun n => a (g n)) atTop (𝓝[<] t) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hag, Filter.Eventually.of_forall (fun n => (hx n).1)⟩
    have hrb : Tendsto (fun n => b (g n))
        atTop (nhdsWithin t (Ici t)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hbg, Filter.Eventually.of_forall (fun n => (hx n).2)⟩
    have hj : Tendsto (fun n => Y (b (g n)) - Y (a (g n)))
        atTop (𝓝 (Y t - Function.leftLim Y t)) := by
      simpa [Function.comp_def] using
        (hR.tendsto.comp hrb).sub (hL.comp hla)
    exact ge_of_tendsto hj.abs (Filter.Eventually.of_forall hbig)
