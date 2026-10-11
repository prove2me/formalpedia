-- Prove2me | solution 1 for BookProof.ChapterEll2Separable.ratVec_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:03:34.394891+00:00
-- url     : https://prove2.me/submissions/cccbe63a-c3b9-4555-80c0-44360ba480c8

-- Generated from ChapterEll2Separable.lean — solution of BookProof.ChapterEll2Separable.ratVec_dense
import Mathlib
import Definitions.Def_ChapterEll2Separable
import Theorems.Thm_BookProof_ChapterEll2Separable_sum_single_rat_mem_range
import Theorems.Thm_BookProof_ChapterEll2Separable_eq_sum_single_of_mem_finSupport
import Theorems.Thm_BookProof_ChapterRieszFischer_finSupport_dense
import Definitions.Def_ChapterRieszFischer
open BookProof.ChapterEll2Separable



open Filter Finset
open scoped ENNReal


open BookProof.ChapterRieszFischer

set_option maxHeartbeats 1000000 in
theorem solution : Dense (Set.range ratVec) := by

  classical
  rw [dense_iff_closure_eq, ← Set.univ_subset_iff]
  intro f _
  rw [mem_closure_iff_nhds_basis Metric.nhds_basis_ball]
  intro eps heps
  -- first approximate `f` by a finitely-supported vector
  obtain ⟨g, hg, hgf⟩ := Metric.mem_closure_iff.1 (finSupport_dense f) (eps / 2) (by linarith)
  set s : Finset ℕ := hg.toFinset
  have hssub : Function.support ((g : ℕ → ℝ)) ⊆ (s : Set ℕ) := by
    intro i hi
    exact Finset.mem_coe.2 ((Set.Finite.mem_toFinset hg).2 hi)
  have hgsum : g = ∑ i ∈ s, lp.single 2 i ((g : ℕ → ℝ) i) :=
    eq_sum_single_of_mem_finSupport g hssub
  -- then approximate each of the finitely many coordinates by a rational
  have hcnn : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have hden : (0 : ℝ) < 2 * ((s.card : ℝ) + 1) := by linarith
  have hpos : (0 : ℝ) < eps / (2 * (s.card + 1)) := div_pos heps hden
  have hq : ∀ i : ℕ, ∃ q : ℚ, |(g : ℕ → ℝ) i - (q : ℝ)| < eps / (2 * (s.card + 1)) := by
    intro i
    obtain ⟨q, hq⟩ := exists_rat_near ((g : ℕ → ℝ) i) hpos
    exact ⟨q, hq⟩
  choose q hqlt using hq
  refine ⟨∑ i ∈ s, lp.single 2 i ((q i : ℝ)), sum_single_rat_mem_range s q, ?_⟩
  -- combine the two estimates
  have hbound : ‖g - ∑ i ∈ s, lp.single 2 i ((q i : ℝ))‖ ≤
      ∑ i ∈ s, ‖lp.single (E := fun _ : ℕ => ℝ) 2 i ((g : ℕ → ℝ) i - (q i : ℝ))‖ := by
    have hdiff : g - ∑ i ∈ s, lp.single 2 i ((q i : ℝ))
        = ∑ i ∈ s, lp.single 2 i ((g : ℕ → ℝ) i - (q i : ℝ)) := by
      have hsplit : ∑ i ∈ s, lp.single 2 i ((g : ℕ → ℝ) i - (q i : ℝ))
          = (∑ i ∈ s, lp.single 2 i ((g : ℕ → ℝ) i))
            - ∑ i ∈ s, lp.single 2 i ((q i : ℝ)) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => lp.single_sub 2 i _ _
      rw [hsplit, ← hgsum]
    rw [hdiff]
    exact norm_sum_le _ _
  have hterm : ∀ i ∈ s,
      ‖lp.single (E := fun _ : ℕ => ℝ) 2 i ((g : ℕ → ℝ) i - (q i : ℝ))‖
        ≤ eps / (2 * (s.card + 1)) := by
    intro i _
    rw [lp.norm_single (by norm_num)]
    exact le_of_lt (by simpa [Real.norm_eq_abs] using hqlt i)
  have hsum_le : ∑ i ∈ s, ‖lp.single (E := fun _ : ℕ => ℝ) 2 i
      ((g : ℕ → ℝ) i - (q i : ℝ))‖ ≤ s.card * (eps / (2 * (s.card + 1))) := by
    simpa using Finset.sum_le_card_nsmul s _ _ hterm
  have hcard : (s.card : ℝ) * (eps / (2 * (s.card + 1))) < eps / 2 := by
    rw [← mul_div_assoc, div_lt_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
    nlinarith
  have : ‖g - ∑ i ∈ s, lp.single 2 i ((q i : ℝ))‖ < eps / 2 :=
    lt_of_le_of_lt (hbound.trans hsum_le) hcard
  have hdist : dist f (∑ i ∈ s, lp.single 2 i ((q i : ℝ))) < eps := by
    have h1 : dist f g < eps / 2 := hgf
    have h2 : dist g (∑ i ∈ s, lp.single 2 i ((q i : ℝ))) < eps / 2 := by
      rwa [dist_eq_norm]
    calc dist f (∑ i ∈ s, lp.single 2 i ((q i : ℝ)))
        ≤ dist f g + dist g (∑ i ∈ s, lp.single 2 i ((q i : ℝ))) := dist_triangle _ _ _
      _ < eps / 2 + eps / 2 := by linarith
      _ = eps := by ring
  simpa [Metric.mem_ball, dist_comm] using hdist
