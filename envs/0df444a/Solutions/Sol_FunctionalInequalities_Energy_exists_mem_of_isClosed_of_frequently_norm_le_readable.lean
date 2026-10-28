-- Prove2me | solution 1 for FunctionalInequalities.Energy.exists_mem_of_isClosed_of_frequently_norm_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:43:23.628494+00:00
-- url     : https://prove2.me/submissions/ccf2dce7-b05b-411d-ab6d-7e5c524011d5

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_LinearPMap

noncomputable section
open Filter Topology Set
section Selection
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
/-- Hilbert selection along a closed subspace of pairs: if `(x n, y n)` lie in a closed
subspace `G`, `x n → x₀`, and `‖y n‖ ≤ L` frequently, then `G` contains a pair `(x₀, y₀)`
with `‖y₀‖ ≤ L`. The pair is found by minimizing the norm over the closed convex hulls of the
tails of `y`; the minimizers form a Cauchy sequence by the parallelogram law. -/
theorem solution
    {G : Submodule ℝ (X × H)} (hG : IsClosed (G : Set (X × H)))
    {x : ℕ → X} {y : ℕ → H} (hxy : ∀ n, (x n, y n) ∈ G)
    {x₀ : X} (hx : Tendsto x atTop (𝓝 x₀)) {L : ℝ} (hL : ∃ᶠ n in atTop, ‖y n‖ ≤ L) :
    ∃ y₀ : H, (x₀, y₀) ∈ G ∧ ‖y₀‖ ≤ L := by
  -- tails of the graph sequence and their closed convex hulls in the second coordinate
  set P : ℕ → Set (X × H) := fun n ↦ (fun j ↦ (x j, y j)) '' Ici n with hP
  set C : ℕ → Set H := fun n ↦ closure (convexHull ℝ (Prod.snd '' P n)) with hC
  have hPG : ∀ n, P n ⊆ (G : Set (X × H)) := by
    rintro n _ ⟨j, -, rfl⟩
    exact hxy j
  have hP_anti : ∀ n, P (n + 1) ⊆ P n := fun n ↦
    image_mono (Ici_subset_Ici.mpr (Nat.le_succ n))
  have hC_anti : ∀ n, C (n + 1) ⊆ C n := fun n ↦
    closure_mono (convexHull_mono (image_mono (hP_anti n)))
  have hC_antitone : Antitone C := antitone_nat_of_succ_le hC_anti
  have hyC : ∀ n j, n ≤ j → y j ∈ C n := fun n j hj ↦
    subset_closure (subset_convexHull ℝ _ ⟨(x j, y j), ⟨j, hj, rfl⟩, rfl⟩)
  have hC_ne : ∀ n, (C n).Nonempty := fun n ↦ ⟨y n, hyC n n le_rfl⟩
  have hC_closed : ∀ n, IsClosed (C n) := fun n ↦ isClosed_closure
  have hC_convex : ∀ n, Convex ℝ (C n) := fun n ↦ (convex_convexHull ℝ _).closure
  -- minimal-norm elements of the tails
  have hmin : ∀ n, ∃ z ∈ C n, ∀ w ∈ C n, ‖z‖ ≤ ‖w‖ := by
    intro n
    obtain ⟨z, hz, hzmin⟩ := exists_norm_eq_iInf_of_complete_convex (hC_ne n)
      (hC_closed n).isComplete (hC_convex n) 0
    refine ⟨z, hz, fun w hw ↦ ?_⟩
    have h1 : ‖(0 : H) - z‖ = ⨅ w : C n, ‖(0 : H) - (w : H)‖ := hzmin
    simp only [zero_sub, norm_neg] at h1
    rw [h1]
    have hbdd : BddBelow (range fun w : C n ↦ ‖(w : H)‖) :=
      ⟨0, by rintro _ ⟨w', rfl⟩; exact norm_nonneg _⟩
    exact ciInf_le hbdd ⟨w, hw⟩
  choose z hzC hzmin using hmin
  have hz_mono : Monotone fun n ↦ ‖z n‖ :=
    monotone_nat_of_le_succ fun n ↦ hzmin n (z (n + 1)) (hC_anti n (hzC (n + 1)))
  have hz_le : ∀ n, ‖z n‖ ≤ L := by
    intro n
    obtain ⟨j, hj, hjL⟩ := frequently_atTop.mp hL n
    exact (hzmin n (y j) (hyC n j hj)).trans hjL
  set S : ℝ := ⨆ n, ‖z n‖ with hS
  have hz_bdd : BddAbove (range fun n ↦ ‖z n‖) := ⟨L, by rintro _ ⟨n, rfl⟩; exact hz_le n⟩
  have hz_tendsto : Tendsto (fun n ↦ ‖z n‖) atTop (𝓝 S) := tendsto_atTop_ciSup hz_mono hz_bdd
  have hz_le_S : ∀ n, ‖z n‖ ≤ S := fun n ↦ le_ciSup hz_bdd n
  -- the minimizers are Cauchy by the parallelogram law
  have hz_cauchy : CauchySeq z := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hsq : Tendsto (fun n ↦ ‖z n‖ ^ 2) atTop (𝓝 (S ^ 2)) := hz_tendsto.pow 2
    have hev : ∀ᶠ n in atTop, S ^ 2 - ‖z n‖ ^ 2 < ε ^ 2 / 2 := by
      have := (tendsto_const_nhds (x := S ^ 2)).sub hsq
      rw [sub_self] at this
      exact (this.eventually (gt_mem_nhds (by positivity)))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    refine ⟨N, fun n hn ↦ ?_⟩
    -- the midpoint lies in the tail `C N`, so its norm dominates `‖z N‖`
    have hmid : (1 / 2 : ℝ) • z N + (1 / 2 : ℝ) • z n ∈ C N :=
      (hC_convex N) (hzC N) (hC_antitone hn (hzC n)) (by norm_num) (by norm_num) (by norm_num)
    have hmid_norm : ‖z N‖ ≤ ‖z n + z N‖ / 2 := by
      have := hzmin N _ hmid
      rwa [← smul_add, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
        one_div, inv_mul_eq_div, add_comm] at this
    have hpar := parallelogram_law_with_norm ℝ (z n) (z N)
    have hbound : ‖z n - z N‖ ^ 2 ≤ 2 * (S ^ 2 - ‖z N‖ ^ 2) := by
      have h4 : 4 * ‖z N‖ ^ 2 ≤ ‖z n + z N‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hmid_norm (by norm_num : (0 : ℝ) ≤ 2)
        rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at this
        nlinarith [norm_nonneg (z N), norm_nonneg (z n + z N)]
      have hn_le : ‖z n‖ ^ 2 ≤ S ^ 2 := by
        have := hz_le_S n
        nlinarith [norm_nonneg (z n)]
      nlinarith
    have hlt : ‖z n - z N‖ ^ 2 < ε ^ 2 := by
      have := hN N le_rfl
      nlinarith
    rw [dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt
  obtain ⟨z₀, hz₀⟩ := cauchySeq_tendsto_of_complete hz_cauchy
  refine ⟨z₀, ?_, le_of_tendsto hz₀.norm (Eventually.of_forall hz_le)⟩
  -- approximate each minimizer by a convex combination of graph points
  have hsel : ∀ n, ∃ p ∈ convexHull ℝ (P n), dist (z n) p.2 < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨w, hw, hdist⟩ := Metric.mem_closure_iff.mp (hzC n) (1 / ((n : ℝ) + 1)) (by positivity)
    have hw' : w ∈ (LinearMap.snd ℝ X H) '' convexHull ℝ (P n) := by
      rw [LinearMap.image_convexHull]
      simpa using hw
    obtain ⟨p, hp, rfl⟩ := hw'
    exact ⟨p, hp, hdist⟩
  choose p hp hpdist using hsel
  have hpG : ∀ n, p n ∈ (G : Set (X × H)) := fun n ↦
    convexHull_min (hPG n) G.convex (hp n)
  have hp2 : Tendsto (fun n ↦ (p n).2) atTop (𝓝 z₀) := by
    refine hz₀.congr_dist ?_
    refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ (hpdist n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hp1 : Tendsto (fun n ↦ (p n).1) atTop (𝓝 x₀) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hx (ε / 2) (by positivity)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hball : Prod.fst '' P n ⊆ Metric.closedBall x₀ (ε / 2) := by
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      exact Metric.mem_closedBall.mpr (hN j (hn.trans hj)).le
    have hmem : (p n).1 ∈ (LinearMap.fst ℝ X H) '' convexHull ℝ (P n) := ⟨p n, hp n, rfl⟩
    rw [LinearMap.image_convexHull] at hmem
    have hsub : convexHull ℝ ((LinearMap.fst ℝ X H) '' P n) ⊆ Metric.closedBall x₀ (ε / 2) :=
      convexHull_min (by simpa using hball) (convex_closedBall x₀ (ε / 2))
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp (hsub hmem)) (half_lt_self hε)
  have hp_tendsto : Tendsto p atTop (𝓝 (x₀, z₀)) := by
    have := hp1.prodMk_nhds hp2
    simpa using this
  exact hG.mem_of_tendsto hp_tendsto (Eventually.of_forall hpG)
