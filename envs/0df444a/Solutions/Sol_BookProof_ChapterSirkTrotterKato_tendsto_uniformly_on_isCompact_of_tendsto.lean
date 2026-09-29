-- Prove2me | solution 1 for BookProof.ChapterSirkTrotterKato.tendsto_uniformly_on_isCompact_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:33:43.744983+00:00
-- url     : https://prove2.me/submissions/23946dbc-c701-4e84-98d7-8a1696a78cba

import Mathlib
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
noncomputable section
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem solution {D : ℕ → H →L[ℂ] H} {M : ℝ}
    (hM : ∀ n y, ‖D n y‖ ≤ M * ‖y‖) (hptw : ∀ y, Tendsto (fun n => D n y) atTop (𝓝 0))
    {K : Set H} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ y ∈ K, ‖D n y‖ ≤ ε := by
  set M' : ℝ := max M 1 with hM'
  have hM'pos : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hM'le : ∀ n y, ‖D n y‖ ≤ M' * ‖y‖ := by
    intro n y
    exact (hM n y).trans (by nlinarith [norm_nonneg y, le_max_left M 1])
  set δ : ℝ := ε / (2 * M') with hδ
  have hδpos : 0 < δ := by positivity
  have hMδ : M' * δ = ε / 2 := by rw [hδ]; field_simp
  have hcover : K ⊆ ⋃ z ∈ K, Metric.ball z δ := fun y hy =>
    Set.mem_biUnion hy (Metric.mem_ball_self hδpos)
  obtain ⟨t, hts, htfin, htcover⟩ := hK.elim_finite_subcover_image
    (fun z (_ : z ∈ K) => Metric.isOpen_ball (x := z) (ε := δ)) hcover
  have hfin : ∀ᶠ n in atTop, ∀ z ∈ t, ‖D n z‖ ≤ ε / 2 := by
    rw [eventually_all_finite htfin]
    intro z _
    have h := (hptw z).norm
    simp only [norm_zero] at h
    exact h.eventually_le_const (by positivity)
  filter_upwards [hfin] with n hn y hy
  obtain ⟨z, hz, hyz⟩ := by simpa using htcover hy
  have h1 : ‖D n (y - z)‖ ≤ M' * δ := by
    refine (hM'le n _).trans ?_
    have hle : ‖y - z‖ ≤ δ := le_of_lt (by simpa [dist_eq_norm] using hyz)
    nlinarith [norm_nonneg (y - z)]
  have h2 : ‖D n z‖ ≤ ε / 2 := hn z hz
  have hsplit : D n y = D n (y - z) + D n z := by rw [map_sub]; abel
  calc ‖D n y‖ ≤ ‖D n (y - z)‖ + ‖D n z‖ := by rw [hsplit]; exact norm_add_le _ _
    _ ≤ M' * δ + ε / 2 := add_le_add h1 h2
    _ = ε := by rw [hMδ]; ring
#print axioms solution
