-- Prove2me | solution 1 for GarrettFA.metric_net_complete_of_seq_complete
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:50:03.889871+00:00
-- url     : https://prove2.me/submissions/a0de6fb3-98df-4e95-bd97-8658a28e47b3

import Mathlib

theorem solution {M : Type*} [MetricSpace M]
    (hM : ∀ u : ℕ → M, CauchySeq u → ∃ x, Filter.Tendsto u Filter.atTop (nhds x))
    {I : Type*} [PartialOrder I] [IsDirected I (· ≤ ·)] (v : I → M)
    (hv : ∀ ε > 0, ∃ i₀ : I, ∀ i ≥ i₀, ∀ j ≥ i₀, dist (v i) (v j) < ε) :
    ∃ x : M, (∀ ε > 0, ∃ i₀ : I, ∀ i ≥ i₀, dist (v i) x < ε) ∧
      ∃ s : ℕ → I, Monotone s ∧ Filter.Tendsto (v ∘ s) Filter.atTop (nhds x) := by
  choose i0 hi0 using fun n : ℕ => hv (1 / ((n : ℝ) + 1)) (by positivity)
  let step : I → ℕ → I := fun a n => Classical.choose (exists_ge_ge a (i0 (n + 1)))
  have hstep : ∀ a n, a ≤ step a n ∧ i0 (n + 1) ≤ step a n := fun a n =>
    Classical.choose_spec (exists_ge_ge a (i0 (n + 1)))
  let s : ℕ → I := fun n => Nat.rec (i0 0) (fun n a => step a n) n
  have hs0 : s 0 = i0 0 := rfl
  have hsS : ∀ n, s (n + 1) = step (s n) n := fun n => rfl
  have hmono : Monotone s := monotone_nat_of_le_succ fun n => by rw [hsS]; exact (hstep _ _).1
  have hge : ∀ n, i0 n ≤ s n := by
    intro n
    cases n with
    | zero => exact le_of_eq hs0.symm
    | succ n => rw [hsS]; exact (hstep _ _).2
  have hclose : ∀ n, ∀ i ≥ i0 n, ∀ m ≥ n, dist (v i) (v (s m)) < 1 / ((n : ℝ) + 1) := by
    intro n i hi m hm
    exact hi0 n i hi (s m) ((hge n).trans (hmono hm))
  have hcauchy : CauchySeq (v ∘ s) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hn => ?_⟩
    have := hclose N (s n) ((hge N).trans (hmono hn)) N le_rfl
    simp only [Function.comp_apply]
    linarith
  obtain ⟨x, hx⟩ := hM _ hcauchy
  refine ⟨x, fun ε hε => ?_, s, hmono, hx⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
  refine ⟨i0 n, fun i hi => ?_⟩
  have hev := (Metric.tendsto_atTop.1 hx) (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨K, hK⟩ := hev
  have h1 := hK (max K n) (le_max_left _ _)
  have h2 := hclose n i hi (max K n) (le_max_right _ _)
  simp only [Function.comp_apply] at h1
  calc dist (v i) x ≤ dist (v i) (v (s (max K n))) + dist (v (s (max K n))) x := dist_triangle _ _ _
    _ < ε := by linarith
