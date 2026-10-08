-- Prove2me | solution 1 for EthierKurtz.lipschitz_holder_closure
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-07T03:52:59.076447+00:00
-- url     : https://prove2.me/submissions/8490a615-eb45-4013-8110-fd20a4910148

import Mathlib

open Filter
open scoped Topology BoundedContinuousFunction

theorem solution (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω)
    (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1) :
    ∀ (h : (closure Ω) →ᵇ ℝ) (K : NNReal),
      LipschitzWith K ⇑h →
        ∃ C : NNReal, HolderWith C ⟨μ, hμ.1.le⟩ ⇑h := by
  intro h K hLip
  by_cases hΩ : Ω.Nonempty
  · obtain ⟨c₀, hc₀⟩ := hΩ
    obtain ⟨r, hr⟩ := hbounded.closure.subset_closedBall c₀
    have hball : ∀ z : closure Ω, dist z.val c₀ ≤ |r| := by
      intro z
      have hmem : z.val ∈ Metric.closedBall c₀ r := hr z.property
      rw [Metric.mem_closedBall] at hmem
      exact le_trans hmem (le_abs_self _)
    have hD : ∀ x y : closure Ω, dist x y ≤ 2 * |r| := by
      intro x y
      calc dist x y = dist x.val y.val := Subtype.dist_eq _ _
        _ ≤ dist x.val c₀ + dist y.val c₀ := by
            rw [dist_comm y.val c₀]
            exact dist_triangle _ _ _
        _ ≤ |r| + |r| := add_le_add (hball x) (hball y)
        _ = 2 * |r| := by ring
    have hM0 : (0 : ℝ) ≤ max 1 ((2 * |r|) ^ (1 - μ)) :=
      le_trans zero_le_one (le_max_left _ _)
    refine ⟨K * ⟨max 1 ((2 * |r|) ^ (1 - μ)), hM0⟩, ?_⟩
    intro x y
    have hnn : 0 ≤ dist x y := dist_nonneg
    have hle : dist x y ≤ 2 * |r| := hD x y
    have hLipd : dist (⇑h x) (⇑h y) ≤ K * dist x y :=
      (lipschitzWith_iff_dist_le_mul.mp hLip) x y
    have hpow : (dist x y) ^ (1 - μ)
        ≤ max 1 ((2 * |r|) ^ (1 - μ)) :=
      le_trans (Real.rpow_le_rpow hnn hle (by linarith)) (le_max_right _ _)
    have hmain : dist (⇑h x) (⇑h y)
        ≤ (K : ℝ) * (max 1 ((2 * |r|) ^ (1 - μ))) * (dist x y) ^ μ := by
      by_cases hd0 : dist x y = 0
      · rw [hd0, mul_zero] at hLipd
        rw [hd0, Real.zero_rpow (ne_of_gt hμ.1), mul_zero]
        exact hLipd
      · have hpos : 0 < dist x y := lt_of_le_of_ne hnn (Ne.symm hd0)
        have hsplit : dist x y
            = (dist x y) ^ μ * (dist x y) ^ (1 - μ) := by
          have e := Real.rpow_add hpos μ (1 - μ)
          rw [show μ + (1 - μ) = 1 by ring, Real.rpow_one] at e
          exact e
        calc dist (⇑h x) (⇑h y)
              ≤ (K : ℝ) * ((dist x y) ^ μ * (dist x y) ^ (1 - μ)) := by
              rw [← hsplit]; exact hLipd
          _ = (K * (dist x y) ^ μ) * (dist x y) ^ (1 - μ) := by ring
          _ ≤ (K * (dist x y) ^ μ) * (max 1 ((2 * |r|) ^ (1 - μ))) :=
              mul_le_mul_of_nonneg_left hpow
                (mul_nonneg K.coe_nonneg (Real.rpow_nonneg hnn _))
          _ = (K : ℝ) * (max 1 ((2 * |r|) ^ (1 - μ))) * (dist x y) ^ μ := by
              ring
    rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg,
      ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    rw [dist_nndist] at hmain
    simp only [NNReal.coe_mul, NNReal.coe_rpow] at hmain ⊢
    · exact hmain
    · exact NNReal.coe_nonneg _
  · obtain rfl := Set.not_nonempty_iff_eq_empty.mp hΩ
    refine ⟨0, fun x y => ?_⟩
    exfalso
    have hx : x.val ∈ (∅ : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
      simpa using x.property
    exact Set.notMem_empty _ hx

