-- Prove2me | solution 1 for BanditAlgorithm.pmVectorEstimator_importance_weighted_gap
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T20:26:08.404188+00:00
-- url     : https://prove2.me/submissions/d3429133-378e-4499-a34b-a7fccee8ac93

import Definitions.Def_PartialMonitoringAlgorithm26

open scoped BigOperators

namespace BanditAlgorithm

theorem _root_.solution
    {k d : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊) (S : Finset (Fin k))
    (q p : Fin k → ℝ) (f : Fin k → 𝕊 → Fin k → ℝ)
    (hq : PMSupportedOn S q) (hp : PMInteriorDistribution p)
    (hf : PMVectorEstimatorOn G S f) (i : Fin d) (b : Fin k) (hb : b ∈ S) :
    ∑ a : Fin k, p a *
        (∑ c : Fin k, q c *
          (f a (G.Φ a i) c / p a - f a (G.Φ a i) b / p a)) =
      ∑ c : Fin k, q c * (G.L c i - G.L b i) := by
  classical
  obtain ⟨r, hr⟩ := hf.2 i
  have hcancel (c : Fin k) :
      ∑ a : Fin k, p a *
          (f a (G.Φ a i) c / p a - f a (G.Φ a i) b / p a) =
        ∑ a : Fin k, (f a (G.Φ a i) c - f a (G.Φ a i) b) := by
    apply Finset.sum_congr rfl
    intro a ha
    field_simp [ne_of_gt (hp.2 a)]
  rw [show (∑ a : Fin k, p a *
      (∑ c : Fin k, q c *
        (f a (G.Φ a i) c / p a - f a (G.Φ a i) b / p a))) =
      ∑ c : Fin k, q c *
        (∑ a : Fin k, p a *
          (f a (G.Φ a i) c / p a - f a (G.Φ a i) b / p a)) by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro a ha
    ring]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hcS : c ∈ S
  · rw [hcancel]
    rw [Finset.sum_sub_distrib, hr c hcS, hr b hb]
    ring
  · rw [hq.2 c hcS]
    simp

end BanditAlgorithm
