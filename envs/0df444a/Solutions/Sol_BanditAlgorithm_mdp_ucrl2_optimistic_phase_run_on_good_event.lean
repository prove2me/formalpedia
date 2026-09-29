-- Prove2me | solution 1 for BanditAlgorithm.mdp_ucrl2_optimistic_phase_run_on_good_event
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T20:42:01.431348+00:00
-- url     : https://prove2.me/submissions/6a605ed4-6af2-425e-bc6e-6bd8081029a1

import Theorems.Thm_BanditAlgorithm_mdp_ucrl2_confidence_event_complement_prob_le
import Theorems.Thm_BanditAlgorithm_mdp_ucrl2_optimistic_phase_run_on_confidence_event

open MeasureTheory ProbabilityTheory ENNReal BanditAlgorithm

/-!
The probabilistic half of the analysis of UCRL2, split along its good event.

The good event is the intersection of two events: the confidence event, that the
true transition rows lie in every confidence ball built from the trajectory, and
a second event on which the martingale fluctuation of the run is controlled.
The first is bounded by `δ/2` for *every* policy -- it is a statement about the
estimates alone -- and the second by `δ/2` for the policy that the constructing
child exhibits.  The reduction is the union bound.
-/

theorem solution
    (S A n : ℕ) (hS : 2 ≤ S) (hA : 0 < A) (hn : 0 < n)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (r : Fin S → Fin A → ℝ) (hr : ∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1) :
    ∃ π : MDPPolicy S A,
      ∀ M : FiniteMDP S A, M.r = r → M.IsCommunicating → 1 ≤ mdpDiameter M →
        ∀ μ0 : MDPStateDistribution S,
          ∃ G : Set (MDPTrajectory S A n),
            mdpMeasure M μ0 π n Gᶜ ≤ ENNReal.ofReal δ ∧
            ∀ h ∈ G,
              ∃ (st : ℕ → Fin S) (act : ℕ → Fin A) (K : ℕ) (τ : ℕ → ℕ)
                (ρ : ℕ → ℝ) (v : ℕ → Fin S → ℝ) (q : ℕ → Fin S → Fin S → ℝ),
                (∀ t : Fin n, h t = (st t, act t)) ∧
                τ 0 = 0 ∧ τ K = n ∧ (∀ k, τ k ≤ τ (k + 1)) ∧
                (K : ℝ) ≤ 3 * Real.sqrt (S * A * n) ∧
                (∀ k < K, mdpOptimalGain M ≤ ρ k) ∧
                (∀ k < K, ∀ x y : Fin S, v k x - v k y ≤ mdpDiameter M) ∧
                (∀ k < K, ∀ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                  ρ k + v k (st t)
                    = M.r (st t) (act t) + ∑ s', q k (st t) s' * v k s') ∧
                (∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                    ∑ s', (q k (st t) s' - (M.P (st t) (act t) s' : ℝ)) * v k s'
                  ≤ mdpDiameter M * (Real.sqrt 2 + 1) *
                      Real.sqrt (14 * S * Real.log (2 * S * A * n / δ)) *
                      Real.sqrt (S * A * n)) ∧
                (∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                    ((∑ s', (M.P (st t) (act t) s' : ℝ) * v k s') - v k (st (t + 1)))
                  ≤ mdpDiameter M * Real.sqrt (2 * n * Real.log (2 / δ))) := by
  obtain ⟨π, hrun⟩ :=
    BanditAlgorithm.mdp_ucrl2_optimistic_phase_run_on_confidence_event
      S A n hS hA hn δ hδ r hr
  refine ⟨π, ?_⟩
  intro M hMr hMcomm hMD μ0
  obtain ⟨E, hE, hcert⟩ := hrun M hMr hMcomm hMD μ0
  refine ⟨mdpConfidenceGoodEvent M n δ ∩ E, ?_, hcert⟩
  have hconf :=
    BanditAlgorithm.mdp_ucrl2_confidence_event_complement_prob_le
      S A n hS hA hn δ hδ M π μ0
  have hδ0 : (0 : ℝ) < δ := hδ.1
  calc mdpMeasure M μ0 π n (mdpConfidenceGoodEvent M n δ ∩ E)ᶜ
      = mdpMeasure M μ0 π n ((mdpConfidenceGoodEvent M n δ)ᶜ ∪ Eᶜ) := by
        rw [Set.compl_inter]
    _ ≤ mdpMeasure M μ0 π n (mdpConfidenceGoodEvent M n δ)ᶜ
          + mdpMeasure M μ0 π n Eᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hconf hE
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1
        ring
