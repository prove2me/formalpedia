-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_locally_observable_objective_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T17:42:29.819828+00:00
-- url     : https://prove2.me/submissions/08b9226f-5a66-4352-bd89-d3da3aeb243a

import Theorems.Thm_BanditAlgorithm_partial_monitoring_locally_observable_water_transfer_certificate
import Theorems.Thm_BanditAlgorithm_pmPsi_le_quadratic

open scoped BigOperators

namespace BanditAlgorithm

theorem _root_.solution
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k)
    (hd : 0 < d)
    (hL : ∀ a i, G.L a i ∈ Set.Icc (0 : ℝ) 1)
    (hloc : LocallyObservable G) :
    ∃ S : Finset (Fin k), ∃ A η₀ : ℝ,
      S.Nonempty ∧ 0 ≤ A ∧ 0 < η₀ ∧
      (∀ (n : ℕ) (i : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (i t) ≤ ∑ t, G.L a (i t)) ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∀ q : Fin k → ℝ, PMSupportedOn S q →
          ∃ p : Fin k → ℝ, ∃ f : Fin k → 𝕊 → Fin k → ℝ,
            PMInteriorDistribution p ∧ PMVectorEstimatorOn G S f ∧
            ∀ i : Fin d, pmAlgorithm26Objective G η q p f i ≤ A := by
  obtain ⟨S, K, η₀, hS, hK, hη₀, hbest, hcert⟩ :=
    partial_monitoring_locally_observable_water_transfer_certificate G hk hd hL hloc
  refine ⟨S, 2 * K, η₀, hS, by positivity, hη₀, hbest, ?_⟩
  intro η hη hηle q hq
  obtain ⟨p, f, hp, hf, hloss, hz, hquad⟩ := hcert η hη hηle q hq
  refine ⟨p, f, hp, hf, ?_⟩
  intro i
  have hpsi (a : Fin k) :
      pmPsi q (fun b => η * f a (G.Φ a i) b / p a) ≤
        ∑ b : Fin k, q b * (η * f a (G.Φ a i) b / p a) ^ 2 :=
    pmPsi_le_quadratic q _ hq.1 (fun b => hz a (G.Φ a i) b)
  have hpsum :
      ∑ a : Fin k, p a * pmPsi q (fun b => η * f a (G.Φ a i) b / p a) ≤
        η ^ 2 * K := by
    calc
      _ ≤ ∑ a : Fin k, p a *
          (∑ b : Fin k, q b * (η * f a (G.Φ a i) b / p a) ^ 2) :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpsi a) (hp.1.1 a)
      _ ≤ _ := hquad i
  unfold pmAlgorithm26Objective
  have hfirst := mul_le_mul_of_nonneg_left (hloss i) (by positivity : 0 ≤ 1 / η)
  have hsecond := mul_le_mul_of_nonneg_left hpsum (by positivity : 0 ≤ 1 / η ^ 2)
  have heta : η ≠ 0 := hη.ne'
  calc
    _ ≤ (1 / η) * (η * K) + (1 / η ^ 2) * (η ^ 2 * K) := add_le_add hfirst hsecond
    _ = 2 * K := by
      field_simp [heta]
      ring

end BanditAlgorithm
