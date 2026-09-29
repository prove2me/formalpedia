-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_locally_observable_algorithm26_solver
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T17:37:06.795176+00:00
-- url     : https://prove2.me/submissions/89ac90f5-520a-454a-b46f-cff9bd0e4560

import Theorems.Thm_BanditAlgorithm_partial_monitoring_locally_observable_objective_uniform_bound
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

namespace BanditAlgorithm

noncomputable section

theorem _root_.solution
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k)
    (hd : 0 < d)
    (hL : ∀ a i, G.L a i ∈ Set.Icc (0 : ℝ) 1)
    (hloc : LocallyObservable G) :
    ∃ S : Finset (Fin k), ∃ C : ℝ, S.Nonempty ∧ 0 < C ∧
      (∀ (n : ℕ) (i : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (i t) ≤ ∑ t, G.L a (i t)) ∧
      ∀ n : ℕ, 0 < n → ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧
        Real.log S.card / η + (n : ℝ) * η * B ≤
          C * max 1 (pmLocObsConst G) * (k : ℝ) ^ ((3 : ℝ) / 2) *
            Real.sqrt (n * Real.log k) ∧
          ∀ q : Fin k → ℝ, PMSupportedOn S q →
            ∃ p : Fin k → ℝ, ∃ f : Fin k → 𝕊 → Fin k → ℝ,
              PMInteriorDistribution p ∧ PMVectorEstimatorOn G S f ∧
              ∀ i : Fin d, pmAlgorithm26Objective G η q p f i ≤ B := by
  obtain ⟨S, A, η₀, hS, hA, hη₀, hbest, hopt⟩ :=
    partial_monitoring_locally_observable_objective_uniform_bound G hk hd hL hloc
  let M := max 1 (pmLocObsConst G) * (k : ℝ) ^ ((3 : ℝ) / 2) *
    Real.sqrt (Real.log k)
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  have hlogk : 0 < Real.log k := Real.log_pos hkR
  have hkpow : 0 < (k : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hlogS : 0 ≤ Real.log S.card := by
    have hScard : 1 ≤ S.card := Finset.one_le_card.mpr hS
    exact Real.log_nonneg (by exact_mod_cast hScard)
  let D := Real.log S.card + Real.log S.card / η₀ + A
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  let C := D / M + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨S, C, hS, hC, hbest, ?_⟩
  intro n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  let η := η₀ / (η₀ * Real.sqrt n + 1)
  have hden : 0 < η₀ * Real.sqrt n + 1 := by positivity
  have hη : 0 < η := div_pos hη₀ hden
  have hηle : η ≤ η₀ := by
    rw [div_le_iff₀ hden]
    have : 1 ≤ η₀ * Real.sqrt n + 1 := by
      nlinarith [mul_pos hη₀ hsqrtn]
    nlinarith
  have hnsqrt : (n : ℝ) ≤ Real.sqrt n * Real.sqrt n := by
    rw [Real.mul_self_sqrt hnR.le]
  have hsqrtone : 1 ≤ Real.sqrt n := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hscalar :
      Real.log S.card / η + (n : ℝ) * η * A ≤ D * Real.sqrt n := by
    have hetaInv : Real.log S.card / η =
        Real.log S.card * Real.sqrt n + Real.log S.card / η₀ := by
      dsimp [η]
      field_simp [hη₀.ne']
    rw [hetaInv]
    have hnet : (n : ℝ) * η ≤ Real.sqrt n := by
      nth_rewrite 1 [show (n : ℝ) = Real.sqrt n * Real.sqrt n by
        exact (Real.mul_self_sqrt hnR.le).symm]
      dsimp [η]
      have hin : Real.sqrt n * η₀ / (η₀ * Real.sqrt n + 1) ≤ 1 := by
        rw [div_le_one hden]
        nlinarith
      calc
        Real.sqrt n * Real.sqrt n * (η₀ / (η₀ * Real.sqrt n + 1)) =
            Real.sqrt n * (Real.sqrt n * η₀ / (η₀ * Real.sqrt n + 1)) := by ring
        _ ≤ Real.sqrt n * 1 := mul_le_mul_of_nonneg_left hin hsqrtn.le
        _ = Real.sqrt n := mul_one _
    have hAterm := mul_le_mul_of_nonneg_right hnet hA
    dsimp [D]
    calc
      Real.log S.card * Real.sqrt n + Real.log S.card / η₀ +
          (n : ℝ) * η * A ≤
        Real.log S.card * Real.sqrt n + Real.log S.card / η₀ +
          Real.sqrt n * A := by linarith
      _ ≤ (Real.log S.card + Real.log S.card / η₀ + A) * Real.sqrt n := by
        have := mul_le_mul_of_nonneg_left hsqrtone
          (div_nonneg hlogS hη₀.le)
        nlinarith
  refine ⟨η, A, hη, hA, ?_, hopt η hη hηle⟩
  have hsqrtmul : Real.sqrt (n * Real.log k) =
      Real.sqrt n * Real.sqrt (Real.log k) := by
    rw [Real.sqrt_mul (by positivity)]
  rw [hsqrtmul]
  rw [show C * max 1 (pmLocObsConst G) * (k : ℝ) ^ ((3 : ℝ) / 2) *
      (Real.sqrt n * Real.sqrt (Real.log k)) = C * M * Real.sqrt n by
    dsimp [M]
    ring]
  calc
    _ ≤ D * Real.sqrt n := hscalar
    _ ≤ C * M * Real.sqrt n := by
      apply mul_le_mul_of_nonneg_right _ hsqrtn.le
      dsimp [C]
      field_simp [hM.ne']
      nlinarith [hM]

end
end BanditAlgorithm
