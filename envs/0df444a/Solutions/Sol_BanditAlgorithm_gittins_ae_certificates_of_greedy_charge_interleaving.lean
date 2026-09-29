-- Prove2me | solution 1 for BanditAlgorithm.gittins_ae_certificates_of_greedy_charge_interleaving
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-01T17:28:28.092179+00:00
-- url     : https://prove2.me/submissions/dee54b77-6763-4fba-8a88-a26cb8724c2e

import Theorems.Thm_BanditAlgorithm_gittins_index_policy_dominates
import Definitions.Def_GittinsChargeInterleaving

open MeasureTheory ProbabilityTheory ENNReal

theorem solution
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : BanditAlgorithm.DiscountedRewardIntegrable P r α)
    (hcal : ∀ (y : S) (ε : ℝ), 0 < ε →
      ∃ τ : (ℕ → S) → ℕ∞,
        BanditAlgorithm.IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
        BanditAlgorithm.gittinsIndex P r α y - ε <
          (∫ ω, BanditAlgorithm.discountedStoppedSum α r τ ω
            ∂BanditAlgorithm.markovChainMeasure P y) /
            (∫ ω, BanditAlgorithm.discountedStoppedSum α (fun _ ↦ 1) τ ω
              ∂BanditAlgorithm.markovChainMeasure P y))
    (πstar : BanditAlgorithm.MarkovBanditPolicy k S)
    (hπ : BanditAlgorithm.IsGittinsIndexPolicy P r α πstar)
    (x : Fin k → S) (π : BanditAlgorithm.MarkovBanditPolicy k S)
    (hinterleaving :
      ∀ {H : Fin k → ℕ → ℝ} {astar : ℕ → Fin k},
        (∀ i, Antitone (H i)) →
        BanditAlgorithm.IsGreedyChargeStackInterleaving H astar →
        ∀ (a : ℕ → Fin k),
          Summable (fun n ↦ α ^ n *
            BanditAlgorithm.chargeStackInterleaving H a n) →
          Summable (fun n ↦ α ^ n *
            BanditAlgorithm.chargeStackInterleaving H astar n) →
          (∑' n : ℕ, α ^ n *
            BanditAlgorithm.chargeStackInterleaving H a n) ≤
            ∑' n : ℕ, α ^ n *
              BanditAlgorithm.chargeStackInterleaving H astar n) :
    ∃ μ : Measure
        ((Fin k → ℕ → S) × ((ℕ → Fin k) × (ℕ → Fin k))),
      ∀ ε : ℝ, 0 < ε →
        ∃ xs ys :
            ((Fin k → ℕ → S) × ((ℕ → Fin k) × (ℕ → Fin k))) →
              List ℝ,
          (∀ᵐ ω ∂μ, (xs ω).Perm (ys ω) ∧
            (ys ω).Pairwise (· ≥ ·)) ∧
          Integrable
            (fun ω ↦ (xs ω).foldr (fun z acc ↦ z + α * acc) 0) μ ∧
          Integrable
            (fun ω ↦ (ys ω).foldr (fun z acc ↦ z + α * acc) 0) μ ∧
          BanditAlgorithm.markovBanditDiscountedValue P r α π x ≤
            (∫ ω, (xs ω).foldr (fun z acc ↦ z + α * acc) 0 ∂μ) + ε ∧
          (∫ ω, (ys ω).foldr (fun z acc ↦ z + α * acc) 0 ∂μ) ≤
            BanditAlgorithm.markovBanditDiscountedValue P r α πstar x + ε := by
  clear hcal hinterleaving
  have hdom := BanditAlgorithm.gittins_index_policy_dominates
    P hr hα0 hα1 hint πstar hπ x π
  cases k with
  | zero =>
      let h0 : BanditAlgorithm.MarkovBanditHistory 0 S 0 :=
        (fun t ↦ t.elim0, x)
      have hmass : ((πstar.select 0) h0) Set.univ = 1 :=
        IsProbabilityMeasure.measure_univ
      have hempty : (Set.univ : Set (Fin 0)) = ∅ := by
        ext i
        exact i.elim0
      rw [hempty, measure_empty] at hmass
      exact (zero_ne_one hmass).elim
  | succ k =>
      let i0 : Fin (k + 1) := 0
      let ω0 :
          (Fin (k + 1) → ℕ → S) ×
            ((ℕ → Fin (k + 1)) × (ℕ → Fin (k + 1))) :=
        ((fun i _ ↦ x i), (fun _ ↦ i0), (fun _ ↦ i0))
      let V := BanditAlgorithm.markovBanditDiscountedValue P r α π x
      refine ⟨Measure.dirac ω0, ?_⟩
      intro ε hε
      let cert := fun _ :
          (Fin (k + 1) → ℕ → S) ×
            ((ℕ → Fin (k + 1)) × (ℕ → Fin (k + 1))) ↦ [V]
      refine ⟨cert, cert, ?_, ?_, ?_, ?_, ?_⟩
      · exact Filter.Eventually.of_forall fun _ ↦ by simp [cert]
      · simpa [cert] using
          (integrable_const V : Integrable
            (fun _ :
              (Fin (k + 1) → ℕ → S) ×
                ((ℕ → Fin (k + 1)) × (ℕ → Fin (k + 1))) ↦ V)
              (Measure.dirac ω0))
      · simpa [cert] using
          (integrable_const V : Integrable
            (fun _ :
              (Fin (k + 1) → ℕ → S) ×
                ((ℕ → Fin (k + 1)) × (ℕ → Fin (k + 1))) ↦ V)
              (Measure.dirac ω0))
      · simp [cert, V]
        exact hε.le
      · simp [cert, V]
        exact hdom.trans (le_add_of_nonneg_right hε.le)
