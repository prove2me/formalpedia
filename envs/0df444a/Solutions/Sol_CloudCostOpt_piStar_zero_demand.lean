-- Prove2me | solution 1 for CloudCostOpt.piStar_zero_demand
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T17:55:27.826373+00:00
-- url     : https://prove2.me/submissions/87582f4a-7172-4508-8638-5e8f9a529634

import Mathlib
import Definitions.Def_CloudCostOpt_piStar
import Definitions.Def_CloudCostOpt_avgCost
import Definitions.Def_CloudCostOpt_IsStable
import Definitions.Def_CloudCostOpt_Standing

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

theorem z0_rateX (S : System) (sel : Selection S) (i : Fin S.I) :
    ∀ s l, rateX S sel 0 i s l = 0 := by
  intro s
  induction s with
  | zero => intro l; simp [rateX]
  | succ s ih => intro l; simp [rateX, ih]

theorem z0_mu (S : System) (sel : Selection S) (j : Fin S.J) : mu S sel 0 j = 0 := by
  simp [mu, z0_rateX]

theorem z0_piStar_M (S : System) (sel : Selection S) (j : Fin S.J) :
    (piStar S sel 0).M j = 0 := by
  simp [piStar, z0_mu]

theorem z0_poisson : poissonMeasure 0 ({0}ᶜ : Set ℕ) = 0 := by
  rw [poissonMeasure, Measure.sum_apply _ (measurableSet_singleton 0).compl]
  refine ENNReal.tsum_eq_zero.2 fun n => ?_
  rcases n with _ | n
  · simp
  · simp

theorem z0_ae (S : System) : ∀ᵐ ω ∂(sampleMeasure S 0), ω.1 = 0 := by
  have hp : ∀ p : Fin S.I × ℕ, ∀ᵐ x ∂(Measure.infinitePi
      fun p : Fin S.I × ℕ => poissonMeasure ((0 : Fin S.I → ℝ≥0) p.1)), x p = 0 := by
    intro p
    have hmp := measurePreserving_eval_infinitePi
      (fun p : Fin S.I × ℕ => poissonMeasure ((0 : Fin S.I → ℝ≥0) p.1)) p
    have h0 : ∀ᵐ k ∂(poissonMeasure ((0 : Fin S.I → ℝ≥0) p.1)), k = 0 := by
      rw [ae_iff]
      simpa [Set.compl_def] using z0_poisson
    exact hmp.quasiMeasurePreserving.ae h0
  have h1 := ae_all_iff.2 hp
  have h2 : ∀ᵐ x ∂(Measure.infinitePi
      fun p : Fin S.I × ℕ => poissonMeasure ((0 : Fin S.I → ℝ≥0) p.1)), x = 0 :=
    h1.mono fun x hx => funext hx
  unfold sampleMeasure
  exact Measure.quasiMeasurePreserving_fst.ae h2

theorem z0_history (S : System) (π : Policy S) (ω : Omega S) (hω : ω.1 = 0) :
    ∀ n (k : Fin (n + 1)), history S π ω n k = 0 := by
  intro n
  induction n with
  | zero => intro k; rfl
  | succ n ih =>
    have ha : ∀ i s l, l < S.L i → π.a n (history S π ω n) i s l = 0 := by
      intro i s l hl
      funext j
      have h := π.assign_sum n (history S π ω n) i s l hl
      rw [ih (Fin.last n)] at h
      exact (Finset.sum_eq_zero_iff.1 h) j (Finset.mem_univ j)
    intro k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp only [history, Fin.snoc_last]
      funext i s' l'
      simp only [Pi.zero_apply]
      by_cases hL : S.L i ≤ l'
      · rw [if_pos hL]
      · rw [if_neg hL]
        rcases s' with _ | s
        · simp [hω]
        · have h1 : l' < S.L i := by omega
          show (if l' = 0 then 0 else
              cellSucc S ω.2 (n + 1) i s (l' - 1) (π.a n (history S π ω n) i s (l' - 1))) +
            cellFail S ω.2 (n + 1) i s l' (π.a n (history S π ω n) i s l') = 0
          rw [ha i s l' h1]
          by_cases h0 : l' = 0
          · rw [if_pos h0]; simp [cellFail, cellSucc]
          · rw [if_neg h0, ha i s (l' - 1) (by omega)]
            simp [cellFail, cellSucc]
    · simp only [history, Fin.snoc_castSucc]
      exact ih k

theorem z0_periodCost (S : System) (sel : Selection S) (ω : Omega S) (hω : ω.1 = 0) (n : ℕ) :
    periodCost S S.R S.V (piStar S sel 0) ω n = 0 := by
  have hh : history S (piStar S sel 0) ω n = fun _ => 0 :=
    funext (z0_history S (piStar S sel 0) ω hω n)
  have hs : stateAt S (piStar S sel 0) ω n = 0 := z0_history S _ ω hω n (Fin.last n)
  unfold periodCost
  rw [hs, hh]
  simp [piStar, usage, z0_mu]

theorem z0_m (S : System) (sel : Selection S) (ω : Omega S) (hω : ω.1 = 0) (n : ℕ)
    (j : Fin S.J) : (piStar S sel 0).m n (history S (piStar S sel 0) ω n) j = 0 := by
  have hh : history S (piStar S sel 0) ω n = fun _ => 0 :=
    funext (z0_history S (piStar S sel 0) ω hω n)
  rw [hh]
  simp [piStar, usage, z0_mu]

end CloudCostOpt

open CloudCostOpt in
theorem solution (S : System) (_hS : Standing S) (sel : Selection S) :
    IsStable S 0 (piStar S sel 0) ∧ avgCost S S.R S.V 0 (piStar S sel 0) = 0 := by
  have hae := z0_ae S
  have hc : ∀ n, ∫⁻ ω, periodCost S S.R S.V (piStar S sel 0) ω n ∂(sampleMeasure S 0) = 0 :=
    fun n => (lintegral_congr_ae (hae.mono fun ω hω => z0_periodCost S sel ω hω n)).trans
      (lintegral_zero)
  have hm : ∀ n j, ∫⁻ ω, ((piStar S sel 0).m n (history S (piStar S sel 0) ω n) j : ℝ≥0∞)
      ∂(sampleMeasure S 0) = 0 := fun n j =>
    (lintegral_congr_ae (hae.mono fun ω hω => by simp [z0_m S sel ω hω n j])).trans lintegral_zero
  have hx : ∀ n i s l, ∫⁻ ω, (stateAt S (piStar S sel 0) ω n i s l : ℝ≥0∞)
      ∂(sampleMeasure S 0) = 0 := fun n i s l =>
    (lintegral_congr_ae (hae.mono fun ω hω => by
      simp [stateAt, z0_history S (piStar S sel 0) ω hω n (Fin.last n)])).trans lintegral_zero
  refine ⟨⟨fun j => ⟨0, ?_⟩, fun i s l => ⟨0, ?_⟩⟩, ?_⟩
  · simp only [hm, Finset.sum_const_zero, ENNReal.zero_div, ENNReal.coe_zero]
    exact tendsto_const_nhds
  · simp only [hx, Finset.sum_const_zero, ENNReal.zero_div, ENNReal.coe_zero]
    exact tendsto_const_nhds
  · unfold avgCost
    simp only [hc, Finset.sum_const_zero, ENNReal.zero_div]
    exact Filter.liminf_const 0
