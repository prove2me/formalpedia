-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a364_selected_small_budget_of_ae_modulus_and_vanishing_sources
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:31:13.331195+00:00
-- url     : https://prove2.me/submissions/5f85044f-67ec-406b-8329-f03d8d43c600

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a363_selected_threshold_ae_energy_majorant_implies_positive_integrability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℝ → ℕ → Ω → ℝ)
    (E A : ℕ → Ω → ℝ) (B : ℝ → ℕ → Ω → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hSm : ∀ δ, 0 < δ → ∀ m,
      AEStronglyMeasurable (fun ω => max (S δ m ω) 0) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hAI : ∀ m, Integrable (A m) P)
    (hBI : ∀ ε, 0 < ε → ∀ m, Integrable (B ε m) P)
    (hEB : ∀ m, (∫ ω, E m ω ∂P) ≤ K)
    (hAL : Tendsto (fun m => ∫ ω, A m ω ∂P) atTop (𝓝 (0 : ℝ)))
    (hBL : ∀ ε, 0 < ε →
      Tendsto (fun m => ∫ ω, B ε m ω ∂P) atTop (𝓝 (0 : ℝ)))
    (hMod : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧
      ∀ m, ∀ᵐ ω ∂P,
        max (S δ m ω) 0 ≤
          ε * E m ω + A m ω + B ε m ω) :
    ∀ η, 0 < η → ∃ δ, 0 < δ ∧
      (∀ m, Integrable (fun ω => max (S δ m ω) 0) P) ∧
      ∃ k : ℕ, ∀ m, k ≤ m →
        (∫ ω, max (S δ m ω) 0 ∂P) ≤ η := by
  intro η hη
  let ε : ℝ := η / (4*(K+1))
  have hKpos : 0 < K+1 := by linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨δ,hδ,hPt⟩ := hMod ε hε
  have hSI : ∀ m, Integrable (fun ω => max (S δ m ω) 0) P :=
    avram_ga_a363_selected_threshold_ae_energy_majorant_implies_positive_integrability
      P S E A (B ε) δ ε hδ hε.le (hSm δ hδ)
      hEI hAI (hBI ε hε) hPt
  have hAB : Tendsto
      (fun m => (∫ ω, A m ω ∂P)+(∫ ω, B ε m ω ∂P))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_zero] using hAL.add (hBL ε hε)
  have hSmall : ∀ᶠ m : ℕ in atTop,
      (∫ ω, A m ω ∂P)+(∫ ω, B ε m ω ∂P) < η/2 :=
    hAB.eventually (isOpen_Iio.mem_nhds (by linarith : (0:ℝ)<η/2))
  obtain ⟨k,hk⟩ := Filter.eventually_atTop.1 hSmall
  refine ⟨δ,hδ,hSI,k,?_⟩
  intro m hm
  have hMajor : Integrable
      (fun ω => ε*E m ω+A m ω+B ε m ω) P :=
    (((hEI m).const_mul ε).add (hAI m)).add (hBI ε hε m)
  have hCompare := integral_mono_ae (hSI m) hMajor (hPt m)
  have hUpper :
      (∫ ω, max (S δ m ω) 0 ∂P) ≤
      ε*(∫ ω, E m ω ∂P)+
        (∫ ω, A m ω ∂P)+(∫ ω, B ε m ω ∂P) := by
    calc
      _ ≤ (∫ ω, ε*E m ω+A m ω+B ε m ω ∂P) := hCompare
      _ = ε*(∫ ω, E m ω ∂P)+
            (∫ ω, A m ω ∂P)+(∫ ω, B ε m ω ∂P) := by
        calc
          _ = (∫ ω, ε*E m ω+A m ω ∂P) +
                (∫ ω, B ε m ω ∂P) :=
            integral_add (((hEI m).const_mul ε).add (hAI m)) (hBI ε hε m)
          _ = ε*(∫ ω, E m ω ∂P) +
                (∫ ω, A m ω ∂P)+(∫ ω, B ε m ω ∂P) := by
            rw [integral_add ((hEI m).const_mul ε) (hAI m), integral_const_mul]
  have hεB : ε*K ≤ η/4 := by
    have hprod : ε*K ≤ ε*(K+1) :=
      mul_le_mul_of_nonneg_left (by linarith : K≤K+1) hε.le
    have heq : ε*(K+1)=η/4 := by
      dsimp [ε]
      field_simp
      all_goals ring
    linarith
  have hEnergy := mul_le_mul_of_nonneg_left (hEB m) hε.le
  linarith [hk m hm]
