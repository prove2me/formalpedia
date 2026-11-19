-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_initial_condexp_zero_of_L1_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T01:01:16.756562+00:00
-- url     : https://prove2.me/submissions/a228183a-12c4-4712-8845-dbb36fab2490

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (ℋ : MeasurableSpace Ω) (hℋ : ℋ ≤ mΩ)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hFI : ∀ n, Integrable (f n) P) (hGI : Integrable g P)
    (hZero : ∀ n, P[f n | ℋ] =ᵐ[P] (fun _ => (0 : ℝ)))
    (hL1 : Tendsto (fun n => eLpNorm (fun ω => g ω - f n ω) 1 P)
      atTop (nhds 0)) :
    P[g | ℋ] =ᵐ[P] (fun _ => (0 : ℝ)) := by
  have hBound (n : ℕ) :
      eLpNorm (P[g | ℋ]) 1 P ≤
        eLpNorm (fun ω => g ω - f n ω) 1 P := by
    have hSub : P[(fun ω => g ω - f n ω) | ℋ] =ᵐ[P]
        P[g | ℋ] := by
      have hFunEq : (fun ω => g ω - f n ω) = g - f n := by
        funext ω
        simp only [Pi.sub_apply]
      rw [hFunEq]
      filter_upwards [condExp_sub hGI (hFI n) ℋ,
        hZero n] with ω hEq hZero
      simpa [hEq, hZero]
    calc
      eLpNorm (P[g | ℋ]) 1 P =
          eLpNorm (P[(fun ω => g ω - f n ω) | ℋ]) 1 P :=
            (eLpNorm_congr_ae hSub).symm
      _ ≤ eLpNorm (fun ω => g ω - f n ω) 1 P :=
        eLpNorm_condExp_le_eLpNorm _ le_rfl
  have hLe : eLpNorm (P[g | ℋ]) 1 P ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hL1
      (Filter.Eventually.of_forall hBound)
  have hZeroNorm : eLpNorm (P[g | ℋ]) 1 P = 0 :=
    le_antisymm hLe bot_le
  have hCEint : Integrable (P[g | ℋ]) P :=
    integrable_condExp
  exact (eLpNorm_eq_zero_iff hCEint.aestronglyMeasurable
    (by norm_num : (1 : ℝ≥0∞) ≠ 0)).mp hZeroNorm
