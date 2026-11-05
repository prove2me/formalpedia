-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_varying_grid_stopped_martingale_sampled_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:51:00.50833+00:00
-- url     : https://prove2.me/submissions/111ca4d9-e73e-4ab2-af2e-30f81f4dcf83

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_every_grid_stopped_martingale_mean_from_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finite_grid_stoppedValue_is_sampled_value

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true original process sampled at each own-grid bounded stopping time is centred when its initial cell is centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ≥0 → Ω → ℝ)
    (hf : Martingale f 𝓕.rightCont P)
    (e : ℕ → ℕ → ℝ≥0) (he : ∀ k, Monotone (e k))
    (𝓖 : ℕ → Filtration ℕ mΩ)
    (h𝓖 : ∀ k, 𝓖 k =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e k i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he k hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e k i) } : Filtration ℕ mΩ))
    (hSF : ∀ k, SigmaFiniteFiltration P (𝓖 k))
    (K : ℕ → Ω → ℕ)
    (hK : ∀ k, IsStoppingTime (𝓖 k) (fun ω => (K k ω : WithTop ℕ)))
    (N : ℕ → ℕ) (hN : ∀ k ω, K k ω ≤ N k)
    (hInit : ∀ k, (∫ ω, stoppedValue (fun i : ℕ => f (e k i))
      (fun _ : Ω => (0 : WithTop ℕ)) ω ∂P) = 0) :
    ∀ k, (∫ ω, f (e k (K k ω)) ω ∂P) = 0 := by
  intro k
  have hStop :=
    avram_p4_e_localise_original_every_grid_stopped_martingale_mean_from_zero
      X f hf e he 𝓖 h𝓖 hSF K hK N hN k
  have hPoint : (fun ω : Ω => f (e k (K k ω)) ω) =
      (fun ω : Ω => stoppedValue (fun i : ℕ => f (e k i))
        (fun ω => (K k ω : WithTop ℕ)) ω) := by
    funext ω
    exact (avram_p4_e_localise_original_finite_grid_stoppedValue_is_sampled_value
      X f (e k) (K k) ω).symm
  rw [hPoint]
  exact hStop.trans (hInit k)
