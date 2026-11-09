-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite12_original_clock_ceiling_two_gaussian_condexp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T11:30:59.76185+00:00
-- url     : https://prove2.me/submissions/8dbe0606-2425-427a-ae2b-59224634f403

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_arbitrary_clock_true_grid_ceiling
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite11_original_zerojump_two_stopped_grid_condexp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Arbitrary original source stopping clocks admit a nearby genuine sampled
stop at which both zero-jump Gaussian martingales satisfy optional sampling. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (N : ℕ) (hN : ∀ ω, σ ω ≤ e N)
    (δ : ℝ≥0) (h0 : e 0 = 0)
    (hStep : ∀ i, e (i + 1) ≤ e i + δ)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e i) } : Filtration ℕ mΩ)) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
    let Q : ℝ≥0 → Ω → ℝ := fun t ω =>
      (M t ω) ^ 2 - (t : ℝ) * X.σ ^ 2
    ∃ (K : Ω → ℕ)
      (hK : IsStoppingTime 𝓖 (fun ω => (K ω : WithTop ℕ))),
      (∀ ω, (K ω : WithTop ℕ) ≤ (N : WithTop ℕ)) ∧
      (∀ ω, σ ω ≤ e (K ω) ∧ e (K ω) ≤ σ ω + δ) ∧
      (stoppedValue (fun i : ℕ => M (e i))
        (fun ω => (K ω : WithTop ℕ)) =ᵐ[P]
        P[stoppedValue (fun i : ℕ => M (e i))
          (fun _ : Ω => (N : WithTop ℕ)) | hK.measurableSpace]) ∧
      (stoppedValue (fun i : ℕ => Q (e i))
        (fun ω => (K ω : WithTop ℕ)) =ᵐ[P]
        P[stoppedValue (fun i : ℕ => Q (e i))
          (fun _ : Ω => (N : WithTop ℕ)) | hK.measurableSpace]) := by
  obtain ⟨K, hK, hKN, hMesh⟩ :=
    avram_ubv_finite12_arbitrary_clock_true_grid_ceiling
      σ hσ e he N hN δ h0 hStep 𝓖 h𝓖
  have hNstop : IsStoppingTime 𝓖 (fun _ : Ω => (N : WithTop ℕ)) := by
    exact isStoppingTime_const 𝓖 N
  have hSample := avram_ubv_finite11_original_zerojump_two_stopped_grid_condexp
    X hν e he 𝓖 h𝓖
    (fun ω => (K ω : WithTop ℕ)) (fun _ : Ω => (N : WithTop ℕ))
    hK hNstop hKN N (fun ω => le_rfl)
  exact ⟨K, hK, hKN, hMesh, hSample⟩
