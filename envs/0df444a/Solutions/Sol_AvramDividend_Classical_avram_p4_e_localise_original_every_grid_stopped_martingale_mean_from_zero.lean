-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_every_grid_stopped_martingale_mean_from_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:39:26.486114+00:00
-- url     : https://prove2.me/submissions/6ea3e682-a514-4588-ab86-87c3415eab95

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat01_monotone_sampling_bounded_optional_stopping_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Each own-grid bounded source martingale stopping index is centred at its deterministic initial cell. -/
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
    (hK : ∀ k, IsStoppingTime (𝓖 k)
      (fun ω => (K k ω : WithTop ℕ)))
    (N : ℕ → ℕ) (hN : ∀ k ω, K k ω ≤ N k) :
    ∀ k,
      (∫ ω, stoppedValue (fun i : ℕ => f (e k i))
        (fun ω => (K k ω : WithTop ℕ)) ω ∂P) =
      (∫ ω, stoppedValue (fun i : ℕ => f (e k i))
        (fun _ : Ω => (0 : WithTop ℕ)) ω ∂P) := by
  intro k
  letI : SigmaFiniteFiltration P (𝓖 k) := hSF k
  have hZero : IsStoppingTime (𝓖 k)
      (fun _ : Ω => (0 : WithTop ℕ)) := by
    intro i
    simp
  have hle : (fun _ : Ω => (0 : WithTop ℕ)) ≤
      (fun ω => (K k ω : WithTop ℕ)) := by
    intro ω
    exact zero_le
  have hbdd : ∀ ω, (K k ω : WithTop ℕ) ≤
      (N k : WithTop ℕ) := by
    intro ω
    exact_mod_cast hN k ω
  symm
  exact chat01_monotone_sampling_bounded_optional_stopping_eq
    (𝓕 := 𝓕.rightCont) (μ := P) (f := f)
    (e k) (he k) hf (𝓖 k) (h𝓖 k)
    (fun _ : Ω => (0 : WithTop ℕ))
    (fun ω => (K k ω : WithTop ℕ))
    hZero (hK k) hle (N k) hbdd
