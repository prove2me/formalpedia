-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_grid_band_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:19:00.515732+00:00
-- url     : https://prove2.me/submissions/ff8a5e7d-83d1-4598-9bb6-e2ce1be70cd9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_countable_exterior_observation_inf_stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (H : ℝ≥0) (δ R : ℕ → ℝ)
    (hδ : Antitone δ) (hR : Monotone R)
    (r : ℕ → ℝ≥0) (hr : DenseRange r) :
    let Y : ℝ≥0 → Ω → ℝ := fun t ω => x + X.X t ω - rightLimit D t ω
    let E : ℕ → Ω → ℕ → ℝ≥0 := fun k ω j =>
      if Y (r j) ω < δ k ∨ R k < Y (r j) ω then min (r j) H else H
    let θ : ℕ → Ω → ℝ≥0 := fun k ω => ⨅ j, E k ω j
    ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (θ k ω : WithTop ℝ≥0)) := by 
  dsimp only
  let Y : ℝ≥0 → Ω → ℝ := fun t ω => x + X.X t ω - rightLimit D t ω
  let E : ℕ → Ω → ℕ → ℝ≥0 := fun k ω j =>
    if Y (r j) ω < δ k ∨ R k < Y (r j) ω then min (r j) H else H
  let θ : ℕ → Ω → ℝ≥0 := fun k ω => ⨅ j, E k ω j
  intro k
  let S : Ω → WithTop ℝ≥0 := fun ω => ⨅ j,
    if Y (r j) ω < δ k ∨ R k < Y (r j) ω then (r j : WithTop ℝ≥0) else ⊤
  have hS : IsStoppingTime 𝓕.rightCont S :=
    avram_wave7_18_original_countable_exterior_observation_inf_stopping
      X x D hD r (δ k) (R k)
  have heq : (fun ω => (θ k ω : WithTop ℝ≥0)) =
      (fun ω => min (S ω) (H : WithTop ℝ≥0)) := by
    funext ω
    change ((⨅ j, E k ω j : ℝ≥0) : WithTop ℝ≥0) = _
    rw [WithTop.coe_iInf (OrderBot.bddBelow _)]
    let A : ℕ → WithTop ℝ≥0 := fun j =>
      if Y (r j) ω < δ k ∨ R k < Y (r j) ω then (r j : WithTop ℝ≥0) else ⊤
    have hE (j : ℕ) : (E k ω j : WithTop ℝ≥0) = A j ⊓ (H : WithTop ℝ≥0) := by
      change ((if Y (r j) ω < δ k ∨ R k < Y (r j) ω then min (r j) H else H : ℝ≥0) : WithTop ℝ≥0) = (if Y (r j) ω < δ k ∨ R k < Y (r j) ω then (r j : WithTop ℝ≥0) else ⊤) ⊓ (H : WithTop ℝ≥0)
      split
      · exact WithTop.coe_min _ _
      · exact (top_inf_eq _).symm
    simp_rw [hE, iInf_inf_eq, iInf_const]
    rfl
  rw [heq]
  exact hS.min_const H
