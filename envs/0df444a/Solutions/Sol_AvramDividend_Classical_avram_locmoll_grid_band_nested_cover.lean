-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_grid_band_nested_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:15:44.852071+00:00
-- url     : https://prove2.me/submissions/c7942997-45db-4dc4-ba3a-139afcfea552

import Mathlib
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
    (∀ ω, Monotone (fun k => θ k ω)) ∧
    (∀ k ω t, t ≤ H → (∀ s : ℝ≥0, s ≤ t → Y s ω ∈ Icc (δ k) (R k)) →
      t ≤ θ k ω) := by 
  dsimp only
  let Y : ℝ≥0 → Ω → ℝ := fun t ω => x + X.X t ω - rightLimit D t ω
  let E : ℕ → Ω → ℕ → ℝ≥0 := fun k ω j =>
    if Y (r j) ω < δ k ∨ R k < Y (r j) ω then min (r j) H else H
  let θ : ℕ → Ω → ℝ≥0 := fun k ω => ⨅ j, E k ω j
  have hθ (k : ℕ) (ω : Ω) (j : ℕ) : θ k ω ≤ E k ω j :=
    ciInf_le (OrderBot.bddBelow _) j
  constructor
  · intro ω i j hij
    change θ i ω ≤ θ j ω
    apply le_ciInf
    intro n
    refine (hθ i ω n).trans ?_
    change E i ω n ≤ E j ω n
    unfold E
    by_cases he : Y (r n) ω < δ j ∨ R j < Y (r n) ω
    · have he' : Y (r n) ω < δ i ∨ R i < Y (r n) ω :=
        he.elim (fun h => Or.inl (h.trans_le (hδ hij)))
          (fun h => Or.inr ((hR hij).trans_lt h))
      simp [he, he']
    · simp only [if_neg he]
      split <;> simp
  · intro k ω t ht hb
    change t ≤ θ k ω
    apply le_ciInf
    intro j
    change t ≤ E k ω j
    unfold E
    split
    · rename_i he
      refine le_min ?_ ht
      by_contra hh
      have hs := hb (r j) (le_of_lt (lt_of_not_ge hh))
      exact he.elim (fun h => (not_lt_of_ge hs.1) h)
        (fun h => (not_lt_of_ge hs.2) h)
    · exact ht

