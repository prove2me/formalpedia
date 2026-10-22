-- Prove2me | solution 1 for BootRobust.Optimality.N_subset_disapp
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:09:34.194052+00:00
-- url     : https://prove2.me/submissions/56634405-5b7f-42e3-8931-1e2a76414d86

import Mathlib
import Definitions.Def_BootRobust_Optimality_Setting

set_option autoImplicit false
open BootRobust.Optimality

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : (ι → ℝ) → (ι → ℝ) → EReal) (Dtr : ι → ℝ) (r : ℝ)
    (N : Set (ι → ℝ)) (hN : relOpen N) (G : ι → ℝ) (a : ℝ)
    (hball : ∀ D ∈ stdSimplex ℝ ι, R D Dtr ≤ (r : EReal) → ∑ i, D i * G i ≤ a)
    (hNsep : ∀ D' ∈ N, a < ∑ i, D' i * G i) :
    relInt N = N ∧ N ⊆ linDisapp R Dtr r G := by
  obtain ⟨U, hU, rfl⟩ := hN
  refine ⟨?_, ?_⟩
  · ext D
    constructor
    · rintro ⟨hDs, V, -, hDV, hVsub⟩
      exact hVsub ⟨hDV, hDs⟩
    · rintro ⟨hDU, hDs⟩
      exact ⟨hDs, U, hU, hDU, subset_rfl⟩
  · intro D hD
    refine ⟨hD.2, ?_⟩
    calc (⨆ D' ∈ {D' : ι → ℝ | D' ∈ stdSimplex ℝ ι ∧ R D' Dtr ≤ (r : EReal)},
          ((∑ i, D' i * G i : ℝ) : EReal)) ≤ (a : EReal) :=
          iSup₂_le fun D' hD' => EReal.coe_le_coe_iff.mpr (hball D' hD'.1 hD'.2)
      _ < ((∑ i, D i * G i : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr (hNsep D hD)
