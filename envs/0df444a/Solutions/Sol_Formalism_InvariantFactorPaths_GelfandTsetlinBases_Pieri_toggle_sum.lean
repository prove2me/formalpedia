-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.toggle_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:11:48.674392+00:00
-- url     : https://prove2.me/submissions/62edabb4-d8bf-4b9d-9838-095f528e2e53

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_mem_stripsUp
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_cond_up
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_cond_low
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_sum_fw
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_sum_bw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
theorem _root_.solution {n : ℕ} (μ : Fin (n + 1) → ℤ) (b : ℕ) (f : (Fin n → ℤ) → ℕ) :
    ∑ ν ∈ stripsUp μ b, ∑ l ∈ gtBox ν, f l = ∑ κ ∈ gtBox μ, ∑ l ∈ sLe κ b, f l := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun x : (Σ _ : Fin (n + 1) → ℤ, Fin n → ℤ) => (⟨fw μ x.2 x.1, x.2⟩ : Σ _ : Fin n → ℤ, Fin n → ℤ))
    (fun y : (Σ _ : Fin n → ℤ, Fin n → ℤ) => (⟨bw μ y.2 b y.1, y.2⟩ : Σ _ : Fin (n + 1) → ℤ, Fin n → ℤ))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨ν, l⟩ h
    simp only [Finset.mem_sigma, mem_stripsUp] at h
    rw [cond_up] at h
    simp only [Finset.mem_sigma]
    rw [cond_low]
    obtain ⟨h1, h2, h3⟩ := h
    have hs := sum_fw μ ν l
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · simp only [fw]; linarith [h2 i]
    · simp only [fw]; linarith [h1 i.succ]
    · have := h1 0; linarith
  · rintro ⟨κ, l⟩ h
    simp only [Finset.mem_sigma] at h
    rw [cond_low] at h
    simp only [Finset.mem_sigma]
    rw [mem_stripsUp, cond_up]
    obtain ⟨h1, h2, h3⟩ := h
    have hs := sum_bw μ κ l b
    refine ⟨fun j => ?_, fun i => ?_, by linarith⟩
    · refine Fin.cases ?_ (fun i => ?_) j
      · simp only [bw, Fin.cons_zero]; linarith
      · simp only [bw, Fin.cons_succ]; linarith [h2 i]
    · simp only [bw, Fin.cons_succ]; linarith [h1 i]
  · rintro ⟨ν, l⟩ h
    simp only [Finset.mem_sigma, mem_stripsUp] at h
    have h3 : ∑ m, ν m - ∑ m, μ m = (b : ℤ) := by
      have h' := h.1
      unfold HStrip at h'
      exact h'.2.2
    have hs := sum_fw μ ν l
    show (⟨bw μ l b (fw μ l ν), l⟩ : Σ _ : Fin (n + 1) → ℤ, Fin n → ℤ) = ⟨ν, l⟩
    congr 1
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [bw, Fin.cons_zero]; linarith
    · simp only [bw, Fin.cons_succ, fw]; ring
  · rintro ⟨κ, l⟩ _
    show (⟨fw μ l (bw μ l b κ), l⟩ : Σ _ : Fin n → ℤ, Fin n → ℤ) = ⟨κ, l⟩
    congr 1
    funext i
    simp only [fw, bw, Fin.cons_succ]
    ring
  · intro x _
    rfl
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
