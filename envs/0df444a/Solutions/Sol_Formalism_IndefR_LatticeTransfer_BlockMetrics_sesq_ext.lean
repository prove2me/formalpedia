-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.BlockMetrics.sesq_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:20.710854+00:00
-- url     : https://prove2.me/submissions/0e4340a7-e7c8-4863-8149-9b36508466e0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_OpNormAtLeOfPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open Formalism.IndefR.LatticeTransfer.BlockMetrics
namespace Formalism.IndefR.LatticeTransfer.BlockMetrics
theorem _root_.solution {K V : Type} [Field K] [AddCommGroup V] [Module K V] {F G : V → V → ℂ}
    {σ : K →+* ℂ} (hσ : ∃ a : K, (σ a).im ≠ 0)
    (hF : (∀ x x' y, F (x + x') y = F x y + F x' y) ∧ (∀ x y y', F x (y + y') = F x y + F x y') ∧
      (∀ (a : K) x y, F (a • x) y = starRingEnd ℂ (σ a) * F x y) ∧
      (∀ (a : K) x y, F x (a • y) = σ a * F x y))
    (hG : (∀ x x' y, G (x + x') y = G x y + G x' y) ∧ (∀ x y y', G x (y + y') = G x y + G x y') ∧
      (∀ (a : K) x y, G (a • x) y = starRingEnd ℂ (σ a) * G x y) ∧
      (∀ (a : K) x y, G x (a • y) = σ a * G x y))
    (h : ∀ x, F x x = G x x) (x y : V) : F x y = G x y := by
  obtain ⟨a, ha⟩ := hσ
  obtain ⟨F1, F2, F3, F4⟩ := hF
  obtain ⟨G1, G2, G3, G4⟩ := hG
  have e1 := h (x + y)
  have e2 := h (a • x + y)
  simp only [F1, F2, F3, F4, G1, G2, G3, G4] at e1 e2
  rw [h x, h y] at e1 e2
  have hne : starRingEnd ℂ (σ a) - σ a ≠ 0 := by
    intro h0
    apply ha
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have key : (starRingEnd ℂ (σ a) - σ a) * (F x y - G x y) = 0 := by
    linear_combination e2 - σ a * e1
  rcases mul_eq_zero.1 key with h0 | h0
  · exact absurd h0 hne
  · exact sub_eq_zero.1 h0
end Formalism.IndefR.LatticeTransfer.BlockMetrics
