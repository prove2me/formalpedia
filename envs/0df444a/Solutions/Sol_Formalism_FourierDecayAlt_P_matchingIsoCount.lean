-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.matchingIsoCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:44:30.456948+00:00
-- url     : https://prove2.me/submissions/2d6798bf-8d38-4b00-a63f-973e116f7ba7

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TripleForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x1_card_isoSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x1_card_isoZZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.IsoCount := by
  intro K _ R n n' Z Z' ι _ C _ _ e lam hne hex
  obtain ⟨a0, φ0, hφ0⟩ := hex
  classical
  have hzero : ∀ b, b ≠ a0 → IsEmpty (isoSet R Z (C b) (e b) (lam b)) := by
    intro b hb
    refine ⟨fun ⟨φ1, h1⟩ => hne b a0 hb ⟨φ1.symm.trans φ0, ?_, ?_⟩⟩
    · have : φ1.symm (e b) = eZ R Z := by rw [← h1.1]; simp
      simp [this, hφ0.1]
    · intro c
      obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (φ1.symm c)
      have h3 : φ1 (Submodule.Quotient.mk v) = c := by rw [hv]; simp
      simp only [LinearEquiv.trans_apply]
      rw [← hv, hφ0.2 v, ← h1.2 v, h3]
  rw [Finset.sum_eq_single a0 (fun b _ hb => by have := hzero b hb; simp) (by simp)]
  rw [card_isoSet R Z _ _ _ φ0 hφ0, ← card_isoZZ R Z Z' _ _ _ φ0 hφ0]
  by_cases hN : Nat.card (autSet R (C a0) (e a0) (lam a0)) = 0
  · have hM : Nat.card (isoSet R Z' (C a0) (e a0) (lam a0)) = 0 := by
      by_cases hE : (isoSet R Z' (C a0) (e a0) (lam a0)).Nonempty
      · obtain ⟨ρ, hρ⟩ := hE
        rw [card_isoSet R Z' _ _ _ ρ hρ, hN]
      · rw [Set.not_nonempty_iff_eq_empty] at hE
        rw [hE]; simp
    simp [hN, hM]
  · have : (Nat.card (autSet R (C a0) (e a0) (lam a0)) : ℂ) ≠ 0 := by exact_mod_cast hN
    field_simp
end Formalism.FourierDecayAlt.P
