-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x4.isoCount
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:53.940025+00:00
-- url     : https://prove2.me/submissions/cecf8e83-48e1-4dd2-ba0e-8edc8f0a86ae

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_card_isoSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_card_isoZZ
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x4
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x4
theorem _root_.solution {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (Z' : Matrix (Fin n') (Fin n') K) (ι : Type) [Fintype ι] (C : ι → Type)
    [∀ a, AddCommGroup (C a)] [∀ a, Module R (C a)] (e : ∀ a, C a) (lam : ∀ a, C a →ₗ[R] KR R)
    (hne : ∀ a b, a ≠ b → ¬ ∃ φ : C a ≃ₗ[R] C b, φ (e a) = e b ∧ ∀ c, lam b (φ c) = lam a c)
    (hex : ∃ a, (isoSet R Z (C a) (e a) (lam a)).Nonempty) :
    ∑ a, (Nat.card (isoSet R Z (C a) (e a) (lam a)) : ℂ) *
        (Nat.card (isoSet R Z' (C a) (e a) (lam a)) : ℂ) /
        (Nat.card (autSet R (C a) (e a) (lam a)) : ℂ) = (Nat.card (isoZZ R Z Z') : ℂ) := by
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
end Formalism.FourierDecayAlt.P.A5x4
