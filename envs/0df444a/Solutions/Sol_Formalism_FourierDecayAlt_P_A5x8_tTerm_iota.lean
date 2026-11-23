-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.tTerm_iota
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:21.638959+00:00
-- url     : https://prove2.me/submissions/8505dc8b-6899-4440-be78-cd232d6c78de

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_card_iso_big
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iA_spec
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iC_spec
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iA_eZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iC_mu
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_bigZ_int_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_tTerm_mk
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_psiKR_mk
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K]
open Classical
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (R : Subring K) (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) {m m' N N' : ℕ}
    (hN : N = m + 1) (hN' : N' = m' + 1) (Z₁ : Matrix (Fin m) (Fin m) K)
    (Z₂ : Matrix (Fin m') (Fin m') K) (c : Kˣ) (h₁ : IsInt R Z₁) (h₂ : IsInt R Z₂)
    (d₁ : IsUnit Z₁.det) (d₂ : IsUnit Z₂.det)
    (s : ((coker R Z₁ →ₗ[R] KR R) × coker R Z₁) × ((coker R Z₂ →ₗ[R] KR R) × coker R Z₂)) :
    tTerm R ψ hN hN' Z₁ Z₂ (c : K) (iota R Z₁ Z₂ s) =
      (if s.1.1 s.1.2 = -(Submodule.Quotient.mk (c : K) : KR R) ∧
          s.2.1 s.2.2 = -(Submodule.Quotient.mk (c : K) : KR R) then
        (Nat.card {θ : coker R Z₁ ≃ₗ[R] coker R Z₂ //
          (∀ y, s.2.1 (θ y) = s.1.1 y) ∧ θ s.1.2 = s.2.2} : ℂ) else 0) *
      psiKR R ψ (s.1.1 (eZ R Z₁) + A5x6.muZ R Z₁ d₁ s.1.2) *
      conj (psiKR R ψ (s.2.1 (eZ R Z₂) + A5x6.muZ R Z₂ d₂ s.2.2)) := by
  obtain ⟨⟨a, b⟩, ⟨a', b'⟩⟩ := s
  rw [show iota R Z₁ Z₂ ((a, b), (a', b')) =
    ((iA R Z₁ a, iC R Z₁ b), (iA R Z₂ a', iC R Z₂ b')) from rfl, tTerm_mk]
  simp only
  rw [iA_eZ, iA_eZ, iC_mu R Z₁ h₁ d₁, iC_mu R Z₂ h₂ d₂, ← Submodule.Quotient.mk_add,
    ← Submodule.Quotient.mk_add, A5x6.psiKR_mk R ψ hψ, A5x6.psiKR_mk R ψ hψ]
  congr 2
  by_cases hI : a b = -(Submodule.Quotient.mk (c : K) : KR R) ∧
      a' b' = -(Submodule.Quotient.mk (c : K) : KR R)
  · have hI1 := (bigZ_int_iff R hN Z₁ h₁ d₁ a b (c : K)).2 hI.1
    have hI2 := (bigZ_int_iff R hN' Z₂ h₂ d₂ a' b' (c : K)).2 hI.2
    rw [if_pos hI, if_pos ⟨hI1, hI2⟩]
    obtain ⟨v, hv, hb⟩ := iC_spec R Z₁ h₁ d₁ b
    obtain ⟨v', hv', hb'⟩ := iC_spec R Z₂ h₂ d₂ b'
    rw [card_iso_big R hN hN' Z₁ Z₂ d₁ d₂ _ _ _ _ c hI1 hI2 a a' (iA_spec R Z₁ a)
      (iA_spec R Z₂ a') v v' hv hv', hb, hb']
  · rw [if_neg hI, if_neg]
    rintro ⟨hI1, hI2⟩
    exact hI ⟨(bigZ_int_iff R hN Z₁ h₁ d₁ a b (c : K)).1 hI1,
      (bigZ_int_iff R hN' Z₂ h₂ d₂ a' b' (c : K)).1 hI2⟩
end Formalism.FourierDecayAlt.P.A5x8
