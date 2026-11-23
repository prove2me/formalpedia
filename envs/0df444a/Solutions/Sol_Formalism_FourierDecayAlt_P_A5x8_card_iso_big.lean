-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.card_iso_big
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:00.844047+00:00
-- url     : https://prove2.me/submissions/d4c1f087-12a2-4893-954e-2d26cdc4d56c

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_blkM_isInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_card
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_top_vec
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_eLast
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_piS_mk
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_piB_mk
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_datB
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_datS
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_muZ_mk
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
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution {K : Type} [CommRing K] (R : Subring K)
    {m m' N N' : ℕ} (hN : N = m + 1) (hN' : N' = m' + 1)
    (Z₁ : Matrix (Fin m) (Fin m) K) (Z₂ : Matrix (Fin m') (Fin m') K)
    (hZ₁ : IsUnit Z₁.det) (hZ₂ : IsUnit Z₂.det) (ξ₁ η₁ : Fin m → K) (ξ₂ η₂ : Fin m' → K) (c : Kˣ)
    (hi₁ : IsInt R (bigZ hN Z₁ ξ₁ η₁ (c : K))) (hi₂ : IsInt R (bigZ hN' Z₂ ξ₂ η₂ (c : K)))
    (α₁ : coker R Z₁ →ₗ[R] KR R) (α₂ : coker R Z₂ →ₗ[R] KR R)
    (hα₁ : ∀ v, α₁ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ξ₁ ⬝ᵥ coeLin R v))
    (hα₂ : ∀ v, α₂ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ξ₂ ⬝ᵥ coeLin R v))
    (b₁ : Fin m → R) (b₂ : Fin m' → R) (hb₁ : coeLin R b₁ = Z₁ *ᵥ η₁)
    (hb₂ : coeLin R b₂ = Z₂ *ᵥ η₂) :
    Nat.card (isoZZ R (bigZ hN Z₁ ξ₁ η₁ (c : K)) (bigZ hN' Z₂ ξ₂ η₂ (c : K))) =
      Nat.card {θ : coker R Z₁ ≃ₗ[R] coker R Z₂ // (∀ y, α₂ (θ y) = α₁ y) ∧
        θ (Submodule.Quotient.mk b₁) = Submodule.Quotient.mk b₂} := by
  obtain ⟨-, -, hξ₁, hs₁⟩ := (blkM_isInt R hN _ _ _ _).1 hi₁
  obtain ⟨-, -, hξ₂, hs₂⟩ := (blkM_isInt R hN' _ _ _ _).1 hi₂
  have DB₁ := iso_datB R hN Z₁ hZ₁ ξ₁ η₁ c b₁ hb₁ ⟨_, hs₁⟩ rfl
  have DB₂ := iso_datB R hN' Z₂ hZ₂ ξ₂ η₂ c b₂ hb₂ ⟨_, hs₂⟩ rfl
  have DS₁ := iso_datS R hN Z₁ ξ₁ hξ₁ α₁ hα₁
  have DS₂ := iso_datS R hN' Z₂ ξ₂ hξ₂ α₂ hα₂
  have e1 := iso_card DB₂ DB₁ (Submodule.Quotient.mk (iso_vec hN 0 1))
    (Submodule.Quotient.mk (iso_vec hN' 0 1)) (by rw [DS₁.Pg, DS₂.Pg])
  have e2 := iso_card DS₂ DS₁ (Submodule.Quotient.mk (iso_vec hN b₁ ⟨_, hs₁⟩))
    (Submodule.Quotient.mk (iso_vec hN' b₂ ⟨_, hs₂⟩)) (by rw [DB₁.Pg, DB₂.Pg])
  have l1 : Nat.card (isoZZ R (bigZ hN Z₁ ξ₁ η₁ (c : K)) (bigZ hN' Z₂ ξ₂ η₂ (c : K))) =
      Nat.card {φ : coker R (bigZ hN Z₁ ξ₁ η₁ (c : K)) ≃ₗ[R] coker R (bigZ hN' Z₂ ξ₂ η₂ (c : K)) //
        (∀ y, A5x6.muZ R (bigZ hN' Z₂ ξ₂ η₂ (c : K)) (iso_bigZ_det hN' Z₂ hZ₂ ξ₂ η₂ c) (φ y) =
          A5x6.muZ R (bigZ hN Z₁ ξ₁ η₁ (c : K)) (iso_bigZ_det hN Z₁ hZ₁ ξ₁ η₁ c) y) ∧
        φ (iso_piB R hN Z₁ ξ₁ η₁ (c : K) (Submodule.Quotient.mk (iso_vec hN 0 1))) =
          iso_piB R hN' Z₂ ξ₂ η₂ (c : K) (Submodule.Quotient.mk (iso_vec hN' 0 1))} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun φ => ?_)
    rw [iso_piB_mk, iso_piB_mk, ← iso_eLast, ← iso_eLast]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun y => ?_, h1⟩
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨v', hv'⟩ := Submodule.Quotient.mk_surjective _ (φ (Submodule.Quotient.mk v))
      rw [← hv', A5x6.muZ_mk, A5x6.muZ_mk]
      exact h2 v v' hv'.symm
    · rintro ⟨h1, h2⟩
      refine ⟨h2, fun v v' hv => ?_⟩
      have := h1 (Submodule.Quotient.mk v)
      rwa [hv, A5x6.muZ_mk, A5x6.muZ_mk] at this
  have l2 : Nat.card {θ : coker R Z₁ ≃ₗ[R] coker R Z₂ // (∀ y, α₂ (θ y) = α₁ y) ∧
        θ (Submodule.Quotient.mk b₁) = Submodule.Quotient.mk b₂} =
      Nat.card {θ : coker R Z₁ ≃ₗ[R] coker R Z₂ // (∀ y, (-α₂) (θ y) = (-α₁) y) ∧
        θ (iso_piS R hN Z₁ ξ₁ (Submodule.Quotient.mk (iso_vec hN b₁ ⟨_, hs₁⟩))) =
          iso_piS R hN' Z₂ ξ₂ (Submodule.Quotient.mk (iso_vec hN' b₂ ⟨_, hs₂⟩))} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun θ => ?_)
    rw [iso_piS_mk, iso_piS_mk, iso_top_vec, iso_top_vec]
    simp only [LinearMap.neg_apply, neg_inj]
  rw [l1, l2, e1, e2]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun Ψ => ?_)
  tauto
end Formalism.FourierDecayAlt.P.A5x8
