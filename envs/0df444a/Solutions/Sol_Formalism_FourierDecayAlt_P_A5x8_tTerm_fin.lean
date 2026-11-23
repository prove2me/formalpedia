-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.tTerm_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:36.375588+00:00
-- url     : https://prove2.me/submissions/b5002b00-a5e1-4689-ab72-e0cc7491bcfa

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_tTerm_supp
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_tTerm_zero
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_finite_coker
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_finite_dual
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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (R : Subring K) (ψ : AddChar K ℂ) (hD : LocalDatum K R ψ) {m m' N N' : ℕ}
    (hN : N = m + 1) (hN' : N' = m' + 1) (Z₁ : Matrix (Fin m) (Fin m) K)
    (Z₂ : Matrix (Fin m') (Fin m') K) (c : K) (d₁ : IsUnit Z₁.det) (d₂ : IsUnit Z₂.det) :
    (Function.support (tTerm R ψ hN hN' Z₁ Z₂ c)).Finite := by
  by_cases hI : IsInt R Z₁ ∧ IsInt R Z₂
  · have := A5x3.finite_coker hD Z₁ hI.1 d₁
    have := A5x3.finite_coker hD Z₂ hI.2 d₂
    have : Finite (coker R Z₁ →ₗ[R] KR R) := A5x3.finite_dual hD.selfDual
    have : Finite (coker R Z₂ →ₗ[R] KR R) := A5x3.finite_dual hD.selfDual
    exact (Set.finite_range (iota R Z₁ Z₂)).subset (tTerm_supp R ψ hN hN' Z₁ Z₂ c d₁ d₂)
  · have : Function.support (tTerm R ψ hN hN' Z₁ Z₂ c) = ∅ := by
      ext y
      simp [tTerm_zero R ψ hN hN' Z₁ Z₂ c hI y]
    rw [this]
    exact Set.finite_empty
end Formalism.FourierDecayAlt.P.A5x8
