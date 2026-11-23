-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x3.sum_over_S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:25.065068+00:00
-- url     : https://prove2.me/submissions/463b22f2-c6af-4dfd-a989-84092bdd1bdf

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_psiBar_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_eq_zero_of_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_finsum_char
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_finite_dual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_chS_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x3
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)
variable {R ψ}
variable {C : Type} [AddCommGroup C] [Module R C]
open Classical
namespace Formalism.FourierDecayAlt.P.A5x3
theorem _root_.solution (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) [Finite C]
    (S : Submodule R (C →ₗ[R] KR R)) (c : C) :
    ∑ᶠ α : S, psiKR R ψ ((α : C →ₗ[R] KR R) c) =
      if ∀ α ∈ S, α c = 0 then (Nat.card S : ℂ) else 0 := by
  have := finite_dual (C := C) h
  split_ifs with hc
  · apply (finsum_char (chS h S c)).1
    intro α
    rw [chS_apply, hc α α.2, ← psiBar_apply h, AddChar.map_zero_eq_one]
  · apply (finsum_char (chS h S c)).2
    by_contra hcon
    push Not at hcon
    apply hc
    intro α hα
    apply eq_zero_of_psi h
    intro r
    have := hcon ⟨r • α, S.smul_mem r hα⟩
    rw [chS_apply] at this
    exact this
end Formalism.FourierDecayAlt.P.A5x3
