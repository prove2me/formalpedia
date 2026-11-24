-- Prove2me | solution 1 for Formalism.HC.Der.frob_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:41:17.632476+00:00
-- url     : https://prove2.me/submissions/c7cf6ab3-e777-40d6-8099-faa0efda492a

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Theorems.Thm_Formalism_HC_Der_res_smul
import Theorems.Thm_Formalism_HC_Der_mem_over_iff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_card_under


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsScalarTower ℚ E L]
omit [IsScalarTower ℚ E L]
namespace Formalism.HC.Der
theorem _root_.solution (p : ℕ) (P : Ideal (𝓞 E)) (Q : Ideal (𝓞 L)) [Q.LiesOver P] [Q.LiesOver (span {(p : ℤ)})]
    [P.LiesOver (span {(p : ℤ)})] (σ : E ≃ₐ[ℚ] E) (τ : L ≃ₐ[ℚ] L)
    (h : ∀ x, algebraMap E L (σ x) = τ (algebraMap E L x)) (hτ : IsArithFrobAt ℤ τ Q) : IsArithFrobAt ℤ σ P := by
  intro x
  have hx : τ • algebraMap (𝓞 E) (𝓞 L) x - algebraMap (𝓞 E) (𝓞 L) x ^ Nat.card (ℤ ⧸ Q.under ℤ) ∈ Q :=
    hτ (algebraMap (𝓞 E) (𝓞 L) x)
  show σ • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P
  rw [odd_card_under p Q] at hx
  rw [odd_card_under p P, mem_over_iff P Q, map_sub, map_pow, res_smul σ τ h]
  exact hx
end Formalism.HC.Der
