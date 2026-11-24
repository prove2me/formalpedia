-- Prove2me | solution 1 for Formalism.HC.Der.exists_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:57:17.200774+00:00
-- url     : https://prove2.me/submissions/a8c26bbd-6da5-4333-a360-691f9a924d54

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Theorems.Thm_Formalism_HC_Der_inertia_res
import Theorems.Thm_Formalism_HC_Der_frob_res
import Theorems.Thm_Formalism_HC_Der_inertia_lift

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
namespace Formalism.HC.Der
theorem _root_.solution {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [IsGalois ℚ L] (ι : E →ₐ[ℚ] L)
    (l : ℕ) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] :
    ∃ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver (span {(l : ℤ)})),
      (∀ (σ : E ≃ₐ[ℚ] E), (∀ x : 𝓞 E, σ • x - x ∈ P) ↔
        ∃ τ : L ≃ₐ[ℚ] L, (∀ x, ι (σ x) = τ (ι x)) ∧ ∀ y : 𝓞 L, τ • y - y ∈ Q) ∧
      ∀ (σ : E ≃ₐ[ℚ] E) (τ : L ≃ₐ[ℚ] L), (∀ x, ι (σ x) = τ (ι x)) → IsArithFrobAt ℤ τ Q → IsArithFrobAt ℤ σ P := by
  let _ : Algebra E L := ι.toRingHom.toAlgebra
  have : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
  have hQ : Q.LiesOver (span {(l : ℤ)}) := Ideal.LiesOver.trans Q P (span {(l : ℤ)})
  exact ⟨Q, hQp, hQ, fun σ => ⟨inertia_lift P Q σ, fun ⟨τ, h1, h2⟩ => inertia_res P Q σ τ h1 h2⟩,
    fun σ τ h1 h2 => frob_res l P Q σ τ h1 h2⟩
end Formalism.HC.Der
