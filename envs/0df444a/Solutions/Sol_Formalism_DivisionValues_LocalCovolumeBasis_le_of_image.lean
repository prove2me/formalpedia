-- Prove2me | solution 1 for Formalism.DivisionValues.LocalCovolumeBasis.le_of_image
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:58.191305+00:00
-- url     : https://prove2.me/submissions/af4f464c-5923-4945-98f4-8a690f5b8b75

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.DivisionValues Formalism.DivisionValues.LocalCovolumeBasis
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
namespace Formalism.DivisionValues.LocalCovolumeBasis
theorem _root_.solution {A N M1 M2 : Submodule (𝓞 K) V} (hN2 : N ≤ M2) (h1A : M1 ≤ A)
    (himg : (N.comap A.subtype).mkQ '' (A.subtype ⁻¹' (M1 : Set V)) =
      (N.comap A.subtype).mkQ '' (A.subtype ⁻¹' (M2 : Set V))) : M1 ≤ M2 := by
  intro x hx
  have hmem : (N.comap A.subtype).mkQ ⟨x, h1A hx⟩ ∈
      (N.comap A.subtype).mkQ '' (A.subtype ⁻¹' (M1 : Set V)) := ⟨⟨x, h1A hx⟩, hx, rfl⟩
  rw [himg] at hmem
  obtain ⟨z, hz, hzx⟩ := hmem
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hzx
  have h1 : ((z : V) - x) ∈ M2 := hN2 hzx
  have h2 : (z : V) ∈ M2 := hz
  have : x = (z : V) - ((z : V) - x) := by abel
  rw [this]
  exact M2.sub_mem h2 h1
end Formalism.DivisionValues.LocalCovolumeBasis
