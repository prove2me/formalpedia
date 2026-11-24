-- Prove2me | solution 1 for Formalism.L2.NG.exists_level_elt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:19:54.980804+00:00
-- url     : https://prove2.me/submissions/bfb2b59e-2317-4104-99a4-19b6d1bc3657

import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsLab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.L2 Formalism.L2.NG
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {p : ℕ} [Fact p.Prime]
namespace Formalism.L2.NG
theorem _root_.solution (x : Formalism.CyclotomicNorms.Fbar p) (hx : x ≠ 0) : ∃ d, 0 < d ∧ x ^ (p ^ d - 1) = 1 := by
  have hint : IsIntegral (ZMod p) x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let K := IntermediateField.adjoin (ZMod p) {x}
  have : FiniteDimensional (ZMod p) K := IntermediateField.adjoin.finiteDimensional hint
  have : Finite K := Module.finite_of_finite (ZMod p)
  have : Fintype K := Fintype.ofFinite K
  have hxK : x ∈ K := IntermediateField.mem_adjoin_simple_self (ZMod p) x
  obtain ⟨d, _, hd⟩ := FiniteField.card K p
  refine ⟨d, d.pos, ?_⟩
  have h0 : (⟨x, hxK⟩ : K) ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have h1 := FiniteField.pow_card_sub_one_eq_one (⟨x, hxK⟩ : K) h0
  rw [hd] at h1
  exact congrArg Subtype.val h1
end Formalism.L2.NG
