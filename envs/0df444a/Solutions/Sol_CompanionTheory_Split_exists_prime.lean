-- Prove2me | solution 1 for CompanionTheory.Split.exists_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:30:16.420737+00:00
-- url     : https://prove2.me/submissions/0db0ee26-fe95-4a99-89fb-3f85b5d13328

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_ExistsDenFin
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut TensorProduct Formalism.UG Formalism.L2
noncomputable section
open CompanionTheory CompanionTheory.Split
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => maximalRealSubfield L
variable (s : SplitPlace L)
namespace CompanionTheory.Split
theorem _root_.solution : ∃ p : ℕ, p.Prime ∧ s.Above p ∧ ∃ f : ℕ, s.q = p ^ f := by
  have := s.v.isMaximal
  let _ : Field (𝓞 L⁺ ⧸ s.v.asIdeal) := Ideal.Quotient.field _
  have : Finite (𝓞 L⁺ ⧸ s.v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ s.v.ne_bot
  let _ : Fintype (𝓞 L⁺ ⧸ s.v.asIdeal) := Fintype.ofFinite _
  obtain ⟨p, hp, f, hpp, hf⟩ := FiniteField.card' (𝓞 L⁺ ⧸ s.v.asIdeal)
  refine ⟨p, hpp, Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_natCast, CharP.cast_eq_zero]), f, ?_⟩
  rw [SplitPlace.q, Nat.card_eq_fintype_card, hf]
end CompanionTheory.Split
