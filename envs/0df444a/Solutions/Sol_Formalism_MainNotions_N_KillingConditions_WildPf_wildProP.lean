-- Prove2me | solution 1 for Formalism.MainNotions.N.KillingConditions.WildPf.wildProP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:17:48.227827+00:00
-- url     : https://prove2.me/submissions/d46a81f1-c174-4dfa-a2a7-f80ab4a41690

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightVersion_Imports
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_WildPro
import Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_exists_ppow_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KillingConditions Formalism.MainNotions.N.KillingConditions.WildPf
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
variable {A}
namespace Formalism.MainNotions.N.KillingConditions.WildPf
theorem _root_.solution (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] : Formalism.MainNotions.N.KillingConditions.WildProP E Ω := by
  intro A p hp hpA σ hσ N hN
  have hnh : (N : Set (Ω ≃ₐ[E] Ω)) ∈ nhds (1 : Ω ≃ₐ[E] Ω) := hN.mem_nhds N.one_mem
  obtain ⟨L, hL, hLN⟩ := (krullTopology_mem_nhds_one_iff E Ω _).1 hnh
  obtain ⟨S, hS⟩ := (Module.finite_def.1 hL : (⊤ : Submodule E L).FG)
  have hint : ∀ s : L, IsIntegral E (s : Ω) := fun s =>
    (isIntegral_algebraMap_iff (algebraMap L Ω).injective).2 (Algebra.IsIntegral.isIntegral s)
  choose a ha using fun s : L => exists_ppow_fix hp hpA (σ := σ) hσ (s : Ω) (hint s)
  refine ⟨S.sup a, hLN ?_⟩
  show σ ^ (p ^ S.sup a) ∈ L.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hx' : (⟨x, hx⟩ : L) ∈ Submodule.span E (S : Set L) := by rw [hS]; trivial
  have key : ∀ u : L, u ∈ Submodule.span E (S : Set L) → (σ ^ (p ^ S.sup a)) (u : Ω) = (u : Ω) := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem s hs => exact ha s _ (Finset.le_sup hs)
    | zero => simp
    | add u v _ _ hu hv =>
      rw [IntermediateField.coe_add, map_add, hu, hv]
    | smul c u _ hu =>
      rw [IntermediateField.coe_smul, map_smul, hu]
  exact key ⟨x, hx⟩ hx'
end Formalism.MainNotions.N.KillingConditions.WildPf
