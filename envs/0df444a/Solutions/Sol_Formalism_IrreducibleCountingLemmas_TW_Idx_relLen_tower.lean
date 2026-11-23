-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_tower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:49.753942+00:00
-- url     : https://prove2.me/submissions/88fb61a7-e79c-4e9e-8d82-419c19d84f28

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
open Formalism.IrreducibleCountingLemmas.TW.Idx
variable {O V : Type} [CommRing O] [AddCommGroup V] [Module O V]
namespace Formalism.IrreducibleCountingLemmas.TW.Idx
theorem _root_.solution {A B C : Submodule O V} (hAB : A ≤ B) (hBC : B ≤ C) :
    relLen C A = relLen B A + relLen C B := by
  unfold relLen
  have h1 : A.comap B.subtype ≤ (A.comap C.subtype).comap (Submodule.inclusion hBC) := by
    intro x hx; exact hx
  have h2 : A.comap C.subtype ≤ B.comap C.subtype := Submodule.comap_mono hAB
  refine Module.length_eq_add_of_exact (Submodule.mapQ _ _ (Submodule.inclusion hBC) h1)
    (Submodule.factor h2) ?_ (Submodule.factor_surjective h2) ?_
  · rw [injective_iff_map_eq_zero]
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    intro hx
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    exact hx
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hfac : Submodule.factor h2 (Submodule.Quotient.mk y) = Submodule.Quotient.mk y := rfl
    rw [hfac, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hy
      exact ⟨Submodule.Quotient.mk ⟨y.1, hy⟩, by rw [Submodule.mapQ_apply]; rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hx
      have h3 : (x : V) - y ∈ A := hx
      have h4 : (y : V) = x - (x - y) := by abel
      show (y : V) ∈ B
      rw [h4]
      exact B.sub_mem x.2 (hAB h3)
end Formalism.IrreducibleCountingLemmas.TW.Idx
