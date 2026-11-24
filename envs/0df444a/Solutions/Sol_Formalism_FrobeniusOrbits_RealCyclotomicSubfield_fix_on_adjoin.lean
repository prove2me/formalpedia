-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.RealCyclotomicSubfield.fix_on_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:08:39.793436+00:00
-- url     : https://prove2.me/submissions/9399479d-4762-452c-a173-b4322474627e

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.RealCyclotomicSubfield
namespace Formalism.FrobeniusOrbits.RealCyclotomicSubfield
theorem _root_.solution {L : Type*} [Field L] [Algebra ℚ L] {E : IntermediateField ℚ L}
    (σ : E ≃ₐ[ℚ] E) {t : L} (hle : ℚ⟮t⟯ ≤ E)
    (hσ : ((σ ⟨t, hle (mem_adjoin_simple_self ℚ t)⟩ : E) : L) = t) :
    ∀ x : E, (x : L) ∈ ℚ⟮t⟯ → σ x = x := by
  intro x hx
  have key : Subfield.closure (Set.range (algebraMap ℚ L) ∪ {t}) ≤
      (((σ : E →+* E).eqLocusField (RingHom.id E)).map (E.val : E →+* L)) := by
    rw [Subfield.closure_le]
    rintro y (⟨q, rfl⟩ | hy)
    · refine Subfield.mem_map.mpr ⟨(q : E), ?_, ?_⟩
      · show σ (q : E) = (q : E)
        exact map_ratCast σ q
      · rw [eq_ratCast (algebraMap ℚ L) q]
        exact map_ratCast (E.val : E →+* L) q
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      refine Subfield.mem_map.mpr ⟨⟨y, hle (mem_adjoin_simple_self ℚ y)⟩, ?_, rfl⟩
      show σ _ = _
      exact Subtype.ext hσ
  obtain ⟨y, hy, hyx⟩ := Subfield.mem_map.mp (key hx)
  have hyx' : y = x := Subtype.ext hyx
  subst hyx'
  exact hy
end Formalism.FrobeniusOrbits.RealCyclotomicSubfield
