-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.RealCyclotomicSubfield.real_on_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:05:49.562807+00:00
-- url     : https://prove2.me/submissions/b9675456-5250-4d22-bd5f-794541fa28be

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
theorem _root_.solution {K : Type*} [Field K] [Algebra ℚ K] (t : K) (φ : K →+* ℂ)
    (ht : starRingEnd ℂ (φ t) = φ t) : ∀ x ∈ ℚ⟮t⟯, starRingEnd ℂ (φ x) = φ x := by
  intro x hx
  have key : Subfield.closure (Set.range (algebraMap ℚ K) ∪ {t}) ≤
      ((starRingEnd ℂ).comp φ).eqLocusField φ := by
    rw [Subfield.closure_le]
    rintro y (⟨q, rfl⟩ | hy)
    · show (starRingEnd ℂ) (φ (algebraMap ℚ K q)) = φ (algebraMap ℚ K q)
      simp only [RingHom.map_rat_algebraMap]
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ht
  exact key hx
end Formalism.FrobeniusOrbits.RealCyclotomicSubfield
