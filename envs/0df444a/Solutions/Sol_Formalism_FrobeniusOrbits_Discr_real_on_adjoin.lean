-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Discr.real_on_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:07.58721+00:00
-- url     : https://prove2.me/submissions/f89fc2e1-1a2d-4778-90ce-c122146bd2d8

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield

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
open Formalism.FrobeniusOrbits.Discr
namespace Formalism.FrobeniusOrbits.Discr
theorem _root_.solution {K : Type*} [Field K] [Algebra ℚ K] (t : K) (φ : K →+* ℂ)
    (ht : starRingEnd ℂ (φ t) = φ t) : ∀ x ∈ ℚ⟮t⟯, starRingEnd ℂ (φ x) = φ x := by
  intro x hx
  have hS : Set.range (algebraMap ℚ K) ∪ {t} ⊆
      (((starRingEnd ℂ).comp φ).eqLocusField φ : Subfield K) := by
    rintro y (⟨q, rfl⟩ | rfl)
    · exact RingHom.congr_fun
        (RingHom.ext_rat ((starRingEnd ℂ).comp (φ.comp (algebraMap ℚ K))) (φ.comp (algebraMap ℚ K))) q
    · exact ht
  exact (Subfield.closure_le.mpr hS) hx
end Formalism.FrobeniusOrbits.Discr
