-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_algEquiv_extending
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:34.98073+00:00
-- url     : https://prove2.me/submissions/0ab01898-870d-431c-87c3-4a08b321257a

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FixedByAutomorphismInField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] [IsAlgClosed E]
    (σ₀ : algebraicClosure F E ≃ₐ[F] algebraicClosure F E) :
    ∃ σ : E ≃ₐ[F] E, ∀ a : algebraicClosure F E, σ (a : E) = (σ₀ a : E) := by
  obtain ⟨ι, B, hB⟩ := exists_isTranscendenceBasis' (algebraicClosure F E) E
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis B hB
  let e₁ : MvPolynomial ι (algebraicClosure F E) ≃ₐ[algebraicClosure F E]
      Algebra.adjoin (algebraicClosure F E) (Set.range B) := hB.1.aevalEquiv
  let m : MvPolynomial ι (algebraicClosure F E) ≃+* MvPolynomial ι (algebraicClosure F E) :=
    MvPolynomial.mapEquiv ι σ₀.toRingEquiv
  let e : Algebra.adjoin (algebraicClosure F E) (Set.range B) ≃+*
      Algebra.adjoin (algebraicClosure F E) (Set.range B) :=
    e₁.symm.toRingEquiv.trans (m.trans e₁.toRingEquiv)
  let σ : E ≃+* E := IsAlgClosure.equivOfEquiv E E e
  have he : ∀ a : algebraicClosure F E,
      e (algebraMap _ _ a) = algebraMap _ _ (σ₀ a) := by
    intro a
    simp only [e, m, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.mapEquiv_apply, MvPolynomial.map_C,
      ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rfl
  have hσ : ∀ a : algebraicClosure F E, σ (a : E) = (σ₀ a : E) := by
    intro a
    have h1 : (a : E) = algebraMap (Algebra.adjoin (algebraicClosure F E) (Set.range B)) E
        (algebraMap _ _ a) := rfl
    rw [h1, IsAlgClosure.equivOfEquiv_algebraMap, he]
    rfl
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) ?_, hσ⟩
  intro r
  have h1 : algebraMap F E r = ((algebraMap F (algebraicClosure F E) r : algebraicClosure F E) : E) :=
    rfl
  rw [h1, hσ, AlgEquiv.commutes]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
