-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.rr_charpoly_compl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:35.991834+00:00
-- url     : https://prove2.me/submissions/37b77c59-a16e-4201-9f32-a93075217a21

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_RestrictRoots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Module Polynomial
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
namespace Formalism.GaloisIrreducibility
theorem _root_.solution (φ : Module.End K V) (P Q : Submodule K V) (hPQ : IsCompl P Q)
    (hP : ∀ x ∈ P, φ x ∈ P) (hQ : ∀ x ∈ Q, φ x ∈ Q) :
    φ.charpoly = (φ.restrict hP).charpoly * (φ.restrict hQ).charpoly := by
  have hconj : (Submodule.prodEquivOfIsCompl P Q hPQ).symm.conj φ = (φ.restrict hP).prodMap (φ.restrict hQ) := by
    apply LinearMap.ext
    rintro ⟨p, q⟩
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_symm, Submodule.coe_prodEquivOfIsCompl', LinearMap.prodMap_apply]
    rw [map_add φ, ← LinearMap.restrict_coe_apply φ hP p, ← LinearMap.restrict_coe_apply φ hQ q,
      map_add, Submodule.prodEquivOfIsCompl_symm_apply_left,
      Submodule.prodEquivOfIsCompl_symm_apply_right]
    simp
  rw [← LinearEquiv.charpoly_conj (Submodule.prodEquivOfIsCompl P Q hPQ).symm φ, hconj, LinearMap.charpoly_prodMap]
end Formalism.GaloisIrreducibility
