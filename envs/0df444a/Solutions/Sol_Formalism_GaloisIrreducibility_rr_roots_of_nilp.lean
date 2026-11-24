-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.rr_roots_of_nilp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:36.541012+00:00
-- url     : https://prove2.me/submissions/70743bf4-a39d-40d3-b65e-b79b4603ad82

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
theorem _root_.solution (B : Module.End K V) (c : K) (h : IsNilpotent (B - c • 1)) :
    B.charpoly.roots = Multiset.replicate (finrank K V) c := by
  have h1 := (LinearMap.isNilpotent_iff_charpoly _).mp h
  rw [LinearMap.charpoly_sub_smul] at h1
  have h2 : B.charpoly = (Polynomial.X - Polynomial.C c) ^ finrank K V := by
    have h3 := congrArg (fun p => p.comp (Polynomial.X - Polynomial.C c)) h1
    simp only [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
      sub_add_cancel, Polynomial.comp_X, Polynomial.pow_comp] at h3
    exact h3
  rw [h2, Polynomial.roots_pow, Polynomial.roots_X_sub_C, Multiset.nsmul_singleton]
end Formalism.GaloisIrreducibility
