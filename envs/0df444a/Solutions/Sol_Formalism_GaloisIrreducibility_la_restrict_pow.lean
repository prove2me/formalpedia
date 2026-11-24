-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.la_restrict_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:43.230117+00:00
-- url     : https://prove2.me/submissions/46475b33-3d43-4dc1-ae28-0305cc4b1096

import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableOf
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_LemmaAOf

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
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
namespace Formalism.GaloisIrreducibility
theorem _root_.solution (τ : Module.End K V) (W : Submodule K V) (hτ : ∀ v ∈ W, τ v ∈ W)
    (n : ℕ) (v : W) : (((τ.restrict hτ) ^ n) v : V) = (τ ^ n) v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.restrict_coe_apply, ih, pow_succ',
      Module.End.mul_apply]
end Formalism.GaloisIrreducibility
