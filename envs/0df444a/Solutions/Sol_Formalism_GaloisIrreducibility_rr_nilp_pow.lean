-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.rr_nilp_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:36.161412+00:00
-- url     : https://prove2.me/submissions/232629ea-f8dc-4d82-baff-05fff8d2abce

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
namespace Formalism.GaloisIrreducibility
theorem _root_.solution {R : Type} [Ring R] {K : Type} [Field K] [Algebra K R] (a : R) (c : K)
    (h : IsNilpotent (a - algebraMap K R c)) (q : ℕ) :
    IsNilpotent (a ^ q - algebraMap K R (c ^ q)) := by
  have hc : Commute a (algebraMap K R c) := (Algebra.commutes c a).symm
  rw [map_pow, ← hc.geom_sum₂_mul]
  refine Commute.isNilpotent_mul_left ?_ h
  refine Commute.sum_left _ _ _ fun i _ => ?_
  exact (((Commute.refl a).sub_right hc).pow_left i).mul_left
    ((hc.symm.sub_right (Commute.refl _)).pow_left _)
end Formalism.GaloisIrreducibility
