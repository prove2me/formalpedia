-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.wach_lattice_nonempty_gamma
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:43.866448+00:00
-- url     : https://prove2.me/submissions/ef5d76f8-46c6-4639-b942-0067e595a1c3

import Definitions.Def_Formalism_CoboundaryTransfers_StatementEx
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_WachLatticeNonemptyGamma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
open Polynomial ExG
namespace Formalism.CoboundaryTransfers
theorem _root_.solution : NonemptyG := by
  intro p _ hp2
  have hp := (Fact.out : p.Prime)
  refine ⟨base p hp2, W p hp2, rfl, ?_, ?_, ?_, φA_X_eq p, ?_, ?_, ?_⟩
  · intro h
    have h1 : (1 : K p) ∈ (W p hp2).N := by
      show (1 : K p) ∈ LinearMap.range (Algebra.linearMap (A p) (K p))
      exact ⟨1, by simp⟩
    rw [h, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  · exact not_isUnit_X
  · show ¬ IsUnit ((X : A p) ^ (p - 1))
    rw [isUnit_pow_iff (by have := hp.two_le; omega)]
    exact not_isUnit_X
  · refine ⟨0, ?_⟩
    show γA p X = X * (algebraMap ℤ_[p] (A p) (-1) + X * 0)
    simp [γA_X]
  · refine ⟨1, isUnit_one, ⟨0, by simp⟩, ?_⟩
    show γA p (X ^ (p - 1)) = 1 * X ^ (p - 1)
    rw [map_pow, γA_X, (hp.even_sub_one hp2).neg_pow, one_mul]
  · refine ⟨algebraMap (A p) (K p) X, fun h => ?_⟩
    simp only [W, AlgHom.toLinearMap_apply] at h
    rw [liftK_alg, γA_X] at h
    have h2 := congrArg (fun f : A p => f.coeff 1) ((IsFractionRing.injective (A p) (K p)) h)
    simp only [coeff_neg, coeff_X_one] at h2
    have h3 : (2 : ℤ_[p]) = 0 := by linear_combination -h2
    exact two_ne_zero h3
end Formalism.CoboundaryTransfers
