-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majDual_herm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:53.272899+00:00
-- url     : https://prove2.me/submissions/fcccb55e-d809-4047-a882-07373c645aa4

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V) (v : InfinitePlace K)
    (hst : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) (x y : V) :
    v.embedding (h x y) = dotProduct (star (vecAt b v x)) ((gramAt h b v).mulVec (vecAt b v y)) := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul,
    smul_eq_mul, map_mul, starRingEnd_apply, hst, RingHom.id_apply]
  simp only [dotProduct, Matrix.mulVec, vecAt, gramAt, Matrix.of_apply, Pi.star_apply]
  simp only [Finset.mul_sum]
  first
  | exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring1
  | (rw [Finset.sum_comm]
     exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring1)
end Formalism.HermitianLatticesTheory
