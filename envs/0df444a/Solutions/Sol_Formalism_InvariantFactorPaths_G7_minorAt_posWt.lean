-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.minorAt_posWt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:42.494931+00:00
-- url     : https://prove2.me/submissions/4c59b30e-8afb-4b18-8df2-f880bf9067c9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MinorProdBlockDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
variable {K σ : Type} [Field K] [DecidableEq σ] {r0 r1 : ℕ}
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {l : ℕ} (s s' : σ) (T : Fin l → Fin r0 → K) (I : Fin l → Fin r1) :
    MvPolynomial.IsWeightedHomogeneous (posWt r0 r1 s) (minorAt s' T I)
      (if s' = s then l else 0) := by
  have hdeg : (if s' = s then l else 0) = 0 + ∑ _i : Fin l, (if s' = s then 1 else 0) := by
    split_ifs with h <;> simp [h]
  rw [hdeg, minorAt, Matrix.det_apply']
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun e _ => ?_)
  refine MvPolynomial.IsWeightedHomogeneous.mul ?hsign
    (MvPolynomial.IsWeightedHomogeneous.prod _ _ _ (fun i _ => ?hent))
  case hsign =>
    have hC := MvPolynomial.isWeightedHomogeneous_C (posWt r0 r1 s)
      ((Equiv.Perm.sign e : ℤ) : K)
    rw [map_intCast] at hC
    exact hC
  case hent =>
    show MvPolynomial.IsWeightedHomogeneous (posWt r0 r1 s)
      (∑ a, MvPolynomial.C (T (e i) a) * MvPolynomial.X (s', a, I i)) (if s' = s then 1 else 0)
    refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun a _ => ?_)
    exact (MvPolynomial.isWeightedHomogeneous_X K (posWt r0 r1 s) (s', a, I i)).C_mul (T (e i) a)
end Formalism.InvariantFactorPaths.G7
