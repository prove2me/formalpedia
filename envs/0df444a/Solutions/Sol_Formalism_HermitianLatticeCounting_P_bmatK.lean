-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.bmatK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:15.359923+00:00
-- url     : https://prove2.me/submissions/4c9c5060-6fec-42e1-bcbf-d72b686d18ff

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
variable {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (h' : U →ₗ[K] U →ₗ⋆[K] K) {m : ℕ} (e f : Fin m → U) (A C : Matrix (Fin m) (Fin m) K)
    (u w : Fin m → U) (hu : ∀ i, u i = ∑ k, A i k • e k) (hw : ∀ j, w j = ∑ l, C j l • f l) :
    (Matrix.of fun i j => h' (u i) (w j)) = A * (Matrix.of fun k l => h' (e k) (f l)) * Cᴴ := by
  ext i j
  simp only [Matrix.of_apply, hu, hw, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
end Formalism.HermitianLatticeCounting.P
