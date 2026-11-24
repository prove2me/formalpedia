-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.mem_ideal_smul_top_pi_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:39.758331+00:00
-- url     : https://prove2.me/submissions/a90bac8c-ff09-4c71-9f0c-9c17f650cdac

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.SLP.P.CountO NumberField
open scoped nonZeroDivisors
open NumberField Formalism.SLP.P.CountO
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {R : Type} [CommRing R] (I : Ideal R) (n : ℕ) (x : Fin n → R) :
    x ∈ I • (⊤ : Submodule R (Fin n → R)) ↔ ∀ i, x i ∈ I := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun r hr m _ i => ?_) (fun a b ha hb i => ?_)
    · simpa [Pi.smul_apply, smul_eq_mul] using I.mul_mem_right (m i) hr
    · simpa using I.add_mem (ha i) (hb i)
  · intro hx
    have : x = ∑ i, x i • Pi.single i (1 : R) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) trivial
end Formalism.HermitianLatticeCounting.P
