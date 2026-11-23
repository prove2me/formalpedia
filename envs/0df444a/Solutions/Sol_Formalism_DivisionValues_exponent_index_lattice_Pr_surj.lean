-- Prove2me | solution 1 for Formalism.DivisionValues.exponent_index_lattice.Pr_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:59.88373+00:00
-- url     : https://prove2.me/submissions/329e83fb-062c-41f9-b269-a525152d2b34

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.exponent_index_lattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open RationalHermitianForm
namespace Formalism.DivisionValues.exponent_index_lattice
theorem _root_.solution {n d : ℕ} {H : Matrix (Fin n) (Fin n) K}
    {E : Matrix (Fin n) (Fin d) K} {Pr : Matrix (Fin d) (Fin n) K} (hO : IsOrthProj H E Pr) :
    Function.Surjective (Matrix.mulVecLin Pr) := by
  intro z
  refine ⟨E.mulVec z, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hO.1, Matrix.one_mulVec]
end Formalism.DivisionValues.exponent_index_lattice
