-- Prove2me | solution 1 for Formalism.L2.DIV.subE_rat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:47:52.043895+00:00
-- url     : https://prove2.me/submissions/40b30c80-0880-4826-a922-7e8fd0fddde4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas

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
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
variable {K : Type} [Field K] [StarRing K] {n : ℕ}
namespace Formalism.L2.DIV
theorem _root_.solution (Z : Submodule K (Fin n → K)) (h : SubHasRatBasis Z) (i : Fin n)
    (j : Fin (subDim Z)) : subE Z i j ∈ cmMax K := by
  have e : subBasis Z = h.choose := by
    first
    | exact dif_pos h
    | (unfold subBasis; exact dif_pos h)
    | (rw [subBasis, dif_pos h])
    | (simp only [subBasis, h, dite_true])
    | (unfold subBasis; simp [h])
  show ((subBasis Z j : Fin n → K) i) ∈ cmMax K
  rw [e]
  exact h.choose_spec j i
end Formalism.L2.DIV
