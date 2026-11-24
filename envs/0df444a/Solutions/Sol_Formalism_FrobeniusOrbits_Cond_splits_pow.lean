-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.splits_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:22:11.755214+00:00
-- url     : https://prove2.me/submissions/4c31d664-d05d-4568-bd8d-4db6da8ace86

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Cond
namespace Formalism.FrobeniusOrbits.Cond
theorem _root_.solution {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ} {ξ : K}
    (hξ : IsPrimitiveRoot ξ n) : ((X ^ n - 1 : ℚ[X]).map (algebraMap ℚ K)).Splits := by
  have hm : (X ^ n - 1 : ℚ[X]).map (algebraMap ℚ K) = X ^ n - C 1 := by simp
  rw [hm]
  exact X_pow_sub_one_splits hξ
end Formalism.FrobeniusOrbits.Cond
