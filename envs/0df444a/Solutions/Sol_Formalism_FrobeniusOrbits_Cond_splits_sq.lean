-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.splits_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:15:45.581807+00:00
-- url     : https://prove2.me/submissions/943ffc59-e79e-4c8e-9b38-39f9fab6ee69

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
theorem _root_.solution {K : Type*} [Field K] [Algebra ℚ K] (c : ℕ) (g : K) (hg : g ^ 2 = -(c : K)) :
    ((X ^ 2 + C (c : ℚ) : ℚ[X]).map (algebraMap ℚ K)).Splits := by
  have hC : (C g : K[X]) ^ 2 = -(c : K[X]) := by
    rw [← C_pow, hg, C_neg, map_natCast]
  have hm : (X ^ 2 + C (c : ℚ) : ℚ[X]).map (algebraMap ℚ K) = (X - C g) * (X - C (-g)) := by
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      map_natCast, C_neg, Polynomial.map_natCast]
    linear_combination hC
  rw [hm]
  exact (Polynomial.Splits.X_sub_C g).mul (Polynomial.Splits.X_sub_C (-g))
end Formalism.FrobeniusOrbits.Cond
