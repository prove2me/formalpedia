-- Prove2me | solution 1 for Formalism.L2.DIV.trace_isIntegral_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:56:17.651844+00:00
-- url     : https://prove2.me/submissions/0eb61b2b-7b1f-4b86-9885-2edad79f4f92

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
namespace Formalism.L2.DIV
theorem _root_.solution {k V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (f : Module.End k V) {N : ℕ} (hN : N ≠ 0) (hf : f ^ N = 1) :
    IsIntegral ℤ (LinearMap.trace k V f) := by
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  refine IsIntegral.multiset_sum fun μ hμ => ?_
  have hroot : f.charpoly.IsRoot μ := (Polynomial.mem_roots'.mp hμ).2
  obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr hroot).exists_hasEigenvector
  have h1 := hv.pow_apply N
  rw [hf, Module.End.one_apply] at h1
  have h2 : (μ ^ N - 1) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
  have h3 : μ ^ N = 1 := by
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv.2
  exact IsIntegral.of_pow (Nat.pos_of_ne_zero hN) (by rw [h3]; exact isIntegral_one)
end Formalism.L2.DIV
