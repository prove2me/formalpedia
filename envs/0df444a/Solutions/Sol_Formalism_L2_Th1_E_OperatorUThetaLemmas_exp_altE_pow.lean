-- Prove2me | solution 1 for Formalism.L2.Th1.E.OperatorUThetaLemmas.exp_altE_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:56.06455+00:00
-- url     : https://prove2.me/submissions/113a3e9b-c532-4cd7-9b14-b6cf800ed76b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_OpUTh0RootOf
import Theorems.Thm_Formalism_L2_Th1_E_OperatorUThetaLemmas_altE_nat_mul
import Theorems.Thm_Formalism_L2_Th1_F_altEInt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.OperatorUThetaLemmas
open Formalism.L2.Th1.F
namespace Formalism.L2.Th1.E.OperatorUThetaLemmas
theorem _root_.solution (L : PeriodPair) (N : ℕ) (x y : ℂ)
    (hx : (N : ℂ) * x ∈ L.lattice) (hy : (N : ℂ) * y ∈ L.lattice) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L x y : ℂ)) ^ (2 * N ^ 2) = 1 := by
  obtain ⟨k, hk⟩ := altEInt L _ _ hx hy
  rw [altE_nat_mul] at hk
  have hk' : ((N : ℂ)) ^ 2 * (altE L x y : ℂ) = (k : ℂ) := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hk
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨-k, ?_⟩
  push_cast
  rw [← hk']
  ring
end Formalism.L2.Th1.E.OperatorUThetaLemmas
