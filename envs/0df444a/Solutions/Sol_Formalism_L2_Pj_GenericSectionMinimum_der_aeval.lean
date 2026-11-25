-- Prove2me | solution 1 for Formalism.L2.Pj.GenericSectionMinimum.der_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:50:21.703286+00:00
-- url     : https://prove2.me/submissions/11725324-4358-4746-9b6f-bc15621f058c

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DerAeval
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_TotalDegreePderivLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenericSectionMinimum
open IsLocalRing Cardinal
variable {F : Type} [Field F]
namespace Formalism.L2.Pj.GenericSectionMinimum
theorem _root_.solution {δ : F → F} (h : IsDer δ) {E : Type} [CommRing E] [Algebra E F]
    (hE : ∀ e, δ (algebraMap E F e) = 0) {σ : Type} [Fintype σ] [DecidableEq σ] (t : σ → F)
    (P : MvPolynomial σ E) :
    δ (MvPolynomial.aeval t P) = ∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i P) * δ (t i) := by
  induction P using MvPolynomial.induction_on
  next a =>
    simp [hE]
  next p q hp hq =>
    simp only [map_add, h.add, hp, hq, add_mul, Finset.sum_add_distrib]
  next p n hp =>
    have hsingle : ∀ i, MvPolynomial.aeval t (MvPolynomial.pderiv i (MvPolynomial.X n : MvPolynomial σ E)) =
        if i = n then 1 else 0 := by
      intro i
      by_cases hi : i = n
      · subst hi
        simp
      · simp [MvPolynomial.pderiv_X, Pi.single_apply, hi, Ne.symm hi]
    simp only [map_mul, MvPolynomial.aeval_X, h.mul, hp, MvPolynomial.pderiv_mul, map_add, hsingle,
      add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.mul_sum, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
end Formalism.L2.Pj.GenericSectionMinimum
