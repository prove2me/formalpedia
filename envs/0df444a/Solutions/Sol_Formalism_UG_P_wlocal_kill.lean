-- Prove2me | solution 1 for Formalism.UG.P.wlocal_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:40:31.467526+00:00
-- url     : https://prove2.me/submissions/cca8b8d6-8b01-4578-8291-30d9fa4ebfa0

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
variable {R : Type} [CommRing R]
namespace Formalism.UG.P
theorem _root_.solution (P : Ideal R) [P.IsPrime] {σ : Type} (w : MvPolynomial σ R)
    (hw : map (algebraMap R (Localization.AtPrime P)) w = 0) :
    ∃ t ∈ P.primeCompl, C t * w = 0 := by
  classical
  have hc : ∀ m, ∃ t : P.primeCompl, (t : R) * w.coeff m = 0 := by
    intro m
    have h1 : algebraMap R (Localization.AtPrime P) (w.coeff m) = 0 := by
      have := congrArg (coeff m) hw
      rwa [coeff_map, coeff_zero] at this
    exact (IsLocalization.map_eq_zero_iff P.primeCompl (Localization.AtPrime P) _).mp h1
  choose t ht using hc
  refine ⟨∏ m ∈ w.support, (t m : R), Submonoid.prod_mem _ (fun m _ => (t m).2), ?_⟩
  ext m
  rw [coeff_C_mul, coeff_zero]
  by_cases hm : m ∈ w.support
  · rw [← Finset.mul_prod_erase _ _ hm, mul_comm ((t m : P.primeCompl) : R), mul_assoc, ht m, mul_zero]
  · have h0 : w.coeff m = 0 := by
      by_contra h
      exact hm (mem_support_iff.mpr h)
    rw [h0, mul_zero]
end Formalism.UG.P
