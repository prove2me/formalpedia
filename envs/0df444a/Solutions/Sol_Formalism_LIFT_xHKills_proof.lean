-- Prove2me | solution 1 for Formalism.LIFT.xHKills_proof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:15:56.886307+00:00
-- url     : https://prove2.me/submissions/70962a79-97d5-43c9-a798-a5306c908907

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CompsOfMemMap
import Theorems.Thm_Formalism_LIFT_xh_coeffs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
open Finset
namespace Formalism.LIFT
theorem _root_.solution : XHKills := by
  intro ℓ _ A _ φA ε X Q H c aa _ hε hU hX hQ hc
  have hℓ : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  have h1 : 1 < ℓ := (Fact.out : ℓ.Prime).one_lt
  obtain ⟨n, hn⟩ : ∃ n, c < ℓ ^ n := ⟨c, Nat.lt_pow_self h1⟩
  let p : Polynomial ℤ := (Polynomial.X - Polynomial.C 1) ^ c
  have hmon : p.Monic := (Polynomial.monic_X_sub_C (1 : ℤ)).pow c
  have hdeg : p.natDegree = c := by
    simp only [p]
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have hsum : (ε - 1) ^ c = ∑ k ∈ range (ℓ ^ n), (p.coeff k : A) * ε ^ k := by
    have := Polynomial.aeval_eq_sum_range' (p := p) (by omega : p.natDegree < ℓ ^ n) ε
    simp only [zsmul_eq_mul] at this
    rw [← this]
    simp [p]
  have hmem : X ^ H * ∑ k ∈ range (ℓ ^ n), (p.coeff k : A) * ε ^ k ∈ aa := by
    rw [← hsum]
    exact aa.mul_mem_left _ hc
  have := xh_coeffs φA ε aa hℓ hε hU X Q H hX hQ n (fun k => p.coeff k) hmem c hn
  have hcoef : p.coeff c = 1 := by
    have := hmon.coeff_natDegree
    rwa [hdeg] at this
  simpa [hcoef] using this
end Formalism.LIFT
