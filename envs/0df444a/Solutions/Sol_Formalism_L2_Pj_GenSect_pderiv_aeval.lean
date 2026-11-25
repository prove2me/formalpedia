-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.pderiv_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:39.445494+00:00
-- url     : https://prove2.me/submissions/1c5caf5a-6d8e-4f51-8ab8-4d89eb2d2956

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ)
variable {K Ω D m}
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (j₀ : Fin m) (u : ι → CT Ω D j₀)
    (q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) (G : MvPolynomial ι K) :
    pderiv q (aeval u G) = ∑ p, aeval u (pderiv p G) * pderiv q (u p) := by
  induction G using MvPolynomial.induction_on
  next a =>
    first
    | (rw [aeval_C, MvPolynomial.algebraMap_apply, pderiv_C]
       simp only [pderiv_C, map_zero, zero_mul, Finset.sum_const_zero])
    | simp
  next G₁ G₂ h₁ h₂ =>
    simp only [map_add, h₁, h₂, add_mul, Finset.sum_add_distrib]
  next G i h =>
    have e1 : ∀ p, pderiv p (G * X i) = G * pderiv p (X i) + X i * pderiv p G := fun p => by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have hs : ∑ p, aeval u (G * pderiv p (X i)) * pderiv q (u p) = aeval u G * pderiv q (u i) := by
      rw [Finset.sum_eq_single i]
      · rw [pderiv_X_self, mul_one]
      · intro b _ hb
        have h0 : pderiv b (X i : MvPolynomial ι K) = 0 := by
          first
          | exact pderiv_X_of_ne (Ne.symm hb)
          | exact pderiv_X_of_ne hb
          | simp [pderiv_X, Pi.single_apply, hb, Ne.symm hb]
        rw [h0, mul_zero, map_zero, zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul, h]
    simp only [e1, map_add, add_mul, Finset.sum_add_distrib]
    rw [hs]
    simp only [map_mul, aeval_X, Finset.mul_sum, mul_assoc]
end Formalism.L2.Pj.GenSect
