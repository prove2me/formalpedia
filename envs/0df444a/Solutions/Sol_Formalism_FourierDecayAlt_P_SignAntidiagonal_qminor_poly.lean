-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.qminor_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:56:00.508511+00:00
-- url     : https://prove2.me/submissions/790f386c-c183-4ddc-81ae-dbe6231c624d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightDerivativeRulePsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlMonoConst
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_lmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_prod_poly
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution {n t : ℕ} (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (s0 : ℂ) :
    PolyLe t (fun u => qminor E a b (u + s0) - algebraMap ℂ A (u ^ t *
      ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if a (σ k) = b k then (1 : ℂ) else 0))) := by
  classical
  refine pl_congr (f := fun u => ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) *
      ((List.ofFn fun k : Fin t => algebraMap ℂ A ((u + (s0 - (k : ℂ))) *
          (if a (σ k) = b k then (1 : ℂ) else 0)) + E (a (σ k)) (b k)).prod -
        algebraMap ℂ A (u ^ t * ∏ k, (if a (σ k) = b k then (1 : ℂ) else 0)))) ?_
    (pl_sum _ _ fun σ _ => pl_lmul _ (prod_poly t _ _ _))
  intro u
  have hT : ∀ (σ : Equiv.Perm (Fin t)) (k : Fin t), Tm E (u + s0 - (k : ℂ)) (a (σ k)) (b k) =
      algebraMap ℂ A ((u + (s0 - (k : ℂ))) * (if a (σ k) = b k then (1 : ℂ) else 0)) + E (a (σ k)) (b k) := by
    intro σ k
    unfold Tm
    split_ifs <;> simp [add_sub_assoc]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · unfold qminor
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hT]
  · rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_left_comm (u ^ t) (((Equiv.Perm.sign σ : ℤ) : ℂ)),
      map_mul (algebraMap ℂ A) (((Equiv.Perm.sign σ : ℤ) : ℂ)), map_intCast]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
