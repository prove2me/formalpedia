-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.comat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:24:37.564795+00:00
-- url     : https://prove2.me/submissions/5122a54f-2629-4a2c-967b-99852c7eee62

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_sgn_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_Th_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_EE_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_Tm_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_REAL_qComatrix_of
import Theorems.Thm_Formalism_REAL_quantumMinorColSkew_holds
import Theorems.Thm_Formalism_REAL_quantumMinorRowSkew_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V)
namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
theorem _root_.solution (hE : GlRel E) (u : ℂ) (X : Fin (N + 1) → V) (i : Fin (N + 1)) :
    Th E u ((u - (N : ℂ)) • X + EE E X) i = qdet E u (X i) := by
  have h : ∀ l, ∑ j : Fin (N + 1), ((-1 : ℂ) ^ ((j : ℕ) + (i : ℕ))) •
      qminor E j.succAbove i.succAbove u (Tm E (u - (N : ℂ)) j l (X l)) = if i = l then qdet E u (X l) else 0 := by
    intro l
    have := congrArg (fun T : Module.End ℂ V => T (X l))
      (qComatrix_of quantumMinorRowSkew_holds quantumMinorColSkew_holds (Module.End ℂ V) N E hE u i l)
    simp only [sgn_mul, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [apply_ite (fun T : Module.End ℂ V => T (X l)), LinearMap.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl (fun j _ => by rw [add_comm])
  have h2 : ∑ l, (if i = l then qdet E u (X l) else 0) = qdet E u (X i) := by simp
  rw [← h2, ← Finset.sum_congr rfl (fun l _ => h l), Finset.sum_comm, Th_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.smul_sum, ← map_sum]
  congr 2
  simp only [Tm_apply, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply,
    Pi.smul_apply, EE_apply]
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
