-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DegreeMapArithmetic.weight_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:36:28.014173+00:00
-- url     : https://prove2.me/submissions/b03c0e25-3fa0-4b61-bbfb-7f736a151ed5

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightMonotonicity
import Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_comm_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DegreeMapArithmetic
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.DegreeMapArithmetic
theorem _root_.solution {n : ℕ} (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (hE : GlRel E) (c : Fin n) (m : ℂ)
    (w : V) (hw : E c.castSucc c.castSucc w = m • w) (a : Fin n → ℕ) :
    E c.castSucc c.castSucc (mono (etaK E) a w) = (m + (a c : ℂ)) • mono (etaK E) a w := by
  have hd : ∀ x, E c.castSucc c.castSucc * etaK E x =
      etaK E x * E c.castSucc c.castSucc + (if x = c then (1 : ℂ) else 0) • etaK E x := by
    intro x
    have h := hE c.castSucc c.castSucc x.castSucc (Fin.last n)
    rw [if_neg (Fin.castSucc_lt_last c).ne', sub_zero] at h
    by_cases hx : x = c
    · subst hx
      rw [if_pos rfl] at h
      rw [if_pos rfl, one_smul]
      exact eq_add_of_sub_eq' h
    · rw [if_neg (fun e => hx (Fin.castSucc_injective _ e).symm)] at h
      rw [if_neg hx, zero_smul, add_zero]
      exact sub_eq_zero.mp h
  have hc := congrArg (fun g : Module.End ℂ V => g w) (comm_mono _ (etaK E) _ hd a)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, hw, map_smul] at hc
  rw [hc, add_smul]
  congr 2
  simp
end Formalism.FourierDecayAlt.P.DegreeMapArithmetic
