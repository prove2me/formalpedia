-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.generalized_log_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:27:43.325627+00:00
-- url     : https://prove2.me/submissions/40977e29-25a9-449e-b00a-6b13bbcc7631

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_isIdMod2_genLog
import Theorems.Thm_Formalism_FG_SolveVAux_low_P
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_solve_exists_vector
import Theorems.Thm_Formalism_FG_subst_injective_vector
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries
open Formalism.FG.SolveVAux (Low low_mono low_add low_mul low_pow low_one_iff low_P)
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : GenLogInverse.{u, v} := by
  intro K _ _ l hl τ _ _ p
  haveI := Fintype.ofFinite τ
  have hf := isIdMod2_genLog (K := K) hl.two_le p
  obtain ⟨g, hg0, hg⟩ := Formalism.FG.solve_exists_vector K τ τ (genLog (K := K) l p) (fun j => X j) hf
    (fun j => constantCoeff_X j)
  refine ⟨g, hg0, hg, ?_⟩
  have hsg : HasSubst g := by
    first
      | exact hasSubst_of_constantCoeff_zero hg0
      | exact HasSubst.of_constantCoeff_zero' hg0
      | exact HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hg0 s]; exact IsNilpotent.zero)
  have hsf : HasSubst (genLog (K := K) l p) := by
    first
      | exact hasSubst_of_constantCoeff_zero hf.1
      | exact HasSubst.of_constantCoeff_zero' hf.1
      | exact HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hf.1 s]; exact IsNilpotent.zero)

  have key := Formalism.FG.subst_injective_vector K τ τ (genLog (K := K) l p)
    (fun x => subst (genLog (K := K) l p) (g x)) X hf
    (fun x => constantCoeff_subst_eq_zero hsf hf.1 (hg0 x)) (fun x => constantCoeff_X x) (fun j => by
      rw [← subst_comp_subst_apply hsg hsf, hg j, subst_X hsf, subst_self]
      rfl)
  exact fun x => congrFun key x
end Formalism.DworkPowerSeriesWeights
