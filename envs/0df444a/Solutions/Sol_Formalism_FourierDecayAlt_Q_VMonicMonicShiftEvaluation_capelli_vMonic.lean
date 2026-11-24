-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation.capelli_vMonic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:38:35.747147+00:00
-- url     : https://prove2.me/submissions/06c237b2-a393-4a30-a7aa-0a03134e7715

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonicShiftEvaluation_EvalXAddCMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonicShiftEvaluation_CapelliPolynomialMonic
import Theorems.Thm_Formalism_FourierDecayAlt_Q_VMonicMonicShiftEvaluation_coeff_PQ
import Theorems.Thm_Formalism_FourierDecayAlt_Q_VMonicMonicShiftEvaluation_term
import Theorems.Thm_Formalism_FourierDecayAlt_Q_VMonicMonicShiftEvaluation_vAB_eval


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation
open Formalism.QuantumDeterminants
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation
theorem _root_.solution : VMonic := by
  intro E _ _ r i hi
  obtain ⟨h1, h2, -⟩ := coeff_PQ (E := E) r i hi
  classical
  refine ⟨fun j g => if hg : g ∈ WSm r E then (((PQ r E i).1.coeff j ⟨g, hg⟩ : WSm r E) : (Fin r → ℂ) → E)
    else 0, ?_⟩
  intro Y f hf
  simp only [dif_pos hf]
  have hdeg : (PQ r E i).1.natDegree < i + 1 :=
    Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.2 h2)
  have hv := (vAB_eval r Y i ⟨f, hf⟩).1
  rw [hv, eval_eq_sum_range' hdeg, Finset.sum_range_succ, LinearMap.add_apply, Submodule.coe_add,
    LinearMap.sum_apply, Submodule.coe_sum, term, h1, add_comm]
  congr 1
  all_goals exact Finset.sum_congr rfl fun j _ => term r _ Y j ⟨f, hf⟩
end Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation
