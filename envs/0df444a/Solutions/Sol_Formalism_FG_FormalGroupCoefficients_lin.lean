-- Prove2me | solution 1 for Formalism.FG.FormalGroupCoefficients.lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:28:20.332278+00:00
-- url     : https://prove2.me/submissions/3d8b92ab-191b-4bf9-879f-c29d46eaaf32

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_cc_X
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_coeff_X_single
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_lin_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open Formalism Formalism.FG Formalism.FG.FormalGroupCoefficients
open MvPowerSeries Formalism.G Formalism.LT
variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {f : ι → MvPowerSeries ι R} {F : ι → MvPowerSeries (Fin 2 × ι) R}
namespace Formalism.FG.FormalGroupCoefficients
theorem _root_.solution (hf : IsIdMod2 f) (hF0 : ∀ i, constantCoeff (F i) = 0)
    (hFG : ∀ j, subst F (f j) = atXv (f j) + atYv (f j)) (i : ι) (x : Fin 2 × ι) :
    coeff (Finsupp.single x 1) (F i) = if x.2 = i then 1 else 0 := by
  have h := congrArg (coeff (Finsupp.single x 1)) (hFG i)
  rw [lin_subst hF0, map_add, atXv, atYv, lin_subst (fun _ => cc_X _),
    lin_subst (fun _ => cc_X _)] at h
  simp only [hf.2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h
  rw [h, coeff_X_single, coeff_X_single]
  obtain ⟨a, k⟩ := x
  fin_cases a <;> by_cases hk : k = i <;> simp [hk]
end Formalism.FG.FormalGroupCoefficients
