-- Prove2me | solution 1 for Formalism.L2.LamCM.substGauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:39.719895+00:00
-- url     : https://prove2.me/submissions/ed2a267f-2b22-4305-9617-631217df4518

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsEvalNeZeroOfTotalDegreeLt
import Theorems.Thm_Formalism_L2_LamCM_coeff_aeval_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open MvPolynomial IsLocalRing
namespace Formalism.L2.LamCM
theorem _root_.solution : SubstGauss := by
  intro R K _ _ _ B _ m P U c hP hcU μ
  classical
  obtain ⟨P0, hP0⟩ : P ∈ Set.range (map (algebraMap R K)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨ν, -, rfl⟩ := mem_coeffs_iff.mp ha
    exact hP ν
  let g0 : FrVar m → MvPolynomial (FrVar m) R := fun v =>
    ∑ j, C (hcU v.1 j v.2.2).choose * X (⟨v.1, (v.2.1, j)⟩ : FrVar m)
  have key : aeval (fun w : FrVar m => C (c w.1 w.2.2) * X w) (substFr U P) = map (algebraMap R K) (bind₁ g0 P0) := by
    rw [map_bind₁, hP0, substFr, aeval_bind₁]
    change bind₁ _ P = bind₁ _ P
    refine congrArg (fun g => bind₁ g P) (funext fun v => ?_)
    simp only [g0, map_sum, map_mul, aeval_C, aeval_X, map_C, map_X, algebraMap_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hcU v.1 j v.2.2).choose_spec, C_mul]
    ring
  have h := coeff_aeval_scale (fun w : FrVar m => c w.1 w.2.2) (substFr U P) μ
  rw [key, coeff_map] at h
  exact ⟨_, h⟩
end Formalism.L2.LamCM
