-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.HaP.comp_smul_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:57:46.92398+00:00
-- url     : https://prove2.me/submissions/1a1791f0-4b19-4cf6-83d5-35198577faf1

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_coeff_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
variable {K : Type} [Field K] [CharZero K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds.HaP
theorem _root_.solution (lam : K →ₗ[ℚ] ℚ) (c : K) (p : MvPolynomial σ ℚ) :
    comp lam (c • map (algebraMap ℚ K) p) = lam c • p := by
  ext m
  simp only [coeff_comp, coeff_smul, coeff_map, smul_eq_mul]
  rw [mul_comm c, ← Algebra.smul_def, map_smul, smul_eq_mul]
  exact mul_comm _ _
end Formalism.L2.FormalSeriesBounds.HaP
