-- Prove2me | solution 1 for Formalism.IndefR.Eqv.iter_fderiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:48:31.788803+00:00
-- url     : https://prove2.me/submissions/45f79fdf-20d8-46a8-b527-71812e36e11b

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_NormIterFderivApplyLe
import Theorems.Thm_Formalism_IndefR_Eqv_snoc_eq_cons_rot
import Theorems.Thm_Formalism_IndefR_Eqv_iterSymmR
import Theorems.Thm_P2M_Formalism_IndefR_Eqv_natCast_lt_inf__24812f2382ad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
open Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace Formalism.IndefR.Eqv
theorem _root_.solution {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (w : V) (a : V) (vs : Fin n → V) :
    iteratedFDeriv ℝ n (fun y => fderiv ℝ φ y w) a vs = iteratedFDeriv ℝ (n + 1) φ a (Fin.cons w vs) := by
  have hf : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (m := ∞) (by simp)
  have e1 : (fun y => fderiv ℝ φ y w) = (ContinuousLinearMap.apply ℝ ℂ w) ∘ fderiv ℝ φ := rfl
  rw [e1, ContinuousLinearMap.iteratedFDeriv_comp_left _ hf.contDiffAt (natCast_lt_inf' n).le]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply]
  have e2 : iteratedFDeriv ℝ (n + 1) φ a (Fin.snoc vs w) = iteratedFDeriv ℝ n (fderiv ℝ φ) a vs w := by
    rw [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  rw [← e2, snoc_eq_cons_rot, iterSymmR V ℂ φ hφ (n + 1) a _ (finRotate (n + 1))]
end Formalism.IndefR.Eqv
