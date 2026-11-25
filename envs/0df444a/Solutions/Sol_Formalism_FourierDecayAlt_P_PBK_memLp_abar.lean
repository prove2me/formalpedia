-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.memLp_abar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:46:46.066138+00:00
-- url     : https://prove2.me/submissions/d58205b5-6543-4d6d-8a3a-18130a1a40f9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AestronglyMeasurableMainD
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_aestronglyMeasurable_abar
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_card_rootSet_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_jac_norm_bz
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_integral_sum_rootSet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {s : ℕ} (hs : s ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1) {bt : ℂ → H} (hbt : StronglyMeasurable bt)
    (hb : MemLp (bz s bt) 2 volume) :
    MemLp (abar s ε bt) 2 volume ∧ ∫ D, abar s ε bt D ^ 2 ≤ s * ∫ z, ‖bz s bt z‖ ^ 2 := by
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hb2 : Integrable (fun z => ‖bz s bt z‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hb.1).1 hb
  have hF : Integrable (fun z => ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 • ‖bt z‖ ^ 2) := by
    simp_rw [jac_norm_bz hε bt]; exact hb2
  obtain ⟨hGi, hGeq⟩ := integral_sum_rootSet s hs ε hε0 (fun z => ‖bt z‖ ^ 2) hF
  have hpt : ∀ D, abar s ε bt D ^ 2 ≤ s * ∑ z ∈ G.rootSet s (ε * D), ‖bt z‖ ^ 2 := by
    intro D
    refine (sq_sum_le_card_mul_sum_sq).trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_rootSet_le s _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hm := aestronglyMeasurable_abar hs hε0 hbt
  have hsq : Integrable (fun D => abar s ε bt D ^ 2) := by
    refine Integrable.mono' (hGi.const_mul s) (hm.pow 2) (Eventually.of_forall fun D => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt D
  refine ⟨(memLp_two_iff_integrable_sq hm).2 hsq, ?_⟩
  calc ∫ D, abar s ε bt D ^ 2 ≤ ∫ D, (s : ℝ) * ∑ z ∈ G.rootSet s (ε * D), ‖bt z‖ ^ 2 :=
        integral_mono hsq (hGi.const_mul s) hpt
    _ = s * ∫ z, ‖bz s bt z‖ ^ 2 := by
        rw [integral_const_mul, hGeq]
        simp_rw [jac_norm_bz hε bt]
end Formalism.FourierDecayAlt.P.PBK
