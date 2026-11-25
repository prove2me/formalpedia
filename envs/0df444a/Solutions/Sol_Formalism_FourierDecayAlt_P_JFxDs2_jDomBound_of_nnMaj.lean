-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxDs2.jDomBound_of_nnMaj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:57:15.429452+00:00
-- url     : https://prove2.me/submissions/e431575f-c655-46cd-9535-7d6e7d9259e0

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JDomBoundOfNnMaj
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs2_sL_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs2_sR_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs2_pn_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs2_allLie_ad
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_bound_scaled
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_length_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_lrt_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_norm_rho_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_sgs_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxDs2
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxDs2
theorem _root_.solution : NNMaj → JDomBound := by
  intro hNN k r Wp Wq _ _ _ _ _ _ D A m F hThr hCC K hK hKsub
  obtain ⟨c, hc⟩ := hCC
  obtain ⟨b, hbI, hb⟩ := hNN k r Wp Wq D A m hThr K hK hKsub
  refine ⟨fun p => c * b p, hbI.const_mul c, ?_⟩
  intro u v hu hv hl g hg
  filter_upwards [hb u v hu hv hl g hg, B7.ae_inSS D] with p hp hin
  have hgG : g ∈ GV k r := (hKsub hg).1
  have hsG : sgs p g ∈ GV k r := B7.sgs_mem D hin hgG
  have hN : 0 < gN (sgs p g) := B6.gN_pos hsG
  have hgA : 0 < gN (sgs p g) ^ A := Real.rpow_pos_of_pos hN A
  have hc0 : 0 ≤ c := by
    have h0 := hc.2 [] [] (by simp) (by simp) (by simp) g hgG
    exact le_trans (mul_nonneg (Real.rpow_pos_of_pos (B6.gN_pos hgG) A).le (norm_nonneg _)) h0
  have hall := allLie_ad (sL_mem hin) (sR_mem hin) hu hv
  have hlen : (B4.lr (u.map (AdL p)) (v.map (AdR p))).length ≤ m := by
    rw [B4.length_lr, List.length_map, List.length_map]; exact hl
  have hbd := B4.bound_scaled hc _ (B4.lrt_lr _ _) hall hlen _ hsG
  rw [← B4.dLR_eq, pn_lr] at hbd
  refine (B7.norm_rho_le D hin _ g).trans ?_
  have h1 : ‖dLR (u.map (AdL p)) (v.map (AdR p)) F (sgs p g)‖ ≤
      ((u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod * c) / gN (sgs p g) ^ A := by
    rw [le_div_iff₀ hgA]
    linarith [hbd]
  refine h1.trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left hp hc0))
  rw [Real.rpow_neg hN.le]
  field_simp
end Formalism.FourierDecayAlt.P.JFxDs2
