-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.qminor_Emir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:37:32.088388+00:00
-- url     : https://prove2.me/submissions/d8970d14-d3fc-4b93-a6cd-12881615921e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHeadV
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_Tm_Emir
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBG_ofFn_prod_smul__0bf769d4659b
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal
variable {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1))
    (u : ℂ) : qminor (Emir E) a b u =
      ((∏ i, ep (a i)) * (∏ i, ep (b i))) • qminor (Formalism.FourierDecayAlt.P.Qx5.Eop E) (rv ∘ a) (rv ∘ b) u := by
  unfold qminor
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Tm_Emir, ofFn_prod_smul', Function.comp_apply]
  rw [mul_smul_comm]
  congr 1
  rw [Finset.prod_mul_distrib, Equiv.prod_comp σ (fun i => ep (a i))]
end Formalism.FourierDecayAlt.P.PBG
