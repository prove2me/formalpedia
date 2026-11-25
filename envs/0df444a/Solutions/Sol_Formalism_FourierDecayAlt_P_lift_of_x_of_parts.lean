-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lift_of_x_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:12:17.321417+00:00
-- url     : https://prove2.me/submissions/f7e3ca76-ba76-4158-9bfa-87ed34e1769e

import Definitions.Def_Formalism_HermitianCurvature_StatementTL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftOfXOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : TL.LiftXOfParts := by
  intro hZ _hC hX Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 hD Y
  obtain ⟨_, _, hAct, hQQ, _, _, _, hLS⟩ := hD
  obtain ⟨B0, _, hB⟩ := hX Wp Wq P Bs X
  obtain ⟨hFB, hEq, hRad⟩ := hB Y
  set E := xFib Bs B0 (Y + ((P.k : ℂ) - 2) / 2) with hE
  set s : ℂ := M.sgn P l0 with hs
  have hx : st.x Y = L.GGi * st.QQ Y 1 1 := by
    rw [hLS.tau, ← mul_assoc, L.GGi_GG, one_mul]
  have hx1 : (st.x Y).1 = X.fn 5 * (s • X.t Y 1 1) := by
    rw [hx, hQQ Y, hAct.2.2.2.2.2.2.2.2.2.2.2.1]
    rfl
  refine hZ Wp Wq P Bs 0 0 0 0 (fun _ => s) E (st.x Y) ?_ hFB ?_ ?_
  · refine ⟨MvPolynomial.C s, by simp, fun g => by simp⟩
  · intro p hp g hg J
    simp only [pow_zero, mul_one, smul_apply]
    rw [hEq p hp g hg J, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  · intro Φ x hx'
    simp only [pow_zero, mul_one, smul_apply]
    rw [hx1, Module.End.mul_apply, X.fn_apply 5 _ x hx', LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply,
      Pi.smul_apply, hRad Φ x hx', smul_smul, smul_smul]
    have hG : (0 : ℝ) < Q.GGl P.k P.r Bs.z Bs.z' x.2 := hx'.2.2
    simp only [Q.fnVal]
    congr 1
    have hG' : ((Q.GGl P.k P.r Bs.z Bs.z' x.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
    field_simp
end Formalism.FourierDecayAlt.P
