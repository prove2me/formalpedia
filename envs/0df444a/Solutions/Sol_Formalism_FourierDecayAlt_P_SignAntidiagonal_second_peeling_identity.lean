-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.second_peeling_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:02:51.328043+00:00
-- url     : https://prove2.me/submissions/8bff08d0-319a-4e8a-a574-b089eff504b6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstPeelingMinorMemIdeal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPeelingMinorMemIdeal
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_herm_wsum
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_dpsi_e_w
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_first_peeling_minor_mem_ideal
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_hT_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_last_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_mem_gen
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_peel_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_succAbove_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_tm_offdiag
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_SignAntidiagonal_smul_mem__5661bbd89423
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution : PeelingCovector := by
  intro A _ _ k m z' yb E i u hz'
  have ha : xR k (m + 1) (m + 1) le_rfl = fun l : Fin (m + 1) => pe k (m + 1) l.val := by
    funext l; ext; simp only [xR, eI, Fin.val_castLE]; rw [pe_lt (by omega)]
  have hb : (fun l : Fin m => xR k (m + 1) (m + 1) le_rfl (i.succAbove l)) =
      fun l : Fin m => pe k (m + 1) (if l.val < i.val then l.val else l.val + 1) := by
    funext l; ext; simp only [xR, eI, Fin.val_castLE, succAbove_val, pe_val]; all_goals (split_ifs <;> omega)
  have hi : xR k (m + 1) i.val (by have := i.isLt; omega) = fun l : Fin i.val => pe k (m + 1) l.val := by
    funext l; ext; simp only [xR, eI, Fin.val_castLE]; rw [pe_lt (by omega)]
  rw [hb, ha, hi]
  have step := peel_col (Ideal.span (rgen k (m + 1) z' E)) E (fun w => herm (Hpk k (m + 1)) (bvec (wI k (m + 1) w)) yb)
    (fun l : Fin (m + 1) => pe k (m + 1) l.val) (fun l : Fin m => pe k (m + 1) (if l.val < i.val then l.val else l.val + 1))
    (wI k (m + 1)) u (herm (Hpk k (m + 1)) z' yb) (by
      intro l
      have := l.isLt
      apply hT_of _ _ _ (fun w => dpsiP k (m + 1) z' (pe k (m + 1) l.val) (wI k (m + 1) w))
      · intro w
        have hw := w.isLt
        have hne : pe k (m + 1) l.val ≠ wI k (m + 1) w := by
          intro h2; have h3 := congrArg Fin.val h2; rw [pe_lt (by omega)] at h3; simp only [wI] at h3; omega
        rw [tm_offdiag _ _ hne]
        apply mem_gen
        simp only [InNp, wI]; rw [pe_lt (by omega)]; omega
      · simp only [dpsi_e_w k (m + 1) z' l.val (by omega), last_iff]
        by_cases hl : l.val = m
        · have e : l.val + 1 = m + 1 := by omega
          simp only [e, if_true, hl]
          rw [herm_wsum k (m + 1) z' yb hz']
          congr 1; ext w; ring
        · have e : ¬ (l.val + 1 = m + 1) := by omega
          simp [e, hl])
  have hc : ((fun l : Fin (m + 1) => pe k (m + 1) l.val) ∘ Fin.castSucc) = fun l : Fin m => pe k (m + 1) l.val := by
    funext l; simp
  rw [hc] at step
  have h2 := smul_mem' _ (herm (Hpk k (m + 1)) z' yb) (first_peeling_minor_mem_ideal k (m + 1) z' E u m i.val (by omega) (by omega))
  have := Ideal.add_mem _ step h2
  rw [smul_sub] at this
  simpa using this
end Formalism.FourierDecayAlt.P.SignAntidiagonal
