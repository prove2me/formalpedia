-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.intertwinerConjugation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:46:48.670201+00:00
-- url     : https://prove2.me/submissions/16e59e1d-39ba-475e-a2dc-f9a83da88d1f

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_I_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_add_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_sub_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_add_comm0
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_sub_comm0
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_Ar_inter
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_Avr_inter
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_mem_c
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_mem_ci
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_mem_cb
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_mem_cbi
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RuleSS_mem___1e86e0c78ac8
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RuleSS_mem__b_cce97eb16fae
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_mem_GG
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_mem_GGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_comm_ofFn
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_comm_fns_D
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_p_Dr
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_p_Dri
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_pb_Drb
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_pb_Drbi
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_leftCorrection_intertwine
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_dualCorrection_intertwine
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_lin_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_four_inter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleSS
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)
namespace Formalism.FourierDecayAlt.P.RuleSS
namespace _root_.Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.R.RuleSS := by
  intro A _ _ r L SS SSs hSf hSp hSpb hSn hSns hTf hTp hTpb hTn hTns Y
  have DD : ∀ {x : A}, x ∈ L.fns → Commute x L.Dr ∧ Commute x L.Dri ∧ Commute x L.Drb ∧ Commute x L.Drbi :=
    fun hx => comm_fns_D L hx

  have cDrDrb : Commute L.Dr L.Drb := (comm_ofFn fun m => ((DD (mem_c L m)).2.2.1).symm).symm
  have cDrDri : Commute L.Dr L.Dri := (comm_ofFn fun m => ((DD (mem_c L m)).2.1).symm).symm
  have cDrDrbi : Commute L.Dr L.Drbi := (comm_ofFn fun m => ((DD (mem_c L m)).2.2.2).symm).symm
  have cDrbDri : Commute L.Drb L.Dri := (comm_ofFn fun m => ((DD (mem_cb L m)).2.1).symm).symm
  have cDrbDrbi : Commute L.Drb L.Drbi := (comm_ofFn fun m => ((DD (mem_cb L m)).2.2.2).symm).symm

  have sDrb := four_inter L L.Drb Y Y Y Y Y (Y - 1) Y Y
    (Ar_inter L _ Y Y (fun l => add_comm0 (comm_ofFn fun m => L.p_cb l m) Y)
      (fun l => (DD (mem_c L l)).2.2.1.eq) (fun l => (DD (mem_ci L l)).2.2.1.eq)).1
    (Ar_inter L _ Y Y (fun l => add_comm0 (comm_ofFn fun m => L.p_cb l m) Y)
      (fun l => (DD (mem_c L l)).2.2.1.eq) (fun l => (DD (mem_ci L l)).2.2.1.eq)).2
    (leftCorrection_intertwine L (comm_ofFn fun m => L.nab_cb m) (DD (mem_ζb L)).2.2.1 (DD (mem_GGi L)).2.2.1 Y)
    (Avr_inter L _ Y (Y - 1) (fun l => sub_shift (pb_Drb L l) Y (Y - 1) rfl)
      (fun l => (DD (mem_cb L l)).2.2.1.eq) (fun l => (DD (mem_cbi L l)).2.2.1.eq)).1
    (Avr_inter L _ Y (Y - 1) (fun l => sub_shift (pb_Drb L l) Y (Y - 1) rfl)
      (fun l => (DD (mem_cb L l)).2.2.1.eq) (fun l => (DD (mem_cbi L l)).2.2.1.eq)).2
    (dualCorrection_intertwine L (comm_ofFn fun m => L.nabs_cb m) (DD (mem_ζ L)).2.2.1 (DD (mem_GGi L)).2.2.1 Y)
    cDrDrb (Commute.refl _) (DD (mem_GG L)).2.2.1

  have sDri := four_inter L L.Dri Y (Y - 1) Y Y (Y - 1) (Y - 1) Y Y
    (Ar_inter L _ Y (Y - 1) (fun l => add_shift (p_Dri L l) Y (Y - 1) (by ring))
      (fun l => (DD (mem_c L l)).2.1.eq) (fun l => (DD (mem_ci L l)).2.1.eq)).1
    (Ar_inter L _ Y (Y - 1) (fun l => add_shift (p_Dri L l) Y (Y - 1) (by ring))
      (fun l => (DD (mem_c L l)).2.1.eq) (fun l => (DD (mem_ci L l)).2.1.eq)).2
    (leftCorrection_intertwine L (comm_ofFn fun m => L.nab_ci m) (DD (mem_ζb L)).2.1 (DD (mem_GGi L)).2.1 Y)
    (Avr_inter L _ (Y - 1) (Y - 1) (fun l => sub_comm0 (comm_ofFn fun m => L.pb_ci l m) _)
      (fun l => (DD (mem_cb L l)).2.1.eq) (fun l => (DD (mem_cbi L l)).2.1.eq)).1
    (Avr_inter L _ (Y - 1) (Y - 1) (fun l => sub_comm0 (comm_ofFn fun m => L.pb_ci l m) _)
      (fun l => (DD (mem_cb L l)).2.1.eq) (fun l => (DD (mem_cbi L l)).2.1.eq)).2
    (dualCorrection_intertwine L (comm_ofFn fun m => L.nabs_ci m) (DD (mem_ζ L)).2.1 (DD (mem_GGi L)).2.1 Y)
    cDrDri cDrbDri (DD (mem_GG L)).2.1

  have hlS : L.l0 Y * SS = SS * L.l0 (Y - 1) := by
    unfold LevelData.l0
    exact lin_shift _ _ _ (Y + 1/2) (Y - 1 + 1/2) (-1)
      (by rw [hSn, map_neg, map_one, neg_one_mul, sub_eq_add_neg])
      (Commute.mul_left (hSf _ (mem_ζb L)) (hSf _ (mem_GGi L))).eq (by ring)
  have hmS : L.m0 Y * SS = SS * L.m0 (Y - 1) := by
    unfold LevelData.m0
    exact lin_shift _ _ _ (Y - 1/2) (Y - 1 - 1/2) (-1)
      (by rw [hSns, map_neg, map_one, neg_one_mul, sub_eq_add_neg])
      (Commute.mul_left (hSf _ (mem_ζ L)) (hSf _ (mem_GGi L))).eq (by ring)
  have sSS := four_inter L SS (Y - 1) (Y - 1) Y (Y - 1) (Y - 1) (Y - 1) Y (Y - 1)
    (Ar_inter L SS (Y - 1) (Y - 1) (fun l => add_comm0 (hSp l) _)
      (fun l => hSf _ (mem_c L l)) (fun l => hSf _ (mem_ci L l))).1
    (Ar_inter L SS (Y - 1) (Y - 1) (fun l => add_comm0 (hSp l) _)
      (fun l => hSf _ (mem_c L l)) (fun l => hSf _ (mem_ci L l))).2
    hlS
    (Avr_inter L SS (Y - 1) (Y - 1) (fun l => sub_comm0 (hSpb l) _)
      (fun l => hSf _ (mem_cb L l)) (fun l => hSf _ (mem_cbi L l))).1
    (Avr_inter L SS (Y - 1) (Y - 1) (fun l => sub_comm0 (hSpb l) _)
      (fun l => hSf _ (mem_cb L l)) (fun l => hSf _ (mem_cbi L l))).2
    hmS
    (comm_ofFn fun m => (hSf _ (mem_c L m)).symm).symm
    (comm_ofFn fun m => (hSf _ (mem_cb L m)).symm).symm (hSf _ (mem_GG L))

  have hlT : L.l0 Y * SSs = SSs * L.l0 (Y + 1) := by
    unfold LevelData.l0
    exact lin_shift _ _ _ (Y + 1/2) (Y + 1 + 1/2) 1
      (by rw [hTn, map_one, one_mul])
      (Commute.mul_left (hTf _ (mem_ζb L)) (hTf _ (mem_GGi L))).eq (by ring)
  have hmT : L.m0 Y * SSs = SSs * L.m0 (Y + 1) := by
    unfold LevelData.m0
    exact lin_shift _ _ _ (Y - 1/2) (Y + 1 - 1/2) 1
      (by rw [hTns, map_one, one_mul])
      (Commute.mul_left (hTf _ (mem_ζ L)) (hTf _ (mem_GGi L))).eq (by ring)
  have sSSs := four_inter L SSs Y Y Y (Y + 1) Y Y Y (Y + 1)
    (Ar_inter L SSs Y Y (fun l => add_comm0 (hTp l) _)
      (fun l => hTf _ (mem_c L l)) (fun l => hTf _ (mem_ci L l))).1
    (Ar_inter L SSs Y Y (fun l => add_comm0 (hTp l) _)
      (fun l => hTf _ (mem_c L l)) (fun l => hTf _ (mem_ci L l))).2
    hlT
    (Avr_inter L SSs Y Y (fun l => sub_comm0 (hTpb l) _)
      (fun l => hTf _ (mem_cb L l)) (fun l => hTf _ (mem_cbi L l))).1
    (Avr_inter L SSs Y Y (fun l => sub_comm0 (hTpb l) _)
      (fun l => hTf _ (mem_cb L l)) (fun l => hTf _ (mem_cbi L l))).2
    hmT
    (comm_ofFn fun m => (hTf _ (mem_c L m)).symm).symm
    (comm_ofFn fun m => (hTf _ (mem_cb L m)).symm).symm (hTf _ (mem_GG L))

  have sDr := four_inter L L.Dr Y (Y + 1) (Y + 1) (Y + 1) Y Y (Y + 1) (Y + 1)
    (Ar_inter L _ Y (Y + 1) (fun l => add_shift (p_Dr L l) Y (Y + 1) rfl)
      (fun l => (DD (mem_c L l)).1.eq) (fun l => (DD (mem_ci L l)).1.eq)).1
    (Ar_inter L _ Y (Y + 1) (fun l => add_shift (p_Dr L l) Y (Y + 1) rfl)
      (fun l => (DD (mem_c L l)).1.eq) (fun l => (DD (mem_ci L l)).1.eq)).2
    (leftCorrection_intertwine L (comm_ofFn fun m => L.nab_c m) (DD (mem_ζb L)).1 (DD (mem_GGi L)).1 (Y + 1))
    (Avr_inter L _ Y Y (fun l => sub_comm0 (comm_ofFn fun m => L.pb_c l m) _)
      (fun l => (DD (mem_cb L l)).1.eq) (fun l => (DD (mem_cbi L l)).1.eq)).1
    (Avr_inter L _ Y Y (fun l => sub_comm0 (comm_ofFn fun m => L.pb_c l m) _)
      (fun l => (DD (mem_cb L l)).1.eq) (fun l => (DD (mem_cbi L l)).1.eq)).2
    (dualCorrection_intertwine L (comm_ofFn fun m => L.nabs_c m) (DD (mem_ζ L)).1 (DD (mem_GGi L)).1 (Y + 1))
    (Commute.refl _) cDrDrb.symm (DD (mem_GG L)).1

  have sDrbi := four_inter L L.Drbi (Y + 1) (Y + 1) (Y + 1) (Y + 1) Y (Y + 1) (Y + 1) (Y + 1)
    (Ar_inter L _ (Y + 1) (Y + 1) (fun l => add_comm0 (comm_ofFn fun m => L.p_cbi l m) _)
      (fun l => (DD (mem_c L l)).2.2.2.eq) (fun l => (DD (mem_ci L l)).2.2.2.eq)).1
    (Ar_inter L _ (Y + 1) (Y + 1) (fun l => add_comm0 (comm_ofFn fun m => L.p_cbi l m) _)
      (fun l => (DD (mem_c L l)).2.2.2.eq) (fun l => (DD (mem_ci L l)).2.2.2.eq)).2
    (leftCorrection_intertwine L (comm_ofFn fun m => L.nab_cbi m) (DD (mem_ζb L)).2.2.2 (DD (mem_GGi L)).2.2.2 (Y + 1))
    (Avr_inter L _ Y (Y + 1) (fun l => sub_shift (pb_Drbi L l) Y (Y + 1) (by ring))
      (fun l => (DD (mem_cb L l)).2.2.2.eq) (fun l => (DD (mem_cbi L l)).2.2.2.eq)).1
    (Avr_inter L _ Y (Y + 1) (fun l => sub_shift (pb_Drbi L l) Y (Y + 1) (by ring))
      (fun l => (DD (mem_cb L l)).2.2.2.eq) (fun l => (DD (mem_cbi L l)).2.2.2.eq)).2
    (dualCorrection_intertwine L (comm_ofFn fun m => L.nabs_cbi m) (DD (mem_ζ L)).2.2.2 (DD (mem_GGi L)).2.2.2 (Y + 1))
    cDrDrbi cDrbDrbi (DD (mem_GG L)).2.2.2
  obtain ⟨a1, b1, c1, d1⟩ := sDrb
  obtain ⟨a2, b2, c2, d2⟩ := sDri
  obtain ⟨a3, b3, c3, d3⟩ := sSS
  obtain ⟨a4, b4, c4, d4⟩ := sSSs
  obtain ⟨a5, b5, c5, d5⟩ := sDr
  obtain ⟨a6, b6, c6, d6⟩ := sDrbi
  exact ⟨I_comp (I_comp a1 a2) a3, I_comp (I_comp b1 b2) b3, I_comp (I_comp c1 c2) c3,
    I_comp (I_comp d1 d2) d3, I_comp a4 (I_comp a5 a6), I_comp b4 (I_comp b5 b6),
    I_comp c4 (I_comp c5 c6), I_comp d4 (I_comp d5 d6)⟩
end _root_.Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P.RuleSS
