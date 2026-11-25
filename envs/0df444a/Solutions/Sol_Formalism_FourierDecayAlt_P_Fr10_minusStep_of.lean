-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr10.minusStep_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:57.890326+00:00
-- url     : https://prove2.me/submissions/0690ce56-5caa-44c8-8960-b1ef94672d72

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_comm_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_star_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_t21_commutator_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_io_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_free_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_free_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_freeOf2_of_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_comm_lit
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_ins_comm_ins
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_comm_mul_ins
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_comm_mul_ins_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_inv_mul_ins
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_star_mul_ins
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_diag_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_diag_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_diag_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_Rht0_mul_10
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_free_m
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_tri_mul
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr10_tri_mul__7132e1048a78
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_freeOf2_diag_scalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_comm_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_sc_comm_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_lit_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_sc_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr10
open Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr10
theorem _root_.solution (hLM : LetterMinus) (hRTT : RTTEntries) (hForm : MinusForm) (hTau : MinusTau)
    (hL : MinusL) : MinusStep := by
  intro A S _ _ _ _ _ _ r L f b Yb h
  obtain ⟨hSL, hF, hFree, hYb, hb, hb1, hbm, hq⟩ := h
  have hFree' := hFree
  obtain ⟨fRR, fTT, fF, fFi, fx, fxi, fc, fci, fee⟩ := hFree
  obtain ⟨xb1, xb2⟩ := hF.x_xi Yb hb
  obtain ⟨xm1, xm2⟩ := hF.x_xi (Yb - 1) hbm
  have hYm : star (Yb - 1) = Yb - 1 := by rw [star_sub, hYb, star_one]

  have fC : FreeOf2 b (!![f.q (Yb - 1) • f.xi (Yb - 1), 0; 0, f.x Yb] : M2 (SlopeTestRemainingChoices S A)) :=
    freeOf2_of_entries (free_smul _ (fxi _)) (free_zero b) (free_zero b) (fx _)
  have fCi : FreeOf2 b (!![(f.q (Yb - 1))⁻¹ • f.x (Yb - 1), 0; 0, f.xi Yb] : M2 (SlopeTestRemainingChoices S A)) :=
    freeOf2_of_entries (free_smul _ (fx _)) (free_zero b) (free_zero b) (fxi _)
  have cC : ∀ w : SlopeTestRemainingChoices S A, (∀ Y, Commute (f.x Y) w) →
      ∀ i j, Commute w ((!![f.q (Yb - 1) • f.xi (Yb - 1), 0; 0, f.x Yb] : M2 (SlopeTestRemainingChoices S A)) i j) := fun w hw =>
    comm_lit ((comm_inv xm1 xm2 (hw _)).symm.smul_right _) (Commute.zero_right w) (Commute.zero_right w)
      (hw _).symm
  have cCi : ∀ w : SlopeTestRemainingChoices S A, (∀ Y, Commute (f.x Y) w) →
      ∀ i j, Commute w ((!![(f.q (Yb - 1))⁻¹ • f.x (Yb - 1), 0; 0, f.xi Yb] : M2 (SlopeTestRemainingChoices S A)) i j) := fun w hw =>
    comm_lit ((hw _).symm.smul_right _) (Commute.zero_right w) (Commute.zero_right w)
      (comm_inv xb1 xb2 (hw _)).symm
  have x_ci : ∀ Y, Commute (f.x Y) f.ci := fun Y => (comm_inv hF.c_ci.1 hF.c_ci.2 (hF.x_c Y).symm).symm
  have fE : FreeOf2 b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG] : M2 (SlopeTestRemainingChoices S A)) :=
    freeOf2_mul (freeOf2_of_entries (free_io b _) (free_zero b) (free_zero b) (free_io b _))
      (freeOf2_of_entries (free_one b) (free_zero b) (free_mul (free_io b _) (free_m L f hFree' _)) (free_io b _))
  have fEi : FreeOf2 b (!![1, 0; -f.m L Yb, io L.GGi] * !![io L.ζb, 0; 0, io L.ζ] : M2 (SlopeTestRemainingChoices S A)) :=
    freeOf2_mul (freeOf2_of_entries (free_one b) (free_zero b) (free_neg (free_m L f hFree' _)) (free_io b _))
      (freeOf2_of_entries (free_io b _) (free_zero b) (free_zero b) (free_io b _))
  refine
    { module := hLM ℂ A S f.reg f.RR f.TT f.q b Yb hF.module fRR fTT (hF.inv_reg hb) hYb
      lowerLeftEntry_commute := ?_
      inv_reg := fun Y hY => ⟨hF.inv_reg hY.1, hY.2.2⟩
      F_Fi := ?_
      Fi_F := ?_
      x_xi := ?_
      c_ci := ⟨?_, ?_⟩
      x_commute := ?_
      x_c := ?_
      x_fn := ?_
      x_nab := ?_
      c_fn := ?_
      x_star := ?_
      c_star := ?_
      ee_fn := ?_
      form := hForm A S r L f b Yb ⟨hSL, hF, hFree', hYb, hb, hb1, hbm, hq⟩
      frame_τ := hTau A S r L f b Yb ⟨hSL, hF, hFree', hYb, hb, hb1, hbm, hq⟩
      frame_l := hL A S r L f b Yb ⟨hSL, hF, hFree', hYb, hb, hb1, hbm, hq⟩ }
  ·
    intro Y hY Y' hY'
    show Commute ((Rht0 b (Yb - Y) * f.TT Y : M2 (SlopeTestRemainingChoices S A)) 1 0) ((Rht0 b (Yb - Y') * f.TT Y' : M2 (SlopeTestRemainingChoices S A)) 1 0)
    by_cases hne : Y = Y'
    · subst hne; exact Commute.refl _
    rw [Rht0_mul_10, Rht0_mul_10]
    refine (Commute.smul_right ?_ _).smul_left _
    have ht := hF.lowerLeftEntry_commute Y hY.1 Y' hY'.1
    have r1 := hRTT ℂ (SlopeTestRemainingChoices S A) f.TT Y' Y (hF.module.rtt Y' hY'.1 Y hY.1) 0 0 1 0
    have r2 := hRTT ℂ (SlopeTestRemainingChoices S A) f.TT Y Y' (hF.module.rtt Y hY.1 Y' hY'.1) 0 0 1 0
    refine ins_comm_ins
      (freeOf2_of_entries (free_smul _ (fTT _ _ _)) (free_zero b) (free_neg (fTT _ _ _)) (free_smul _ (fTT _ _ _)))
      (freeOf2_of_entries (free_smul _ (fTT _ _ _)) (free_zero b) (free_neg (fTT _ _ _)) (free_smul _ (fTT _ _ _))) ?_
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    have e10 := t21_commutator_identity (f.TT Y 0 0) (f.TT Y 1 0) (f.TT Y' 0 0) (f.TT Y' 1 0) Y Y' Yb hne r1 r2
    refine lit_congr ?_ (by simp) e10 ?_
    · simp only [zero_mul, add_zero]
      exact ((ht.smul_left _).smul_right _).eq
    · simp only [mul_zero, zero_add]
      exact ((ht.smul_left _).smul_right _).eq
  · show ins b _ * f.F * (f.Fi * ins b _) = 1
    calc _ = ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG]) * (f.F * f.Fi) *
          ins b (!![1, 0; -f.m L Yb, io L.GGi] * !![io L.ζb, 0; 0, io L.ζ]) := by simp only [mul_assoc]
      _ = 1 := by rw [hF.F_Fi, mul_one, ← ins_mul b _ _ fE, tri_mul, ins_one]
  · show f.Fi * ins b _ * (ins b _ * f.F) = 1
    calc _ = f.Fi * (ins b (!![1, 0; -f.m L Yb, io L.GGi] * !![io L.ζb, 0; 0, io L.ζ]) *
          ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG])) * f.F := by
            simp only [mul_assoc]
      _ = 1 := by rw [← ins_mul b _ _ fEi, tri_mul', ins_one, mul_one, hF.Fi_F]
  · rintro Y ⟨hYi, h0, h1⟩
    obtain ⟨a1, a2⟩ := hF.x_xi Y hYi
    have h0' : Yb - Y ≠ 0 := h0
    have h1' : Yb - Y - 1 ≠ 0 := sub_ne_zero.mpr h1
    exact ⟨inv_mul_ins (fxi Y) (freeOf2_diag_scalar b _) a1 (comm_sc _ _) (sc_inv (by field_simp)),
      inv_mul_ins (fx Y) (freeOf2_diag_scalar b _) a2 (comm_sc _ _) (sc_inv (by field_simp))⟩
  · refine inv_mul_ins fci fC hF.c_ci.1 (cC f.ci x_ci) ?_
    rw [diag_mul, ← diag_one, xb1, smul_mul_smul_comm, xm2, mul_inv_cancel₀ hq, one_smul]
  · refine inv_mul_ins fc fCi hF.c_ci.2 (cCi f.c hF.x_c) ?_
    rw [diag_mul, ← diag_one, xb2, smul_mul_smul_comm, xm1, inv_mul_cancel₀ hq, one_smul]
  · intro Y Y'
    exact comm_mul_ins (fx Y) (fx Y') (freeOf2_diag_scalar b _) (freeOf2_diag_scalar b _) (hF.x_commute Y Y') (comm_sc _ _) (comm_sc _ _)
      (sc_comm_diag _ _ _)
  · intro Y
    exact comm_mul_ins (fx Y) fc (freeOf2_diag_scalar b _) fC (hF.x_c Y) (cC (f.x Y) (fun Y' => hF.x_commute Y' Y)) (comm_sc _ _)
      (sc_comm_diag _ _ _)
  · intro Y g hg
    exact comm_mul_ins_one (free_io b g) (hF.x_fn Y g hg) (comm_sc _ _)
  · intro Y
    exact comm_mul_ins_one (free_io b _) (hF.x_nab Y) (comm_sc _ _)
  · intro g hg
    exact comm_mul_ins_one (free_io b g) (hF.c_fn g hg) (cC (io g) (fun Y => hF.x_fn Y g hg))
  · intro Y hY
    refine star_mul_ins (fx Y) (freeOf2_diag_scalar b _) (hF.x_star Y hY) (comm_sc _ _) ?_
    rw [diag_star, star_smul, star_one, star_div₀, star_sub, star_sub, star_sub, hY, hYb, star_one]
  · refine star_mul_ins fc fC hF.c_star (cC f.c hF.x_c) ?_
    rw [diag_star, star_smul, hF.module.q_real _ hYm, star_inv xm1 (hF.x_star _ hYm), hF.x_star _ hYb]
  · intro Y g hg
    have gx : ∀ Y, Commute (io g) (f.x Y) := fun Y => (hF.x_fn Y g hg).symm
    have gb : Commute (io g) (f.xi Yb) := (comm_inv xb1 xb2 (hF.x_fn Yb g hg)).symm
    have gm : Commute (io g) (f.xi (Yb - 1)) := (comm_inv xm1 xm2 (hF.x_fn (Yb - 1) g hg)).symm
    have ge : ∀ Y, Commute (io g) (f.ee Y) := fun Y => (hF.ee_fn Y g hg).symm
    have gD : Commute (io g) (f.DD Y Yb) := ((ge Y).sub_right (ge Yb)).smul_right _
    have gt : Commute (io g : SlopeTestRemainingChoices S A) (tz L) := by
      have hz : L.ζbi ∈ zfns L := by simp [zfns]
      refine io_comm ?_
      rw [mul_smul_comm, smul_mul_assoc, L.fns_comm g (Or.inr hg) L.ζbi (Or.inr hz)]
    exact (ins_comm b _ (io g) (free_io b g) (comm_lit (ge Y) (Commute.zero_right _)
      ((gb.mul_right gm).smul_right _).neg_right
      ((((gb.mul_right (ge Y)).mul_right (gx Yb)).sub_right gD).add_right gt))).symm
end Formalism.FourierDecayAlt.P.Fr10
