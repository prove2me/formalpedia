-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr7.plusStep_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:09.653286+00:00
-- url     : https://prove2.me/submissions/9b2761aa-ce19-406a-9826-64ad16c032cd

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_comm_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_star_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_mul_mul_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_mat1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_mat2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_key_rel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_tri_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_io_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_io_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_free_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_free_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_free_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_free2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_comm2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_dg_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_dg_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_dg_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_dg_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_comm_dg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_comm_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_freeOf_smul_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_mul_rh0_apply_one_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_zfns_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_eU_mul_eU
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr7
open Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr7
theorem _root_.solution (hLP : LetterPlus) (hRTT : RTTEntries) (hForm : PlusForm) (hTau : PlusTau) (hPL : PlusL)
    (L : LevelData A r) (f : FrameData S A) (a : S) (Ya : ℂ) (h : PlusHyp L f a Ya) :
    IsFrame L (f.plus L a Ya) := by
  have hH := h
  obtain ⟨hstar, hf, hfree, hYa, hYaI, hYa1I, hq⟩ := h
  obtain ⟨fRR, fTT, fF, fFi, fx, fxi, fc, fci, fee⟩ := hfree
  have xiYa := hf.x_xi Ya hYaI
  have xiYa1 := hf.x_xi (Ya + 1) hYa1I
  have hYaR : Ya ∈ f.reg := hf.inv_reg hYaI
  have xi_c : ∀ Y ∈ f.inv, Commute (f.xi Y) f.c := fun Y hY =>
    comm_inv (hf.x_xi Y hY).1 (hf.x_xi Y hY).2 (hf.x_c Y)
  have x_ci : ∀ Y, Commute (f.x Y) f.ci := fun Y =>
    (comm_inv hf.c_ci.1 hf.c_ci.2 (hf.x_c Y).symm).symm
  have xi_ci : ∀ Y ∈ f.inv, Commute (f.xi Y) f.ci := fun Y hY =>
    (comm_inv hf.c_ci.1 hf.c_ci.2 (xi_c Y hY).symm).symm
  have xi_x : ∀ Y ∈ f.inv, ∀ Y', Commute (f.xi Y) (f.x Y') := fun Y hY Y' =>
    comm_inv (hf.x_xi Y hY).1 (hf.x_xi Y hY).2 (hf.x_commute Y Y')
  have xi_fn : ∀ Y ∈ f.inv, ∀ g ∈ zfns L, Commute (f.xi Y) (io g) := fun Y hY g hg =>
    comm_inv (hf.x_xi Y hY).1 (hf.x_xi Y hY).2 (hf.x_fn Y g hg)
  have hl : FreeOf a (f.l L Ya) := by
    simp only [FrameData.l, kapL]
    exact free_add (free_io a _) (free_mul (free_io a _) (fee Ya))
  have hs : ∀ (u v : SlopeTestRemainingChoices S A) (c d : ℂ), (c • u) * (d • v) = (c * d) • (u * v) := fun u v c d => by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hD12 : ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya] *
      ins a !![(f.q Ya)⁻¹ • f.x (Ya + 1), 0; 0, f.xi Ya] = 1 := by
    rw [dg_mul (free_smul _ (fxi _)) (fx _), hs, mul_inv_cancel₀ hq, one_smul, xiYa1.2, xiYa.1,
      dg_one]
  have hD21 : ins a !![(f.q Ya)⁻¹ • f.x (Ya + 1), 0; 0, f.xi Ya] *
      ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya] = 1 := by
    rw [dg_mul (free_smul _ (fx _)) (fxi _), hs, inv_mul_cancel₀ hq, one_smul, xiYa1.1, xiYa.2,
      dg_one]
  have diagonalShiftOneMinus : Commute f.c (ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya]) :=
    comm_dg fc ((xi_c (Ya + 1) hYa1I).symm.smul_right _) (hf.x_c Ya).symm
  have ciD1 : Commute f.ci (ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya]) :=
    comm_dg fci ((xi_ci (Ya + 1) hYa1I).symm.smul_right _) (x_ci Ya).symm
  have cD2 : Commute f.c (ins a !![(f.q Ya)⁻¹ • f.x (Ya + 1), 0; 0, f.xi Ya]) :=
    comm_dg fc ((hf.x_c (Ya + 1)).symm.smul_right _) (xi_c Ya hYaI).symm
  have assoc4 : ∀ u v w x : SlopeTestRemainingChoices S A, u * v * (w * x) = u * (v * w) * x := fun _ _ _ _ => by
    simp only [mul_assoc]
  refine
    { module := hLP ℂ A S f.reg f.RR f.TT f.q a Ya hf.module fRR fTT hYaR hYa
      lowerLeftEntry_commute := ?_
      inv_reg := fun Y hY => ⟨hf.inv_reg hY.1, hY.2.2⟩
      F_Fi := ?_
      Fi_F := ?_
      x_xi := ?_
      c_ci := ⟨mul_mul_one hf.c_ci.1 hD12 ciD1.symm, mul_mul_one hf.c_ci.2 hD21 cD2.symm⟩
      x_commute := ?_
      x_c := ?_
      x_fn := ?_
      x_nab := ?_
      c_fn := ?_
      x_star := ?_
      c_star := ?_
      ee_fn := ?_
      form := hForm A S r L f a Ya hH
      frame_τ := hTau A S r L f a Ya hH
      frame_l := hPL A S r L f a Ya hH }
  · intro Y hY Y' hY'
    show Commute ((f.TT Y * Rh0 a (Y - Ya) : M2 (SlopeTestRemainingChoices S A)) 1 0)
      ((f.TT Y' * Rh0 a (Y' - Ya) : M2 (SlopeTestRemainingChoices S A)) 1 0)
    rw [mul_rh0_apply_one_zero, mul_rh0_apply_one_zero]
    by_cases hYY : Y = Y'
    · subst hYY
      exact Commute.refl _
    have hee : (eU a 0 0 : SlopeTestRemainingChoices S A) * eU a 0 0 = eU a 0 0 := by rw [eU_mul_eU]; simp
    have hen : (eU a 0 0 : SlopeTestRemainingChoices S A) * eU a 0 1 = eU a 0 1 := by rw [eU_mul_eU]; simp
    have hne : (eU a 0 1 : SlopeTestRemainingChoices S A) * eU a 0 0 = 0 := by rw [eU_mul_eU]; simp
    have hnn : (eU a 0 1 : SlopeTestRemainingChoices S A) * eU a 0 1 = 0 := by rw [eU_mul_eU]; simp
    have K := key_rel _ _ _ _ Y Y' Ya hYY
      (hRTT ℂ (SlopeTestRemainingChoices S A) f.TT Y' Y (hf.module.rtt Y' hY'.1 Y hY.1) 1 1 1 0)
      (hRTT ℂ (SlopeTestRemainingChoices S A) f.TT Y Y' (hf.module.rtt Y hY.1 Y' hY'.1) 1 1 1 0)
    exact ((tri_comm _ _ _ _ (eU a 0 0) (eU a 0 1) (Y - Ya) (Y' - Ya) hee hen hne hnn
      (fTT Y 1 0 0 0).eq (fTT Y' 1 0 0 0).eq (fTT Y 1 1 0 0).eq (fTT Y' 1 1 0 0).eq
      (fTT Y 1 0 0 1).eq (fTT Y' 1 0 0 1).eq (fTT Y 1 1 0 1).eq (fTT Y' 1 1 0 1).eq
      (hf.lowerLeftEntry_commute Y hY.1 Y' hY'.1).eq K).smul_left _).smul_right _
  · have hM : FreeOf2 a (!![io L.ζi, 0; 0, io L.ζbi] * !![1, 0; io L.GG * f.l L Ya, io L.GG] :
        M2 (SlopeTestRemainingChoices S A)) :=
      freeOf2_mul (free2 (free_io a _) free_zero free_zero (free_io a _))
        (free2 free_one free_zero (free_mul (free_io a _) hl) (free_io a _))
    show ins a _ * f.F * (f.Fi * ins a _) = 1
    rw [assoc4, hf.F_Fi, mul_one, ← ins_mul a _ _ hM,
      mat1 (io L.ζ) (io L.ζi) (io L.ζb) (io L.ζbi) (io L.GG) (io L.GGi) (f.l L Ya)
        (io_inv L.ζi_ζ) (io_inv L.ζbi_ζb) (io_inv L.GG_GGi), ins_one]
  · have hN : FreeOf2 a (!![1, 0; -f.l L Ya, io L.GGi] * !![io L.ζ, 0; 0, io L.ζb] :
        M2 (SlopeTestRemainingChoices S A)) :=
      freeOf2_mul (free2 free_one free_zero (free_neg hl) (free_io a _))
        (free2 (free_io a _) free_zero free_zero (free_io a _))
    show f.Fi * ins a _ * (ins a _ * f.F) = 1
    rw [assoc4, ← ins_mul a _ _ hN,
      mat2 (io L.ζ) (io L.ζi) (io L.ζb) (io L.ζbi) (io L.GG) (io L.GGi) (f.l L Ya)
        (io_inv L.ζ_ζi) (io_inv L.ζb_ζbi) (io_inv L.GGi_GG), ins_one, mul_one, hf.Fi_F]
  · intro Y hY
    obtain ⟨hYI, hY0, hY1⟩ := hY
    have hY1' : Y - Ya - 1 ≠ 0 := sub_ne_zero.mpr hY1
    have hab : ((Y - Ya) / (Y - Ya - 1)) * ((Y - Ya - 1) / (Y - Ya)) = 1 := by
      field_simp
    have hba : ((Y - Ya - 1) / (Y - Ya)) * ((Y - Ya) / (Y - Ya - 1)) = 1 := by
      rw [mul_comm]; exact hab
    have d1 : ins a !![((Y - Ya) / (Y - Ya - 1)) • (1 : SlopeTestRemainingChoices S A), 0; 0, 1] *
        ins a !![((Y - Ya - 1) / (Y - Ya)) • (1 : SlopeTestRemainingChoices S A), 0; 0, 1] = 1 := by
      rw [dg_mul (freeOf_smul_one _) free_one, hs, hab, one_smul, one_mul, dg_one]
    have d2 : ins a !![((Y - Ya - 1) / (Y - Ya)) • (1 : SlopeTestRemainingChoices S A), 0; 0, 1] *
        ins a !![((Y - Ya) / (Y - Ya - 1)) • (1 : SlopeTestRemainingChoices S A), 0; 0, 1] = 1 := by
      rw [dg_mul (freeOf_smul_one _) free_one, hs, hba, one_smul, one_mul, dg_one]
    exact ⟨mul_mul_one (hf.x_xi Y hYI).1 d1 (comm_sc (fxi Y) _).symm,
      mul_mul_one (hf.x_xi Y hYI).2 d2 (comm_sc (fx Y) _).symm⟩
  · intro Y Y'
    exact ((hf.x_commute Y Y').mul_right (comm_sc (fx Y) _)).mul_left
      ((comm_sc (fx Y') _).symm.mul_right (dg_comm (freeOf_smul_one _) free_one (freeOf_smul_one _) free_one
        (((Commute.refl (1 : SlopeTestRemainingChoices S A)).smul_left _).smul_right _) (Commute.refl 1)))
  · intro Y
    exact ((hf.x_c Y).mul_right (comm_dg (fx Y) ((xi_x (Ya + 1) hYa1I Y).symm.smul_right _)
        (hf.x_commute Y Ya))).mul_left
      ((comm_sc fc _).symm.mul_right (dg_comm (freeOf_smul_one _) free_one (free_smul _ (fxi _)) (fx _)
        ((Commute.one_left _).smul_left _) (Commute.one_left _)))
  · intro Y g hg
    exact (hf.x_fn Y g hg).mul_left (comm_sc (free_io a g) _).symm
  · intro Y
    exact (hf.x_nab Y).mul_left (comm_sc (free_io a _) _).symm
  · intro g hg
    exact (hf.c_fn g hg).mul_left (comm_dg (free_io a g)
      ((xi_fn (Ya + 1) hYa1I g hg).symm.smul_right _) (hf.x_fn Ya g hg).symm).symm
  · intro Y hY
    have hα : star ((Y - Ya) / (Y - Ya - 1)) = (Y - Ya) / (Y - Ya - 1) := by
      simp [hY, hYa]
    show star (f.x Y * ins a !![((Y - Ya) / (Y - Ya - 1)) • (1 : SlopeTestRemainingChoices S A), 0; 0, 1]) =
      f.x Y * ins a !![((Y - Ya) / (Y - Ya - 1)) • (1 : SlopeTestRemainingChoices S A), 0; 0, 1]
    rw [star_mul, dg_star (freeOf_smul_one _) free_one, star_smul, star_one, hα, hf.x_star Y hY]
    exact (comm_sc (fx Y) _).eq.symm
  · have hqR : star (f.q Ya) = f.q Ya := hf.module.q_real Ya hYa
    have hxi1 : star (f.xi (Ya + 1)) = f.xi (Ya + 1) :=
      star_inv xiYa1.1 (hf.x_star (Ya + 1) (by simp [hYa]))
    show star (f.c * ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya]) =
      f.c * ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya]
    rw [star_mul, dg_star (free_smul _ (fxi _)) (fx _), star_smul, hqR, hxi1, hf.x_star Ya hYa,
      hf.c_star]
    exact diagonalShiftOneMinus.eq.symm
  · intro Y g hg
    have hz : L.ζbi ∈ zfns L := by simp [zfns]
    have htz : Commute (io g : SlopeTestRemainingChoices S A) (tz L) := by
      unfold tz
      exact io_comm (by rw [mul_smul_comm, smul_mul_assoc, zfns_comm L hg hz])
    have hDD : Commute (io g : SlopeTestRemainingChoices S A) (f.DD Y Ya) := by
      unfold FrameData.DD
      exact ((hf.ee_fn Y g hg).symm.sub_right (hf.ee_fn Ya g hg).symm).smul_right _
    exact (ins_comm a _ (io g) (free_io a g)
      (comm2 (((hf.ee_fn Y g hg).symm.sub_right hDD).add_right htz)
        ((Commute.one_right _).smul_right _).neg_right (Commute.zero_right _)
        (((xi_fn Ya hYaI g hg).symm.mul_right (hf.ee_fn Y g hg).symm).mul_right
          (hf.x_fn Ya g hg).symm))).symm
end Formalism.FourierDecayAlt.P.Fr7
