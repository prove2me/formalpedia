-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.slope_bound_single_lift_of_definitions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:51:14.38414+00:00
-- url     : https://prove2.me/submissions/8d5f66c7-8f53-4444-948d-c275b1992410

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_IndefiniteTreeX
import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeFullAssemblyWeighted
import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_SlopeBoundSingleLiftOfDefinitions
import Theorems.Thm_Formalism_L2_Indef_Tree_cut_lines
import Theorems.Thm_Formalism_L2_Indef_Tree_period_of_leaves
import Theorems.Thm_Formalism_L2_Indef_Tree_exp_neg_le_twelfth
import Theorems.Thm_Formalism_L2_Indef_Tree_cfl_Q
import Theorems.Thm_Formalism_L2_Indef_Tree_g_Q
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_main
import Theorems.Thm_Formalism_ExtensionFiltration_covolume_assembly_weighted
import Theorems.Thm_UpperTheory_Reformulated_B_SelectionLemmas_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module NumberField Formalism.HN
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
attribute [instance] SlopeBoundParameters.fPl SlopeBoundParameters.dimNeZero
attribute [instance] SlopeBoundLiftData.fι SlopeBoundLiftData.nι
set_option maxHeartbeats 1000000
namespace Formalism.L2.Indef.Tree
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (Ca Cb Cf Cc C1 Cm Cn : ℝ) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCf : 0 ≤ Cf) (hCc : 0 ≤ Cc) (hC1 : 0 ≤ C1)
    (hCm : 0 ≤ Cm) (d D : ℕ) (hD : 0 < D) (hdD : d = D) (XW XWr : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (M : Submodule (𝓞 K) (Fin d → K)) (hM : Submodule.IsLattice K M) (P : SlopeBoundParameters) (F : SlopeBoundLiftData K P)
    (hKL : LeafKL P) (hCN : LeafCN P) (hFE : LeafFE P) (hDi : LeafDiff P) (hNo : LeafNorm P)
    (hPg : PageParams P) (hFa : FacParams Cf F) (hDF : LeafDegFlat Cc F) (hEx : LeafExport Cf F)
    (hCu : LeafCut F) (hSB : LeafShareBad F) (hBR : LeafBadRows F) (hMN : LeafMuN F) (hLa : LeafLam F)
    (hRe : LeafRecord XWr M F) (hN2 : LeafNote2 Cn F) (hMe : LeafMeasure Cm (D := D) XW XWr M P)
    (hq : F.q' = 0) (hDe : LeafDef C1 Cf F) :
    Formalism.DivisionValues.lcv XW M / (D : ℝ) ≤ F.main + slopeBoundConstant Ca Cb Cf Cc C1 Cm * (P.B0 * P.llx) := by
  obtain ⟨-, -, -, hx, heps, hrd4, hv2, hv, hlrd, hLc, hlx, hllx, hx7, hcard, hm, hf, hk, hkS, hkη, hS, hR, hkR,
    hGP, hPPpp, hPPdef⟩ := hPg
  obtain ⟨hwt, hU, hw, hsh, hpq, hq0, hq1, hkap, hCLk, hδb, hn2b⟩ := hFa
  obtain ⟨-, hper⟩ := period_of_leaves P hKL hCN hFE hDi hNo hv hv2 hrd4 hLc hx
  obtain ⟨hNfg, hMkfg, hN0, hXN, hg1, hee, hsa, hint, hNM, hlogg⟩ := hCu
  obtain ⟨hδ0, hδx⟩ := hSB
  obtain ⟨hXWr, hmes⟩ := hMe
  obtain ⟨hrec, ho'⟩ := hRe
  obtain ⟨hn20, -⟩ := hN2

  have hL0 : 0 ≤ P.L := Real.rpow_nonneg (by linarith) _
  have hb1 : 1 ≤ P.b := Real.one_le_exp hL0
  have hlrd0 : 0 ≤ Real.log P.rd := Real.log_nonneg (by linarith)
  have hδ12 : F.δ ≤ 1 / 12 := le_trans hδx (exp_neg_le_twelfth _ hx7)
  have hkap0 : 0 ≤ F.kap := by linarith
  have hfN : 0 ≤ 20 * P.f * P.Nr ^ 2 * P.L := by positivity
  have hPPp0 : 0 ≤ P.PPp := by linarith
  have hQe : F.Q = 2 * (P.PPp * F.kap) + 2 * F.kap + 2 * (Real.log P.rd * F.kap) := by
    unfold SlopeBoundLiftData.Q SlopeBoundParameters.lrd; ring
  have hlk : 0 ≤ Real.log P.rd * F.kap := mul_nonneg hlrd0 hkap0
  have hPk : 0 ≤ P.PPp * F.kap := mul_nonneg hPPp0 hkap0
  have hQ2 : 2 * P.PPp * F.kap ≤ F.Q := by rw [hQe]; linarith only [hlk, hkap0]
  have hQ0 : 0 ≤ F.Q := by linarith only [hQ2, hPk]
  have hcflQ : |2 * F.cfl Cf| ≤ F.Q := by
    rw [hQe]; exact cfl_Q _ _ _ _ _ hEx (mul_nonneg hCf hL0) hCLk hlk
  have hGQ : 2 * Real.log (F.g : ℝ) ≤ F.Q := le_trans (g_Q _ _ _ _ hlogg hGP hkap hPPp0) hQ2
  have hmuNQ : |F.muN| ≤ F.Q := le_trans hMN hQ2
  have hmmQ : F.mmax ≤ F.Q := le_trans hLa hQ2
  obtain ⟨hdN, hdNs, hdb, hcut⟩ := cut_lines K (Fin F.nN → K) (Fin F.nN) (Pi.basisFun K (Fin F.nN)) F.XN hXN
    F.NN F.Mk F.e F.g hNfg hMkfg hN0 hg1 hee hsa hint hNM
  have hδQ : 12 * F.δ * F.Q = 24 * F.δ * ((P.PPp + 1 + Real.log P.rd) * F.kap) := by
    unfold SlopeBoundLiftData.Q SlopeBoundParameters.lrd; ring
  have hDF' : ∀ τ, |F.c1 τ + F.pq * P.logOm / 2| ≤ Cc * F.q' * (Real.log P.rd + |P.Lc|) := fun τ =>
    le_trans (hDF τ) (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg P.Lc]) (mul_nonneg hCc hq0))
  have hB0 : 0 ≤ P.B0 := by
    unfold SlopeBoundParameters.B0
    have : 0 ≤ P.x ^ P.eps := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ P.f * P.m * P.b := by positivity
    positivity
  have hBl : 0 ≤ P.B0 * P.llx := mul_nonneg hB0 (by linarith)
  have hBl' : P.B0 ≤ P.B0 * P.llx := by nlinarith only [hB0, hllx]
  have hdbQ : ((rkK F.bad : ℕ) : ℝ) ≤ 3 * F.δ * ((rkK F.NN : ℕ) : ℝ) := hBR
  have hcfl0 : F.cfl Cf = (∑ τ, F.w τ * F.c1 τ) - Cf * P.L := by
    unfold SlopeBoundLiftData.cfl; rw [hq]; ring
  have hfirst : -(2 * (C1 * P.LL0 * (∑ τ, F.ua τ) + P.b / 4)) ≤ F.muN - 2 * F.cfl Cf := by
    have hU' : F.U = ∑ τ, F.ua τ := rfl
    unfold LeafDef at hDe
    rw [hU'] at hDe
    rw [hcfl0]
    linarith only [hDe, hPPdef]
  have key := Formalism.ExtensionFiltration.covolume_assembly_weighted K d D hD hdD XWr hXWr M hM P.Pl F.w F.w0 F.c1 F.ua
    (F.muN - 2 * F.cfl Cf) F.muN F.muN F.muG F.mmax 1 1 (rkK F.NN : ℝ) (rkK F.good : ℝ) (rkK F.bad : ℝ)
    C1 Cf Cc (F.cfl Cf) 0 F.δ F.Q 0 0 (2 * Real.log (F.g : ℝ)) (2 * (F.o' + F.n2))
    F.pq F.q' P.logOm P.x P.eps P.L P.b P.rd |P.Lc| P.llx P.LL0 P.B0 P.f P.m P.k P.S P.η P.a P.La P.R 1
    hfirst rfl (by linarith only) one_pos le_rfl (by norm_num) le_rfl le_rfl (by linarith only) hcflQ hQ0
    (by linarith only [hb1])
    hdN hdNs hdb hdbQ hδ0 hδ12 hcut hmuNQ hmmQ hGQ hrec
    (by rw [hδQ]; linarith only [hδb, ho', hPPpp, hn2b, hb1])
    hDF' hwt hU hw hkS hkη hcard hm hf hq0 hq1 hx heps rfl rfl (by linarith only [hrd4]) hlrd (abs_nonneg _) hLc
    hlx hllx rfl rfl hC1 hCf hCc hsh hS hR hkR hk hpq rfl rfl le_rfl (by rw [one_mul]; exact hper)
  have hc : 64 * (C1 + 3 * Cf) + 8 * Cc + 2 + 12 * 1 + Cm ≤ slopeBoundConstant Ca Cb Cf Cc C1 Cm := by
    unfold slopeBoundConstant; linarith only [hCa, hCb]
  have hc' := mul_le_mul_of_nonneg_right hc hBl
  have hm' : Cm * P.B0 ≤ Cm * (P.B0 * P.llx) := mul_le_mul_of_nonneg_left hBl' hCm
  show Formalism.DivisionValues.lcv XW M / (D : ℝ) ≤ (∑ σ, F.pq * F.w0 σ * P.logOm) + slopeBoundConstant Ca Cb Cf Cc C1 Cm * (P.B0 * P.llx)
  have e1 : (64 * (C1 + 3 * Cf) + 8 * Cc + 2 + 12 * 1) * P.B0 * P.llx + Cm * (P.B0 * P.llx) =
      (64 * (C1 + 3 * Cf) + 8 * Cc + 2 + 12 * 1 + Cm) * (P.B0 * P.llx) := by ring
  linarith only [key, hmes, hc', hm', e1]
end Formalism.L2.Indef.Tree
