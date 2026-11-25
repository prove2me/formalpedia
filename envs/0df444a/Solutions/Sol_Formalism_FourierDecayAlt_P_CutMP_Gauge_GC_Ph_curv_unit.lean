-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph.curv_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:09:53.123886+00:00
-- url     : https://prove2.me/submissions/a58f7cc6-0364-46d8-a2f4-b9537b9ab5d4

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCHolPh
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ph_isOpen_annT
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ph_re_conj_fderiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ph_curv_alg
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ph_hasFDerivAt_star

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
theorem _root_.solution {TT : ℝ} {u : ℂ → ℂ} (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (AnnT TT))
    (h1 : ∀ ζ ∈ AnnT TT, ‖u ζ‖ = 1) {ζ : ℂ} (hζ : ζ ∈ AnnT TT) :
    (NF.dZb (fun w => star (u w) * NF.dZ u w) ζ).re = 0 := by
  have hs := isOpen_annT TT
  have hn : AnnT TT ∈ nhds ζ := hs.mem_nhds hζ
  have hud : ∀ w ∈ AnnT TT, DifferentiableAt ℝ u w := fun w hw =>
    (hu.differentiableOn (by simp)).differentiableAt (hs.mem_nhds hw)
  have hd2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ u) (AnnT TT) :=
    hu.fderiv_of_isOpen hs (by simp)
  have hDd : DifferentiableAt ℝ (fderiv ℝ u) ζ := (hd2.differentiableOn (by simp)).differentiableAt hn
  set S := fderiv ℝ (fderiv ℝ u) ζ with hS
  have hDv : ∀ v : ℂ, HasFDerivAt (fun w => fderiv ℝ u w v) (S.flip v) ζ := by
    intro v
    have := hDd.hasFDerivAt.clm_apply (hasFDerivAt_const v ζ)
    simpa using this
  have hsym : S 1 Complex.I = S Complex.I 1 :=
    ((hu.contDiffAt hn).isSymmSndFDerivAt (by (try simp); exact (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.2 le_top))) 1 Complex.I

  have h2 : ∀ k : ℂ, (star (fderiv ℝ u ζ k) * fderiv ℝ u ζ k + star (u ζ) * S k k).re = 0 := by
    intro k
    have hφ : HasFDerivAt (fun w => star (u w) * fderiv ℝ u w k)
        (star (u ζ) • S.flip k + fderiv ℝ u ζ k • Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ u ζ)) ζ :=
      (hasFDerivAt_star (hud ζ hζ)).mul (hDv k)
    have hre := Complex.reCLM.hasFDerivAt.comp ζ hφ
    have h0 : HasFDerivAt (Complex.reCLM ∘ fun w => star (u w) * fderiv ℝ u w k) (0 : ℂ →L[ℝ] ℝ) ζ := by
      apply (hasFDerivAt_const (0 : ℝ) ζ).congr_of_eventuallyEq
      filter_upwards [hn] with w hw
      simp only [Function.comp_apply, Complex.reCLM_apply]
      exact re_conj_fderiv hu h1 hw k
    have he := congrArg (fun L : ℂ →L[ℝ] ℝ => L k) (hre.unique h0)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, ContinuousLinearMap.flip_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
      Complex.reCLM_apply, ContinuousLinearMap.zero_apply, smul_eq_mul] at he
    rw [← he, Complex.star_def]
    congr 1
    ring

  have ht : HasFDerivAt (fun w => NF.dZ u w)
      ((1 / 2 : ℂ) • (S.flip 1 - Complex.I • S.flip Complex.I)) ζ := by
    have := ((hDv 1).sub ((hDv Complex.I).const_mul Complex.I)).const_mul (1 / 2 : ℂ)
    unfold NF.dZ
    exact this
  have hF : HasFDerivAt (fun w => star (u w) * NF.dZ u w) _ ζ := (hasFDerivAt_star (hud ζ hζ)).mul ht
  have hnorm : u ζ * star (u ζ) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1 ζ hζ]; simp
  have key : NF.dZb (fun w => star (u w) * NF.dZ u w) ζ = (1 / 4 : ℂ) *
      ((star (fderiv ℝ u ζ 1) + Complex.I * star (fderiv ℝ u ζ Complex.I)) *
        (fderiv ℝ u ζ 1 - Complex.I * fderiv ℝ u ζ Complex.I) + star (u ζ) * (S 1 1 + S Complex.I Complex.I)) := by
    unfold NF.dZb
    rw [hF.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, ContinuousLinearMap.flip_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul]
    unfold NF.dZ
    simp only [Complex.star_def, hsym]
    ring_nf
    rw [Complex.I_sq]
    ring
  have := curv_alg (u ζ) (fderiv ℝ u ζ 1) (fderiv ℝ u ζ Complex.I) (S 1 1) (S Complex.I Complex.I) hnorm
    (re_conj_fderiv hu h1 hζ 1) (re_conj_fderiv hu h1 hζ Complex.I) (h2 1) (h2 Complex.I)
  rw [key, Complex.mul_re, this]
  simp
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
