-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.ibp_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:49.365974+00:00
-- url     : https://prove2.me/submissions/aeeffc67-6c97-419a-ac34-25627f533726

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_contDiff_smul_of_tsupport
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_tsupport_smul_subset__d2c1bc7b3def
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_holo_contDiffOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wirtingerIBP
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_Bd_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bk_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bk_contDiffOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {d : ℕ}
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {β t : ℂ} (hβ : β ≠ 0) (ht : t ≠ 0) {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (hne : ∀ x ∈ Ω, fderiv ℂ g x ≠ 0)
    {a : (Fin d → ℂ) → V} (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a) (hsupp : tsupport a ⊆ Ω) :
    ∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d)) =
      ∑ k : Fin d, (-(2 * t / (Complex.I * β))) •
        ∫ x : Fin d → ℂ, psi β (g x / t) • wirt k (fun y => bk g k y • a y) x ∂(muPi β (Fin d)) := by
  have hf : ∀ k, ContDiff ℝ 1 (fun y => bk g k y • a y) := fun k =>
    contDiff_smul_of_tsupport hΩ (by exact_mod_cast bk_contDiffOn hΩ hg hne k 1) ha hsupp
  have hfs : ∀ k, tsupport (fun y => bk g k y • a y) ⊆ tsupport a := fun k => tsupport_smul_subset' _ _
  have hfc : ∀ k, HasCompactSupport (fun y => bk g k y • a y) := fun k =>
    hc.of_isClosed_subset (isClosed_tsupport _) (hfs k)
  have hW : ∀ k, ∫ x : Fin d → ℂ, psi β (g x / t) • wirt k (fun y => bk g k y • a y) x ∂(muPi β (Fin d)) =
      -∫ x : Fin d → ℂ, (Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) * psi β (g x / t)) •
        (bk g k x • a x) ∂(muPi β (Fin d)) := fun k =>
    wirtingerIBP d β t Ω g ht hΩ hg V _ k (hf k) (hfc k) ((hfs k).trans hsupp)
  have hcont : ∀ k, ContinuousOn (fun x => Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) *
      psi β (g x / t)) Ω := by
    intro k
    have h1 : ContinuousOn (fderiv ℂ g) Ω :=
      ((holo_contDiffOn hΩ hg 1).continuousOn_fderiv_of_isOpen hΩ (by norm_num))
    have h2 : ContinuousOn (fun x => fderiv ℂ g x (Pi.single k 1)) Ω := h1.clm_apply continuousOn_const
    have h3 : ContinuousOn (fun x => psi β (g x / t)) Ω := by
      unfold psi
      refine Complex.continuous_exp.comp_continuousOn ?_
      refine continuousOn_const.mul ?_
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      refine Complex.continuous_re.comp_continuousOn ?_
      exact continuousOn_const.mul (hg.continuousOn.div_const _)
    exact (((continuousOn_const.mul h2).div_const _).mul h3)
  have hint : ∀ k, Integrable (fun x => (Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) *
      psi β (g x / t)) • (bk g k x • a x)) (muPi β (Fin d)) := by
    intro k
    have h1 : ContDiff ℝ 0 (fun x => (Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) *
      psi β (g x / t)) • (bk g k x • a x)) :=
      contDiff_smul_of_tsupport hΩ (contDiffOn_zero.mpr (hcont k)) ((hf k).of_le (by norm_num))
        ((hfs k).trans hsupp)
    refine (contDiff_zero.mp h1).integrable_of_hasCompactSupport ?_
    exact (hfc k).of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset' _ _)
  have hpt : ∀ x, psi β (g x / t) • a x = ∑ k : Fin d, (2 * t / (Complex.I * β)) •
      ((Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) * psi β (g x / t)) • (bk g k x • a x)) := by
    intro x
    by_cases hx : x ∈ Ω
    · have h1 := bk_sum (hne x hx)
      have h2 : ∀ k : Fin d, (2 * t / (Complex.I * β)) •
          ((Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) * psi β (g x / t)) • (bk g k x • a x)) =
          (fderiv ℂ g x (Pi.single k 1) * bk g k x) • (psi β (g x / t) • a x) := by
        intro k
        simp only [smul_smul]
        congr 1
        have : Complex.I ≠ 0 := Complex.I_ne_zero
        field_simp
      simp only [h2]
      rw [← Finset.sum_smul, h1, one_smul]
    · have : a x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h)
      simp [this]
  simp only [hpt]
  have hint' : ∀ k ∈ (Finset.univ : Finset (Fin d)), Integrable (fun x => (2 * t / (Complex.I * β)) •
      ((Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) * psi β (g x / t)) • (bk g k x • a x)))
      (muPi β (Fin d)) := fun k _ => (hint k).smul _
  rw [integral_finsetSum _ hint']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_smul, hW k, neg_smul, smul_neg, neg_neg]
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
