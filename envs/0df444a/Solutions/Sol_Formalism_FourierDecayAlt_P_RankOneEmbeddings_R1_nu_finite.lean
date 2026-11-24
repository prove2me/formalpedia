-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.nu_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:36:14.560577+00:00
-- url     : https://prove2.me/submissions/a122cbc3-7d27-4583-9fa1-dac024b81280

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_Om_open
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_ae_Om
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_Phi_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_ae_both
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_haar_finite
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_wd_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
theorem _root_.solution (KW : CompactW) (RM : RankOneMem) (z z' : Vc k r)
    {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : MeasSec s)
    (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' s)
    {μW μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z) μW) (hW' : IsHaarOn (UWset k r z') μW')
    (K : Set (Mt k r)) (hK : IsCompact K) : (nu z z' s μW μW') K < ∞ := by
  haveI := haar_sigmaFinite hW
  haveI := haar_sigmaFinite hW'
  haveI := haar_finite KW hz hT hW
  haveI := haar_finite KW hz' hT' hW'
  have hcont : Continuous fun m : Mt k r => herm (Hpk k r) ((Matrix.of m : Mat k r) *ᵥ z') z := by
    unfold herm
    fun_prop
  obtain ⟨R, hR⟩ := (hK.image hcont).isBounded.subset_closedBall (0 : ℂ)
  have hOm : MeasurableSet (Om k r z z') := (Om_open z z').measurableSet
  obtain ⟨B, hBdef⟩ : ∃ B : Set ℂ, B = Metric.closedBall 0 R ∪ (Om k r z z')ᶜ := ⟨_, rfl⟩
  have hnull := ae_iff.1 (ae_both z z' hW hW')
  unfold nu
  rw [Measure.map_apply (Phi_meas hs) hK.isClosed.measurableSet]
  have hsub : Phi s ⁻¹' K ⊆ (B ×ˢ Set.univ) ∪
      {x : ℂ × (Mt k r × Mt k r) | ¬((Matrix.of x.2.1 : Mat k r) ∈ UWset k r z ∧
        (Matrix.of x.2.2 : Mat k r) ∈ UWset k r z')} := by
    intro x hx
    by_cases hg : (Matrix.of x.2.1 : Mat k r) ∈ UWset k r z ∧ (Matrix.of x.2.2 : Mat k r) ∈ UWset k r z'
    · left
      refine ⟨?_, Set.mem_univ _⟩
      rw [hBdef]
      by_cases hζ : x.1 ∈ Om k r z z'
      · left
        have hrm := (RM k r z z' s hz hz' hsec x.1 hζ _ hg.1 _ hg.2).2
        exact hR ⟨Phi s x, hx, hrm⟩
      · right
        exact hζ
    · right
      exact hg
  have h1 : wd k r z z' (Om k r z z')ᶜ = 0 := by
    show (volume.withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)) (Om k r z z')ᶜ = 0
    rw [withDensity_apply _ hOm.compl]
    have hae : ∀ᵐ ζ ∂(volume.restrict (Om k r z z')ᶜ),
        ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) = 0 := by
      rw [ae_restrict_iff' hOm.compl]
      filter_upwards [ae_Om (r := r) z z'] with ζ hζ hc
      rcases hζ with hζ | hζ
      · exact absurd hζ hc
      · rw [hζ, ENNReal.ofReal_zero]
    rw [lintegral_congr_ae hae, lintegral_zero]
  have hwdB : wd k r z z' B < ∞ := by
    rw [hBdef]
    calc wd k r z z' (Metric.closedBall 0 R ∪ (Om k r z z')ᶜ)
        ≤ wd k r z z' (Metric.closedBall 0 R) + wd k r z z' (Om k r z z')ᶜ := measure_union_le _ _
      _ < ∞ := by
        rw [h1, add_zero]
        exact wd_ball z z' (mul_nonneg hT.le hT'.le) R
  calc ((wd k r z z').prod (μW.prod μW')) (Phi s ⁻¹' K)
      ≤ ((wd k r z z').prod (μW.prod μW')) ((B ×ˢ Set.univ) ∪
        {x : ℂ × (Mt k r × Mt k r) | ¬((Matrix.of x.2.1 : Mat k r) ∈ UWset k r z ∧
          (Matrix.of x.2.2 : Mat k r) ∈ UWset k r z')}) := measure_mono hsub
    _ ≤ ((wd k r z z').prod (μW.prod μW')) (B ×ˢ Set.univ) +
        ((wd k r z z').prod (μW.prod μW')) {x : ℂ × (Mt k r × Mt k r) | ¬((Matrix.of x.2.1 : Mat k r) ∈ UWset k r z ∧
          (Matrix.of x.2.2 : Mat k r) ∈ UWset k r z')} := measure_union_le _ _
    _ < ∞ := by
      rw [Measure.prod_prod, hnull, add_zero]
      exact ENNReal.mul_lt_top hwdB (measure_lt_top _ _)
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
