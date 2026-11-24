-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.nu_hyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:22:18.663454+00:00
-- url     : https://prove2.me/submissions/793a238e-a1e6-46d2-9b85-4579fc1f444c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_mvM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_Phi_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_ae_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_emb_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_measurable_inv_mulVec_embWb_of_measSec

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
theorem _root_.solution (CWb : ClosedWb) (CW : ClosedW) (UF : UWbFacts) (z z' : Vc k r)
    {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : MeasSec s) (hsu : ∀ ζ, (s ζ)ᴴ * Hb k * s ζ = Hb k)
    {μW μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z) μW) [SFinite μW] [SFinite μW']
    (f : Mt k r → ℝ≥0∞) (hf : Measurable f) (G : Vc k r → ℝ≥0∞) (hG : Measurable G)
    (hFG : ∀ m ∈ UWb k r, (∫⁻ h', f (mulM (m, h')) ∂μW') = G (m *ᵥ z')) (b : Mat k r) (hb : b ∈ UWb k r) :
    ∫⁻ m, f (lmulM b m) ∂(nu z z' s μW μW') = ∫⁻ v, G (b *ᵥ v) ∂(hypMeas k r z z' s μW) := by
  have hWb := CWb k r
  have hPhi := Phi_meas (r := r) hs
  have hL : Measurable (lmulM b : Mt k r → Mt k r) := (lmulM_cont b).measurable
  have hψ := measurable_inv_mulVec_embWb_of_measSec (r := r) hs z'
  have hbv : Measurable fun v : Vc k r => b *ᵥ v :=
    (mvM_cont.comp (continuous_const.prodMk continuous_id)).measurable
  have hfL : Measurable fun m : Mt k r => f (lmulM b m) := hf.comp hL
  have hGb : Measurable fun v : Vc k r => G (b *ᵥ v) := hG.comp hbv
  have hF : Measurable fun x : ℂ × (Mt k r × Mt k r) => f (lmulM b (Phi s x)) := hfL.comp hPhi
  have hGψ : Measurable fun p : ℂ × Mt k r =>
      G (b *ᵥ ((Matrix.of p.2 : Mat k r)⁻¹ *ᵥ (embWb k r (s p.1) *ᵥ z'))) := hGb.comp hψ
  unfold nu hypMeas
  rw [lintegral_map hfL hPhi, lintegral_map hGb hψ, lintegral_prod _ hF.aemeasurable,
    lintegral_prod _ hGψ.aemeasurable]
  refine lintegral_congr fun ζ => ?_
  have hFζ : Measurable fun p : Mt k r × Mt k r => f (lmulM b (Phi s (ζ, p))) :=
    hF.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ hFζ.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem hW] with h hh
  have hu : (Matrix.of h : Mat k r) ∈ UWb k r := (UF k r).2.1 z hh
  have hm : (Matrix.of h : Mat k r)⁻¹ * embWb k r (s ζ) ∈ UWb k r :=
    hWb.mul_mem _ (hWb.inv_mem _ hu) _ (emb_mem UF hsu ζ)
  have hbm : b * ((Matrix.of h : Mat k r)⁻¹ * embWb k r (s ζ)) ∈ UWb k r := hWb.mul_mem _ hb _ hm
  have e1 : ∀ h' : Mt k r, f (lmulM b (Phi s (ζ, (h, h')))) =
      f (mulM (b * ((Matrix.of h : Mat k r)⁻¹ * embWb k r (s ζ)), h')) := fun h' => by
    congr 1
    show b * ((Matrix.of h : Mat k r)⁻¹ * embWb k r (s ζ) * Matrix.of h') =
      b * ((Matrix.of h : Mat k r)⁻¹ * embWb k r (s ζ)) * Matrix.of h'
    simp only [Matrix.mul_assoc]
  simp only [e1]
  rw [hFG _ hbm]
  congr 1
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
