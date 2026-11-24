-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.nu_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:27.346441+00:00
-- url     : https://prove2.me/submissions/dcd90ac2-e25c-43a9-81ad-695af2f6e43d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_mvM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_exists_G
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_FF_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_FF_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_nu_hyp

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
theorem _root_.solution (CWb : ClosedWb) (CW : ClosedW) (UF : UWbFacts) (HI : HypInv) (z z' : Vc k r)
    {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : MeasSec s) (hsu : ∀ ζ, (s ζ)ᴴ * Hb k * s ζ = Hb k)
    (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' s)
    {μW μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z) μW) (hW' : IsHaarOn (UWset k r z') μW')
    (a : Mat k r) (ha : a ∈ UWb k r) : (nu z z' s μW μW').map (lmulM a) = nu z z' s μW μW' := by
  haveI := haar_sigmaFinite hW
  haveI := haar_sigmaFinite hW'
  have hWb := CWb k r
  apply Measure.ext_of_lintegral
  intro f hf
  have hL : Measurable (lmulM a : Mt k r → Mt k r) := (lmulM_cont a).measurable
  rw [lintegral_map hf hL]
  obtain ⟨G, hG, hFG⟩ := exists_G CWb z' (fun m => ∫⁻ h', f (mulM (m, h')) ∂μW') (FF_meas μW' f hf)
    (fun m h hh => FF_inv hW' f hf m h hh)
  have hFG' : ∀ m ∈ UWb k r, (∫⁻ h', f (mulM (m, h')) ∂μW') = G (m *ᵥ z') := hFG
  have h1 := nu_hyp CWb CW UF z z' hs hsu hW f hf G hG hFG' a ha
  have h2 := nu_hyp CWb CW UF z z' hs hsu hW f hf G hG hFG' 1 hWb.one_mem
  have hHI := HI k r z z' s μW hk hz hz' hT hT' hsec hW a ha
  have hav : Measurable fun v : Vc k r => a *ᵥ v :=
    (mvM_cont.comp (continuous_const.prodMk continuous_id)).measurable
  rw [h1]
  calc ∫⁻ v, G (a *ᵥ v) ∂(hypMeas k r z z' s μW)
      = ∫⁻ v, G v ∂((hypMeas k r z z' s μW).map fun v => a *ᵥ v) := (lintegral_map hG hav).symm
    _ = ∫⁻ v, G v ∂(hypMeas k r z z' s μW) := by rw [hHI]
    _ = ∫⁻ v, G ((1 : Mat k r) *ᵥ v) ∂(hypMeas k r z z' s μW) := by simp only [Matrix.one_mulVec]
    _ = ∫⁻ m, f (lmulM 1 m) ∂(nu z z' s μW μW') := h2.symm
    _ = ∫⁻ m, f m ∂(nu z z' s μW μW') := by
      congr 1
      funext m
      congr 1
      show (1 : Mat k r) * Matrix.of m = m
      exact Matrix.one_mul _
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
