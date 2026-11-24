-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.nu_conc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:36:11.35461+00:00
-- url     : https://prove2.me/submissions/4a8a3501-5092-4ea0-a87c-5bbf710da53c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_Phi_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_emb_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_ae_both

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
    {μW μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z) μW) (hW' : IsHaarOn (UWset k r z') μW') :
    (nu z z' s μW μW') (UWb k r)ᶜ = 0 := by
  haveI := haar_sigmaFinite hW
  haveI := haar_sigmaFinite hW'
  have hWb := CWb k r
  have hc' : IsClosed {m : Mt k r | (Matrix.of m : Mat k r) ∈ UWb k r} := hWb.closed
  have hcl : MeasurableSet ({m : Mt k r | (Matrix.of m : Mat k r) ∈ UWb k r}ᶜ) := hc'.measurableSet.compl
  show (Measure.map (Phi s) ((wd k r z z').prod (μW.prod μW'))) ({m : Mt k r | (Matrix.of m : Mat k r) ∈ UWb k r}ᶜ) = 0
  rw [Measure.map_apply (Phi_meas hs) hcl]
  apply measure_mono_null _ (ae_iff.1 (ae_both z z' hW hW'))
  intro x hx
  have hx' : (Matrix.of (Phi s x) : Mat k r) ∉ UWb k r := hx
  show ¬ ((Matrix.of x.2.1 : Mat k r) ∈ UWset k r z ∧ (Matrix.of x.2.2 : Mat k r) ∈ UWset k r z')
  rintro ⟨h1, h2⟩
  apply hx'
  have hu1 : (Matrix.of x.2.1 : Mat k r) ∈ UWb k r := (UF k r).2.1 z h1
  have hu2 : (Matrix.of x.2.2 : Mat k r) ∈ UWb k r := (UF k r).2.1 z' h2
  exact hWb.mul_mem _ (hWb.mul_mem _ (hWb.inv_mem _ hu1) _ (emb_mem UF hsu x.1)) _ hu2
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
