-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.nu_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:36:15.381349+00:00
-- url     : https://prove2.me/submissions/7261c728-8ff2-47be-a986-ac611e7dc3e9

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_Phi_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_wd_ne_zero

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
theorem _root_.solution (z z' : Vc k r) {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : MeasSec s)
    {μW μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z) μW) (hW' : IsHaarOn (UWset k r z') μW') :
    nu z z' s μW μW' ≠ 0 := by
  haveI := haar_sigmaFinite hW
  haveI := haar_sigmaFinite hW'
  unfold nu
  intro h0
  rw [Measure.map_eq_zero_iff (Phi_meas hs).aemeasurable] at h0
  have h1 : ((wd k r z z').prod (μW.prod μW')) Set.univ = 0 := by simp [h0]
  rw [← Set.univ_prod_univ, Measure.prod_prod, ← Set.univ_prod_univ, Measure.prod_prod] at h1
  rcases mul_eq_zero.1 h1 with h | h
  · exact wd_ne_zero z z' (Measure.measure_univ_eq_zero.1 h)
  · rcases mul_eq_zero.1 h with h | h
    · exact hW.ne_zero (Measure.measure_univ_eq_zero.1 h)
    · exact hW'.ne_zero (Measure.measure_univ_eq_zero.1 h)
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
