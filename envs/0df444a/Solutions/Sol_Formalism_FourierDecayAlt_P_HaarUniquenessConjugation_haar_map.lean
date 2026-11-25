-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.haar_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:05:19.299903+00:00
-- url     : https://prove2.me/submissions/c1119a3b-7ac1-4c06-9c37-7a8e1f0c06f9

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftErrorLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarUniquenessConjugation
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_lmul_phi
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_rmul_phi
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_phi_closedEmbedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_phi_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_phi_range
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_lmul_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_rmul_cont

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
variable {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r}
namespace Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
theorem _root_.solution (hE : UJEmb) (hU : Unimodular) (hC : UHConj) (hP : IsUnit P.det)
    (hH : Pᴴ * Jm ε * P = Hpk k r) : IsHaarOn (GV k r) ((muG ε).map (phi ε P)) := by
  have hm := phi_measurable (ε := ε) hE hP
  have hce := phi_closedEmbedding (ε := ε) hE hP
  have hr := phi_range hE hC hP hH
  have hcl : IsClosed (Set.range (phi ε P)) := hce.isClosed_range
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hr, Measure.map_apply hm hcl.measurableSet.compl]
    have : phi ε P ⁻¹' (Set.range (phi ε P))ᶜ = ∅ := by
      ext u; simp
    rw [this, measure_empty]
  · intro a ha
    rw [← hr] at ha
    obtain ⟨u, rfl⟩ := ha
    have hl : Measurable (lmulM (phi ε P u)) := (lmul_cont _).measurable
    rw [Measure.map_map hl hm]
    have e : lmulM (phi ε P u) ∘ phi ε P = phi ε P ∘ (fun v => u * v) := by
      funext v; exact lmul_phi hP u v
    rw [e, ← Measure.map_map hm (measurable_const_mul u), map_mul_left_eq_self]
  · intro a ha
    rw [← hr] at ha
    obtain ⟨u, rfl⟩ := ha
    have hl : Measurable (rmulF (phi ε P u)) := (rmul_cont _).measurable
    rw [Measure.map_map hl hm]
    have e : rmulF (phi ε P u) ∘ phi ε P = phi ε P ∘ (fun v => v * u) := by
      funext v; exact rmul_phi hP u v
    rw [e, ← Measure.map_map hm (measurable_mul_const u), hU]
  · intro K hK
    rw [Measure.map_apply hm hK.isClosed.measurableSet]
    exact (hce.isCompact_preimage hK).measure_lt_top
  · intro h0
    have h1 : ((muG ε).map (phi ε P)) Set.univ = 0 := by rw [h0]; rfl
    rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, Measure.measure_univ_eq_zero] at h1
    exact (Measure.IsHaarMeasure.toIsOpenPosMeasure (μ := muG ε)).open_pos Set.univ isOpen_univ ⟨1, trivial⟩ (by rw [h1]; rfl)
end Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
