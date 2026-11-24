-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:59:31.916444+00:00
-- url     : https://prove2.me/submissions/60a8e12d-545a-44c1-979d-b4c1f90d0ef0

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lev_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_mulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_sigmaFinite_of_haar
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_heisenberg_map_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_levM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_neg_HPar
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_levM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mulM_cont


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution (HIv : HaarInv) (hG : ClosedG) (HI : HeisInv) (μG₁ : Measure (Mt k r')) (h₁ : IsHaarOn (GV k r') μG₁)
    (hP : IsClosedSubgroup (P1set k r')) (hμP : IsHaarOn (P1set k r') (muP μG₁)) (h : Mt k (1 + r') → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ q, h q ∂(muP μG₁) =
      ∫⁻ p : HPar k r' × Mt k r', h (mulM (levM k r' p.2, heisF k r' p.1)) ∂((volume : Measure (HPar k r')).prod μG₁) := by
  have := sigmaFinite_of_haar h₁
  have e1 : (μHeis k r').prod (μG₁.map (levM k r')) =
      ((volume : Measure (HPar k r')).prod μG₁).map (Prod.map (heisF k r') (levM k r')) :=
    Measure.map_prod_map _ _ heisenberg_map_continuous.measurable levM_cont.measurable
  have hPM : Measurable (Prod.map (heisF k r') (levM k r')) := heisenberg_map_continuous.measurable.prodMap levM_cont.measurable
  have hH : Measurable fun p : HPar k r' × Mt k r' => h (mulM (levM k r' p.2, heisF k r' p.1)) :=
    hh.comp (mulM_cont.measurable.comp ((levM_cont.measurable.comp measurable_snd).prodMk (heisenberg_map_continuous.measurable.comp measurable_fst)))
  have hNI : Measurable (Prod.map (Neg.neg : HPar k r' → HPar k r') (invM : Mt k r' → Mt k r')) :=
    measurable_neg.prodMap invM_meas
  have hae : ∀ᵐ p : HPar k r' × Mt k r' ∂((volume : Measure (HPar k r')).prod μG₁), p.2 ∈ (GV k r' : Set (Mt k r')) := by
    rw [ae_iff]
    have : {p : HPar k r' × Mt k r' | ¬ p.2 ∈ (GV k r' : Set (Mt k r'))} = Set.univ ×ˢ ((GV k r')ᶜ : Set (Mt k r')) := by
      ext p; simp only [Set.mem_prod, Set.mem_univ, true_and]; exact Iff.rfl
    rw [this, Measure.prod_prod, h₁.conc, mul_zero]
  calc ∫⁻ q, h q ∂(muP μG₁) = ∫⁻ q, h q ∂((muP μG₁).map invM) := by rw [HIv _ _ _ _ hP hμP]
    _ = ∫⁻ q, h (invM q) ∂(muP μG₁) := lintegral_map hh invM_meas
    _ = ∫⁻ p : HPar k r' × Mt k r', h (invM (mulM (heisF k r' p.1, levM k r' p.2))) ∂((volume : Measure (HPar k r')).prod μG₁) := by
        unfold muP
        rw [e1, Measure.map_map mulM_cont.measurable hPM]
        exact lintegral_map (f := fun q => h (invM q)) (hh.comp invM_meas) (mulM_cont.measurable.comp hPM)
    _ = ∫⁻ p : HPar k r' × Mt k r', (fun p' : HPar k r' × Mt k r' => h (mulM (levM k r' p'.2, heisF k r' p'.1)))
          (Prod.map (Neg.neg : HPar k r' → HPar k r') (invM : Mt k r' → Mt k r') p) ∂((volume : Measure (HPar k r')).prod μG₁) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with p hp
        congr 1
        show ((heis0 k r' p.1 * ιLev k 1 r' (Matrix.of p.2) : Mat k (1 + r'))⁻¹ : Mat k (1 + r')) =
          ιLev k 1 r' ((Matrix.of p.2 : Mat k r')⁻¹ : Mat k r') * heis0 k r' (-p.1)
        rw [Matrix.mul_inv_rev, HI, lev_inv (Matrix.of p.2) ((hG k r').unit _ hp)]
        rfl
    _ = ∫⁻ p', h (mulM (levM k r' p'.2, heisF k r' p'.1))
          ∂(((volume : Measure (HPar k r')).prod μG₁).map (Prod.map (Neg.neg : HPar k r' → HPar k r') (invM : Mt k r' → Mt k r'))) :=
        (lintegral_map hH hNI).symm
    _ = _ := by
        rw [← Measure.map_prod_map _ _ measurable_neg invM_meas, neg_HPar, HIv _ _ _ _ (hG k r') h₁]
end Formalism.FourierDecayAlt.P.B2x9
