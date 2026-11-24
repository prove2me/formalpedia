-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.nu_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:52:57.658816+00:00
-- url     : https://prove2.me/submissions/9d28ddfe-4055-4ba4-82b4-59141ec57863

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_parametrisation_base_vector_image
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_invM_contOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_mulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_sigmaFinite_of_haar
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_xi_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_tau_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_cone_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_II_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_ae_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_Ff_ind
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_nu_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_evalE_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_invM_contOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cone_eq


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
theorem _root_.solution (HIv : HaarInv) (hG : ClosedG) (HA : HeisAct) (HI : HeisInv) (OM : OneStepMem) (CF : ConeFinite)
    (μG₁ : Measure (Mt k r')) (h₁ : IsHaarOn (GV k r') μG₁)
    (hP : IsClosedSubgroup (P1set k r')) (hμP : IsHaarOn (P1set k r') (muP μG₁))
    (K : Set (Mt k (1 + r'))) (hK : IsCompact K) : nu μG₁ K < ∞ := by
  have := sigmaFinite_of_haar h₁
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set K' : Set (Mt k (1 + r')) := K ∩ (GV k (1 + r') : Set (Mt k (1 + r'))) with hK'
  have hK'c : IsCompact K' := hK.inter_right (hG k (1 + r')).closed
  have hinvc : IsCompact ((invM : Mt k (1 + r') → Mt k (1 + r')) '' K') :=
    hK'c.image_of_continuousOn (invM_contOn.mono fun x hx => ((hG k (1 + r')).unit x hx.2).ne_zero)
  set D : Set (Mt k (1 + r')) := mulM '' (((invM : Mt k (1 + r') → Mt k (1 + r')) '' K') ×ˢ K') with hD
  have hDc : IsCompact D := (hinvc.prod hK'c).image mulM_cont
  set Ke : Set (Fin (2 * (1 + r') + k + 1) → ℂ) := (fun g : Mt k (1 + r') => (Matrix.of g : Mat k (1 + r')) *ᵥ e0 k r') '' K with hKe
  have hKec : IsCompact Ke := hK.image evalE_cont
  have hKem : MeasurableSet Ke := hKec.isClosed.measurableSet
  have bound : ∀ p : ℂ × HPar k r', p.1 ≠ 0 →
      Ff (muP μG₁) (K.indicator 1) (tau k r' p) ≤ muP μG₁ D * (xi k r' ⁻¹' Ke).indicator 1 p := by
    intro p hp
    rw [Ff_ind _ _ hKm]
    set T : Set (Mt k (1 + r')) := (fun q => mulM (tau k r' p, q)) ⁻¹' K with hT
    have hgG := tau_mem hG HI OM p hp
    have hT' : muP μG₁ (T ∩ (P1set k r' : Set (Mt k (1 + r')))) = muP μG₁ T := measure_inter_conull hμP.conc
    rw [← hT']
    by_cases hne : (T ∩ (P1set k r' : Set (Mt k (1 + r')))).Nonempty
    · obtain ⟨q₀, hq₀T, hq₀P⟩ := hne
      have hq₀K' : mulM (tau k r' p, q₀) ∈ K' := ⟨hq₀T, (hG k (1 + r')).mul_mem _ hgG _ hq₀P.1⟩
      have hxi : xi k r' p ∈ Ke := by
        refine ⟨mulM (tau k r' p, q₀), hq₀T, ?_⟩
        show ((Matrix.of (tau k r' p) : Mat k (1 + r')) * (Matrix.of q₀ : Mat k (1 + r'))) *ᵥ e0 k r' = _
        rw [← Matrix.mulVec_mulVec]
        have : (Matrix.of q₀ : Mat k (1 + r')) *ᵥ e0 k r' = e0 k r' := hq₀P.2
        rw [this, parametrisation_base_vector_image HA]
      rw [Set.indicator_of_mem (show p ∈ xi k r' ⁻¹' Ke from hxi)]
      simp only [Pi.one_apply, mul_one]
      have hq₀inv : ((Matrix.of q₀ : Mat k (1 + r'))⁻¹ : Mat k (1 + r')) ∈ P1set k r' := hP.inv_mem _ hq₀P
      calc muP μG₁ (T ∩ (P1set k r' : Set (Mt k (1 + r'))))
          ≤ muP μG₁ (lmulM ((Matrix.of q₀ : Mat k (1 + r'))⁻¹ : Mat k (1 + r')) ⁻¹' D) := by
            refine measure_mono ?_
            rintro q ⟨hqT, hqP⟩
            refine ⟨(invM (mulM (tau k r' p, q₀)), mulM (tau k r' p, q)), ⟨⟨_, hq₀K', rfl⟩, ⟨hqT, (hG k (1 + r')).mul_mem _ hgG _ hqP.1⟩⟩, ?_⟩
            show (((Matrix.of (tau k r' p) : Mat k (1 + r')) * (Matrix.of q₀ : Mat k (1 + r')))⁻¹ : Mat k (1 + r')) *
              ((Matrix.of (tau k r' p) : Mat k (1 + r')) * (Matrix.of q : Mat k (1 + r'))) =
              ((Matrix.of q₀ : Mat k (1 + r'))⁻¹ : Mat k (1 + r')) * (Matrix.of q : Mat k (1 + r'))
            rw [Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Matrix.of (tau k r' p) : Mat k (1 + r')),
              Matrix.nonsing_inv_mul _ ((hG k (1 + r')).unit _ hgG), Matrix.one_mul]
        _ = (muP μG₁).map (lmulM ((Matrix.of q₀ : Mat k (1 + r'))⁻¹ : Mat k (1 + r'))) D :=
            (Measure.map_apply (lmulM_cont _).measurable hDc.isClosed.measurableSet).symm
        _ = muP μG₁ D := by rw [hμP.left _ hq₀inv]
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty]
      exact bot_le
  rw [nu_apply _ _ hKm, II_eq HIv hG HI μG₁ h₁ hP hμP _ (measurable_one.indicator hKm)]
  calc ∫⁻ p, Ff (muP μG₁) (K.indicator 1) (tau k r' p) ∂(mCone k r')
      ≤ ∫⁻ p, muP μG₁ D * (xi k r' ⁻¹' Ke).indicator 1 p ∂(mCone k r') := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_ne] with p hp
        exact bound p hp
    _ = muP μG₁ D * coneMeas k r' Ke := by
        rw [lintegral_const_mul _ (measurable_one.indicator (xi_cont.measurable hKem)),
          lintegral_indicator_one (xi_cont.measurable hKem), cone_eq, Measure.map_apply xi_cont.measurable hKem]
    _ < ∞ := ENNReal.mul_lt_top (hμP.finite_compact D hDc) (CF k r' Ke hKec)
end Formalism.FourierDecayAlt.P.B2x9
