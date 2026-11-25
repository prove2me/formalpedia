-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HeisenbergLevelMinors.unipotent_volume_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:07:20.793429+00:00
-- url     : https://prove2.me/submissions/d83c72b9-dc01-440c-9d41-2cceb32201a9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JDomBoundOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastLevelSliceOfScalar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormBallVolumes
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLevelMinors
import Theorems.Thm_Formalism_FourierDecayAlt_P_HeisenbergLevelMinors_gN_lev_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_HeisenbergLevelMinors_coord_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_haarUnique
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_levM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_continuous_heis0
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_NormBallVolumes_gN_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_unipotent_haar_base_case
import Theorems.Thm_Formalism_FourierDecayAlt_P_unipotent_haar_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_unipotent_haar_recursion
import Theorems.Thm_Formalism_FourierDecayAlt_P_unipotent_radical_closed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
theorem _root_.solution : NNVol := by
  intro k r
  induction r using Nat.strong_induction_on with
  | _ r ih => ?_
  intro μ hμ
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hb : Formalism.QuantumDeterminants.Nset k 0 = {1} := Formalism.FourierDecayAlt.P.unipotent_haar_base_case k
    have hc : μ ((({1} : Set (Mat k 0)) : Set (Mt k 0))ᶜ) = 0 := by rw [← hb]; exact hμ.conc
    have h1 : μ Set.univ ≤ μ (({1} : Set (Mat k 0)) : Set (Mt k 0)) + μ ((({1} : Set (Mat k 0)) : Set (Mt k 0))ᶜ) := by
      have h2 : (Set.univ : Set (Mt k 0)) = (({1} : Set (Mat k 0)) : Set (Mt k 0)) ∪ (({1} : Set (Mat k 0)) : Set (Mt k 0))ᶜ :=
        (Set.union_compl_self _).symm
      exact h2 ▸ measure_union_le _ _
    have hfin : μ Set.univ ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ h1
      rw [hc, add_zero]
      exact (hμ.finite_compact _ isCompact_singleton).ne
    refine ⟨(μ Set.univ).toReal, fun R hR => ?_⟩
    calc μ {x | gN (Matrix.of x : Mat k 0) ≤ R} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = ENNReal.ofReal (μ Set.univ).toReal := (ENNReal.ofReal_toReal hfin).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right ENNReal.toReal_nonneg
          (Real.one_le_rpow hR (by positivity)))
  obtain ⟨r', rfl⟩ : ∃ r', r = 1 + r' := ⟨r - 1, by omega⟩
  obtain ⟨μ', hμ'⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r'
  obtain ⟨C', hC'⟩ := ih r' (by omega) μ' hμ'
  have hsf' := B5.haar_sigmaFinite hμ'
  have hR0 := Formalism.FourierDecayAlt.P.unipotent_haar_recursion k r' μ' hμ'
  obtain ⟨c, hc⟩ := B2x1.haarUnique k (1 + r') _ _ μ (Formalism.FourierDecayAlt.P.unipotent_radical_closed k (1 + r')) hR0 hμ.conc hμ.left
    hμ.finite_compact
  have hh0 : Measurable (heisM k r') := by
    have : Continuous (heisM k r') := B2x5.continuous_heis0 k r'
    exact this.measurable
  have hμH : Formalism.FourierDecayAlt.B2.μHeis k r' = (volume : Measure (Formalism.FourierDecayAlt.B2.HPar k r')).map (heisM k r') := rfl
  have hlev : Measurable (Formalism.FourierDecayAlt.B2.levM k r') := (B2x2.levM_cont k r').measurable
  have hAH : (volume : Measure (Formalism.FourierDecayAlt.B2.HPar k r')).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨v, hv0, hV⟩ : ∃ v : ℝ, 0 ≤ v ∧
      (volume : Measure (Formalism.FourierDecayAlt.B2.HPar k r')) (Metric.ball 0 1) = ENNReal.ofReal v :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal (measure_ball_lt_top).ne).symm⟩
  have hdim : Module.finrank ℝ (Formalism.FourierDecayAlt.B2.HPar k r') = 2 * (2 * r' + k + 1) + 1 := by
    simp [Module.finrank_prod, Module.finrank_pi_fintype, Complex.finrank_real_complex]; ring
  refine ⟨(c : ℝ) * (v * max C' 0), fun R hR => ?_⟩
  have hR0' : (0 : ℝ) ≤ R := by linarith
  set E : Set (Mt k (1 + r')) := {x | gN (Matrix.of x : Mat k (1 + r')) ≤ R} with hEd
  have hE : MeasurableSet E := measurableSet_le (NormBallVolumes.gN_meas _ _) measurable_const
  have hsub : (Prod.map (heisM k r') (Formalism.FourierDecayAlt.B2.levM k r')) ⁻¹' (Formalism.FourierDecayAlt.B2.mulM ⁻¹' E) ⊆
      Metric.closedBall (0 : Formalism.FourierDecayAlt.B2.HPar k r') R ×ˢ {y : Mt k r' | gN (Matrix.of y : Mat k r') ≤ R} := by
    intro p hp
    have hp' : gN (Formalism.FourierDecayAlt.B2.heis0 k r' p.1 * ιLev k 1 r' (Matrix.of p.2)) ≤ R := hp
    exact ⟨mem_closedBall_zero_iff.2 (le_trans (coord_le p.1 _) hp'), le_trans (gN_lev_le p.1 _) hp'⟩
  have hmeas0 : ((Formalism.FourierDecayAlt.B2.μHeis k r').prod (μ'.map (Formalism.FourierDecayAlt.B2.levM k r'))).map Formalism.FourierDecayAlt.B2.mulM E ≤
      ENNReal.ofReal (R ^ (2 * (2 * r' + k + 1) + 1)) * ENNReal.ofReal v * ENNReal.ofReal (C' * R ^ (((2 * r' + k + 1 : ℕ) : ℝ) ^ 2)) := by
    rw [Measure.map_apply B2x1.mulM_cont.measurable hE]
    rw [hμH, Measure.map_prod_map _ _ hh0 hlev, Measure.map_apply (hh0.prodMap hlev) (hE.preimage B2x1.mulM_cont.measurable)]
    calc _ ≤ ((volume : Measure (Formalism.FourierDecayAlt.B2.HPar k r')).prod μ')
          (Metric.closedBall (0 : Formalism.FourierDecayAlt.B2.HPar k r') R ×ˢ {y : Mt k r' | gN (Matrix.of y : Mat k r') ≤ R}) :=
          measure_mono hsub
      _ = (volume : Measure (Formalism.FourierDecayAlt.B2.HPar k r')) (Metric.closedBall 0 R) *
            μ' {y : Mt k r' | gN (Matrix.of y : Mat k r') ≤ R} := Measure.prod_prod _ _
      _ ≤ _ := by
          rw [Measure.addHaar_closedBall _ _ hR0', hdim, hV]
          gcongr
          exact hC' R hR
  rw [hc, Measure.smul_apply]
  have hpow : R ^ (2 * (2 * r' + k + 1) + 1) * R ^ (((2 * r' + k + 1 : ℕ) : ℝ) ^ 2) ≤
      R ^ (((2 * (1 + r') + k + 1 : ℕ) : ℝ) ^ 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith)]
    apply Real.rpow_le_rpow_of_exponent_le hR
    push_cast; nlinarith
  have hC'' : C' * R ^ (((2 * r' + k + 1 : ℕ) : ℝ) ^ 2) ≤ max C' 0 * R ^ (((2 * r' + k + 1 : ℕ) : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hR0' _)
  calc c • (((Formalism.FourierDecayAlt.B2.μHeis k r').prod (μ'.map (Formalism.FourierDecayAlt.B2.levM k r'))).map Formalism.FourierDecayAlt.B2.mulM E)
      ≤ (c : ℝ≥0∞) * (ENNReal.ofReal (R ^ (2 * (2 * r' + k + 1) + 1)) * ENNReal.ofReal v *
          ENNReal.ofReal (max C' 0 * R ^ (((2 * r' + k + 1 : ℕ) : ℝ) ^ 2))) := by
        rw [ENNReal.smul_def, smul_eq_mul]
        gcongr
        exact le_trans hmeas0 (by gcongr)
    _ = ENNReal.ofReal ((c : ℝ) * (v * max C' 0 *
          (R ^ (2 * (2 * r' + k + 1) + 1) * R ^ (((2 * r' + k + 1 : ℕ) : ℝ) ^ 2)))) := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have h0 : 0 ≤ (c : ℝ) * (v * max C' 0) :=
          mul_nonneg c.2 (mul_nonneg hv0 (le_max_right _ _))
        calc (c : ℝ) * (v * max C' 0 * (R ^ (2 * (2 * r' + k + 1) + 1) * R ^ (((2 * r' + k + 1 : ℕ) : ℝ) ^ 2)))
            = ((c : ℝ) * (v * max C' 0)) *
                (R ^ (2 * (2 * r' + k + 1) + 1) * R ^ (((2 * r' + k + 1 : ℕ) : ℝ) ^ 2)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow h0
end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
