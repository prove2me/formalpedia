-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakDominationMajorants.NInt.lint_gN_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:31:13.483098+00:00
-- url     : https://prove2.me/submissions/8d20fb24-e75e-46f2-83a1-4bcf2722bf21

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_NInt_gN_mid_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_NInt_gN_heis_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_NInt_rpow_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_NInt_lint_heis_fin
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_NInt_sigmaFinite_haar
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_NInt_gN_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_NInt_levM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_NInt_base
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_measurable_heisT
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_haar_measure_unique_up_to_scalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_unipotent_haar_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_unipotent_haar_recursion
import Theorems.Thm_Formalism_FourierDecayAlt_P_unipotent_radical_closed
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x5__Heis_eq_adc2ccc881fd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix
open Matrix
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakDominationMajorants Formalism.FourierDecayAlt.P.WeakDominationMajorants.NInt
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.B2x6
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.NInt
theorem _root_.solution (k r : ℕ) (μ : Measure (Mt k r)) (hμ : IsHaarOn (Nset k r) μ) (a : ℝ)
    (ha : r = 0 ∨ (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ) - 1) < a) :
    ∫⁻ x, ENNReal.ofReal (gN (Matrix.of x : Mat k r) ^ (-a)) ∂μ < ⊤ := by
  revert μ a
  induction r with
  | zero => intro μ hμ a _; exact base k μ hμ a
  | succ r' ih =>
    rw [Nat.add_comm r' 1]
    intro μ hμ a ha
    have ha' : ((1 + r' : ℕ) : ℝ) * (4 * ((1 + r' : ℕ) : ℝ) + 2 * (k : ℝ) - 1) < a := by
      rcases ha with h | h
      · omega
      · exact h
    push_cast at ha'
    have hr0 : (0 : ℝ) ≤ r' := Nat.cast_nonneg _
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have ha0 : 0 < a := by nlinarith
    obtain ⟨μ', hμ'⟩ := unipotent_haar_exists k r'
    have := sigmaFinite_haar hμ'
    obtain ⟨c, hc⟩ := haar_measure_unique_up_to_scalar k (1 + r') (Nset k (1 + r')) _ μ (unipotent_radical_closed k (1 + r'))
      (unipotent_haar_recursion k r' μ' hμ') hμ.conc hμ.left hμ.finite_compact
    have hf : Measurable (fun x : Mt k (1 + r') => ENNReal.ofReal (gN (Matrix.of x : Mat k (1 + r')) ^ (-a))) :=
      ENNReal.measurable_ofReal.comp ((gN_cont k (1 + r')).measurable.pow_const _)
    have hM : Measurable (mulM : Mt k (1 + r') × Mt k (1 + r') → Mt k (1 + r')) :=
      Formalism.FourierDecayAlt.P.B2x1.mulM_cont.measurable
    rw [hc, lintegral_smul_measure]
    rw [ENNReal.smul_def, smul_eq_mul]
    refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
    rw [lintegral_map hf hM, Formalism.FourierDecayAlt.P.B2x5.μHeis_eq,
      Measure.map_prod_map _ _ (Formalism.FourierDecayAlt.P.B2x5.measurable_heisT k r') (levM_meas k r'),
      lintegral_map (f := fun p : Mt k (1 + r') × Mt k (1 + r') =>
        ENNReal.ofReal (gN (Matrix.of (mulM p) : Mat k (1 + r')) ^ (-a))) (hf.comp hM)
        ((Formalism.FourierDecayAlt.P.B2x5.measurable_heisT k r').prodMap (levM_meas k r'))]
    set θ : ℝ := 1 / (1 + (r' : ℝ)) with hθ
    have h1r : (0 : ℝ) < 1 + r' := by linarith
    have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
    have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one h1r]; linarith
    have hae : ∀ᵐ q ∂((volume : Measure (HPar k r')).prod μ'), Matrix.of q.2 ∈ Nset k r' := by
      rw [ae_iff]
      refine measure_mono_null (t := (Set.univ : Set (HPar k r')) ×ˢ ((Nset k r')ᶜ : Set (Mt k r'))) ?_ ?_
      · intro q hq; exact ⟨trivial, hq⟩
      · rw [Measure.prod_prod, hμ'.conc, mul_zero]
    have key : ∀ᵐ q ∂((volume : Measure (HPar k r')).prod μ'),
        ENNReal.ofReal (gN (Matrix.of (mulM (Prod.map (Formalism.FourierDecayAlt.P.B2x5.heisT k r') (levM k r') q)) :
          Mat k (1 + r')) ^ (-a)) ≤
        ENNReal.ofReal (((1 + ‖q.1‖) / 2) ^ (-(θ * a))) *
          ENNReal.ofReal (gN (Matrix.of q.2 : Mat k r') ^ (-((1 - θ) * a))) := by
      filter_upwards [hae] with q hq
      have e : ENNReal.ofReal (gN (Matrix.of (mulM (Prod.map (Formalism.FourierDecayAlt.P.B2x5.heisT k r') (levM k r') q)) :
          Mat k (1 + r')) ^ (-a)) =
          ENNReal.ofReal (gN (heis0 k r' q.1 * ιLev k 1 r' (Matrix.of q.2)) ^ (-a)) := rfl
      rw [e, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
      apply ENNReal.ofReal_le_ofReal
      have hB : 1 ≤ gN (Matrix.of q.2 : Mat k r') := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hq.1
      apply rpow_split (by positivity) (by linarith) _ (le_trans' (gN_mid_le q.1 _) le_rfl) ha0.le hθ0 hθ1
      have := gN_heis_le q.1 (Matrix.of q.2 : Mat k r')
      linarith
    have hF1 : Measurable (fun x : HPar k r' => ENNReal.ofReal (((1 + ‖x‖) / 2) ^ (-(θ * a)))) := by
      apply ENNReal.measurable_ofReal.comp
      exact ((measurable_const.add measurable_norm).div_const _).pow_const _
    have hF2 : Measurable (fun x : Mt k r' => ENNReal.ofReal (gN (Matrix.of x : Mat k r') ^ (-((1 - θ) * a)))) :=
      ENNReal.measurable_ofReal.comp ((gN_cont k r').measurable.pow_const _)
    calc _ ≤ ∫⁻ q, ENNReal.ofReal (((1 + ‖q.1‖) / 2) ^ (-(θ * a))) *
          ENNReal.ofReal (gN (Matrix.of q.2 : Mat k r') ^ (-((1 - θ) * a))) ∂((volume : Measure (HPar k r')).prod μ') :=
          lintegral_mono_ae key
      _ = (∫⁻ x : HPar k r', ENNReal.ofReal (((1 + ‖x‖) / 2) ^ (-(θ * a)))) *
          ∫⁻ x, ENNReal.ofReal (gN (Matrix.of x : Mat k r') ^ (-((1 - θ) * a))) ∂μ' :=
          lintegral_prod_mul hF1.aemeasurable hF2.aemeasurable
      _ < ⊤ := by
        refine ENNReal.mul_lt_top (lint_heis_fin k r' ?_) (ih μ' hμ' _ ?_)
        · push_cast
          rw [hθ, one_div, inv_mul_eq_div, lt_div_iff₀ h1r]
          nlinarith
        · rcases Nat.eq_zero_or_pos r' with h0 | hpos
          · exact Or.inl h0
          · right
            have e1 : (1 - θ) * a = (r' : ℝ) * (a / (1 + r')) := by
              rw [hθ]; field_simp; ring
            rw [e1]
            have hrpos : (0 : ℝ) < r' := by exact_mod_cast hpos
            apply mul_lt_mul_of_pos_left _ hrpos
            rw [lt_div_iff₀ h1r]
            nlinarith
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.NInt
