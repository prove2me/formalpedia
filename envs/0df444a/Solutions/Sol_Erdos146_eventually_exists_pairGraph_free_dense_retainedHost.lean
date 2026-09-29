-- Prove2me | solution 1 for Erdos146.eventually_exists_pairGraph_free_dense_retainedHost
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:48:18.569528+00:00
-- url     : https://prove2.me/submissions/5616dd66-a10f-4d16-908c-90402be59f1f

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_Erdos146_binaryEntropy_continuous
import Theorems.Thm_Erdos146_binaryEntropy_zero
import Theorems.Thm_Erdos146_entropySlack_pos
import Theorems.Thm_Erdos146_eventually_manuscriptExpectedRetainedEdge_entropy_lower
import Theorems.Thm_Erdos146_exp_mul_div_nat_succ_tendsto_atTop
import Theorems.Thm_Erdos146_hammingExpectedRetainedVertexCount_eq
import Theorems.Thm_Erdos146_hammingRetentionMeasure_isProbability
import Theorems.Thm_Erdos146_hammingRetentionProbability_mul_wordCount_tendsto_atTop
import Theorems.Thm_Erdos146_manuscriptSamplingFailureEvent_real_le
import Theorems.Thm_Erdos146_midpointBeta_lt_one
import Theorems.Thm_Erdos146_midpointBeta_lt_upper_unconditional
import Theorems.Thm_Erdos146_pairGraphOverFin_free_of_manuscript_exclusion

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem empiricalEntropyError_tendsto_zero :
    Filter.Tendsto empiricalEntropyError Filter.atTop (nhds 0) := by
  have hinv :
      Filter.Tendsto (fun L : ℕ => 1 / (L : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hfirst :
      Filter.Tendsto
        (fun L : ℕ => (1 + logTwo 3) / (L : ℝ))
        Filter.atTop (nhds 0) := by
    have hconst :
        Filter.Tendsto (fun _ : ℕ => 1 + logTwo 3)
          Filter.atTop (nhds (1 + logTwo 3)) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv] using hconst.mul hinv
  have hentropy :
      Filter.Tendsto
        (fun L : ℕ => binaryEntropy (1 / (L : ℝ)))
        Filter.atTop (nhds 0) := by
    have hcontinuous := binaryEntropy_continuous.continuousAt.tendsto.comp hinv
    rw [binaryEntropy_zero] at hcontinuous
    refine hcontinuous.congr' ?_
    filter_upwards [] with L
    rfl
  change Filter.Tendsto
    (fun L : ℕ => (1 + logTwo 3) / (L : ℝ) +
      binaryEntropy (1 / (L : ℝ)) / 2)
    Filter.atTop (nhds 0)
  simpa using hfirst.add (hentropy.div_const 2)

theorem logTwo_pairLayer_card_add_one_le (L : ℕ) (hL : 2 ≤ L) :
    logTwo ((L.choose 2 + 1 : ℕ) : ℝ) ≤
      2 * (L : ℝ) / Real.log 2 := by
  let x : ℝ := ((L.choose 2 + 1 : ℕ) : ℝ)
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hLreal : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hchoose : (L.choose 2 : ℝ) =
      (L : ℝ) * ((L : ℝ) - 1) / 2 := by
    exact Nat.cast_choose_two ℝ L
  have hxle : x ≤ (L : ℝ) ^ 2 := by
    dsimp [x]
    push_cast
    rw [hchoose]
    nlinarith [sq_nonneg ((L : ℝ) - 1)]
  have hsqrt : Real.sqrt x ≤ (L : ℝ) := by
    have hsq := Real.sq_sqrt hxpos.le
    have hsqrt_nonneg := Real.sqrt_nonneg x
    nlinarith
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    have hbound := Real.log_le_rpow_div hxpos.le
      (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at hbound
    norm_num at hbound
    linarith
  change Real.log x / Real.log 2 ≤ 2 * (L : ℝ) / Real.log 2
  apply (div_le_div_iff_of_pos_right log_two_pos).mpr
  linarith

theorem exists_empiricalEntropyError_base :
    ∃ L₀ : ℕ, 4 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L → empiricalEntropyError L < entropySlack := by
  have heventually :
      ∀ᶠ L : ℕ in Filter.atTop,
        empiricalEntropyError L < entropySlack :=
    (tendsto_order.1 empiricalEntropyError_tendsto_zero).2
      entropySlack entropySlack_pos
  obtain ⟨L₀, hL₀⟩ := (Filter.eventually_atTop.1 heventually)
  refine ⟨max 4 L₀, le_max_left _ _, ?_⟩
  intro L hL
  exact hL₀ L ((le_max_right 4 L₀).trans hL)

theorem exists_entropy_exclusion_base :
    ∃ L₀ : ℕ, 4 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L →
        empiricalEntropyError L < entropySlack ∧
        (L : ℝ) +
            3 * logTwo ((L.choose 2 + 1 : ℕ) : ℝ) -
              entropySlack * (L.choose 2 : ℝ) < -1 := by
  obtain ⟨Lerror, _, herror⟩ := exists_empiricalEntropyError_base
  let C : ℝ := 1 + 6 / Real.log 2
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (4 * (C + entropySlack + 1) / entropySlack)
  refine ⟨max 4 (max Lerror N), le_max_left _ _, ?_⟩
  intro L hL
  have hrest : max Lerror N ≤ L :=
    (le_max_right 4 (max Lerror N)).trans hL
  have herrorL : Lerror ≤ L := (le_max_left Lerror N).trans hrest
  have hNL : N ≤ L := (le_max_right Lerror N).trans hrest
  refine ⟨herror L herrorL, ?_⟩
  have hLfour : 4 ≤ L :=
    (le_max_left 4 (max Lerror N)).trans hL
  have hLreal : (4 : ℝ) ≤ L := by exact_mod_cast hLfour
  have hLpos : 0 < (L : ℝ) := by linarith
  have hNreal : (N : ℝ) ≤ L := by exact_mod_cast hNL
  have hthreshold :
      4 * (C + entropySlack + 1) / entropySlack < (L : ℝ) :=
    hN.trans_le hNreal
  have hbig :
      4 * (C + entropySlack + 1) < entropySlack * (L : ℝ) := by
    have h := (div_lt_iff₀ entropySlack_pos).mp hthreshold
    nlinarith
  have hscaled := mul_lt_mul_of_pos_right hbig hLpos
  have hlog := logTwo_pairLayer_card_add_one_le L (by omega)
  have hlinear :
      (L : ℝ) + 3 * logTwo ((L.choose 2 + 1 : ℕ) : ℝ) ≤
        C * (L : ℝ) := by
    calc
      (L : ℝ) + 3 * logTwo ((L.choose 2 + 1 : ℕ) : ℝ) ≤
          (L : ℝ) + 3 * (2 * (L : ℝ) / Real.log 2) := by
            gcongr
      _ = C * (L : ℝ) := by
        dsimp [C]
        ring
  have hchoose : (L.choose 2 : ℝ) =
      (L : ℝ) * ((L : ℝ) - 1) / 2 :=
    Nat.cast_choose_two ℝ L
  rw [hchoose]
  nlinarith [mul_pos entropySlack_pos hLpos]

theorem exists_entropy_exclusion_depth :
    ∃ depth : ℕ, 0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) := by
  obtain ⟨depth, hdepth⟩ :=
    exists_nat_gt ((2 : ℝ) / certifiedWindowWidth)
  have hwidth := certifiedWindowWidth_pos
  have hdepth_real : 0 < (depth : ℝ) :=
    (div_pos (by norm_num) hwidth).trans hdepth
  have hdepth_nat : 0 < depth := by exact_mod_cast hdepth_real
  refine ⟨depth, hdepth_nat, ?_⟩
  have hproduct := (div_lt_iff₀ hwidth).mp hdepth
  nlinarith

theorem hammingRetentionProbability_mul_wordCount_inv_tendsto_zero :
    Tendsto
      (fun dimension : ℕ =>
        1 / (hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)))
      atTop (𝓝 0) := by
  have htendsto := tendsto_inv_atTop_zero.comp
    hammingRetentionProbability_mul_wordCount_tendsto_atTop
  refine htendsto.congr' ?_
  filter_upwards [] with dimension
  simp only [Function.comp_apply, one_div]

theorem hammingExpectedRetainedVertexCount_tendsto_atTop :
    Tendsto hammingExpectedRetainedVertexCount atTop atTop := by
  have hgrowth :=
    hammingRetentionProbability_mul_wordCount_tendsto_atTop.const_mul_atTop
      (by norm_num : (0 : ℝ) < 2)
  apply hgrowth.congr'
  filter_upwards [] with dimension
  rw [hammingExpectedRetainedVertexCount_eq]
  ring

theorem hammingExpectedRetainedVertexCount_inv_tendsto_zero :
    Tendsto
      (fun dimension : ℕ =>
        1 / hammingExpectedRetainedVertexCount dimension)
      atTop (𝓝 0) := by
  have htendsto := tendsto_inv_atTop_zero.comp
    hammingExpectedRetainedVertexCount_tendsto_atTop
  refine htendsto.congr' ?_
  filter_upwards [] with dimension
  simp only [Function.comp_apply, one_div]

theorem exp_neg_dimension_log_two (dimension : ℕ) :
    Real.exp (-(dimension : ℝ) * Real.log 2) =
      ((1 / 2 : ℝ) ^ dimension) := by
  calc
    Real.exp (-(dimension : ℝ) * Real.log 2) =
        Real.exp (-((dimension : ℝ) * Real.log 2)) := by
          congr 1
          ring
    _ = (Real.exp ((dimension : ℝ) * Real.log 2))⁻¹ :=
      Real.exp_neg _
    _ = ((2 : ℝ) ^ dimension)⁻¹ := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    _ = ((1 / 2 : ℝ) ^ dimension) := by
      rw [← inv_pow]
      norm_num

theorem pairLayerExclusionProbability_tendsto_zero (depth : ℕ) :
    Filter.Tendsto
      (fun dimension : ℕ =>
        (((2 * depth : ℕ) : ℝ)) *
          Real.exp (-(dimension : ℝ) * Real.log 2))
      Filter.atTop (nhds 0) := by
  have hgeometric :
      Filter.Tendsto
        (fun dimension : ℕ => (1 / 2 : ℝ) ^ dimension)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simp_rw [exp_neg_dimension_log_two]
  simpa only [mul_zero] using
    hgeometric.const_mul (((2 * depth : ℕ) : ℝ))

theorem exists_hammingRetention_outside_event
    (dimension : ℕ)
    (event : Set (Set (Bool × HammingWord dimension)))
    (hsmall : (hammingRetentionMeasure dimension).real event < 1) :
    ∃ retained : Set (Bool × HammingWord dimension), retained ∉ event := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  by_contra hnone
  push Not at hnone
  have hevent : event = Set.univ := Set.eq_univ_of_forall hnone
  rw [hevent] at hsmall
  simp at hsmall

theorem exists_actualPairLayer_exclusion_parameters :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ layer : Fin depth,
        let layerSize :=
          Fintype.card (PairLayer baseSize layer.val)
        4 ≤ layerSize ∧
        empiricalEntropyError layerSize < entropySlack ∧
        (layerSize : ℝ) +
          3 * logTwo ((layerSize.choose 2 + 1 : ℕ) : ℝ) -
            entropySlack * (layerSize.choose 2 : ℝ) < -1 := by
  obtain ⟨baseSize, hbase, hbase_conditions⟩ :=
    exists_entropy_exclusion_base
  obtain ⟨depth, hdepth, hdepth_window⟩ :=
    exists_entropy_exclusion_depth
  refine ⟨baseSize, depth, hbase, hdepth, hdepth_window, ?_⟩
  intro layer
  dsimp
  have hsize :
      baseSize ≤ Fintype.card (PairLayer baseSize layer.val) :=
    pairLayer_card_ge_base baseSize layer.val hbase
  obtain ⟨herror, hfirst_moment⟩ :=
    hbase_conditions
      (Fintype.card (PairLayer baseSize layer.val)) hsize
  exact ⟨hbase.trans hsize, herror, hfirst_moment⟩

theorem sampledHammingEdgeEntropyRate_pos :
    0 < sampledHammingEdgeEntropyRate := by
  have hwindow := midpointBeta_lt_upper_unconditional
  unfold entropyUpperEndpoint at hwindow
  have hbeta := midpointBeta_lt_one
  have hbits : 0 < 1 - 2 * midpointBeta + binaryEntropy tau := by
    nlinarith
  have hentropy :
      Real.binEntropy tau = binaryEntropy tau * Real.log 2 := by
    unfold binaryEntropy
    field_simp [log_two_pos.ne']
  unfold sampledHammingEdgeEntropyRate
  rw [hentropy]
  nlinarith [mul_pos hbits log_two_pos]

theorem manuscriptExpectedRetainedEdgeCount_tendsto_atTop :
    Tendsto
      (fun dimension : ℕ =>
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension))
      atTop atTop := by
  have hrate := sampledHammingEdgeEntropyRate_pos
  have hloss : 0 < sampledHammingEdgeEntropyRate / 2 := by
    positivity
  have hlower := eventually_manuscriptExpectedRetainedEdge_entropy_lower
    (sampledHammingEdgeEntropyRate / 2) hloss
  have hgrowth := exp_mul_div_nat_succ_tendsto_atTop
    (sampledHammingEdgeEntropyRate / 2) hloss
  have hhalf :
      sampledHammingEdgeEntropyRate -
          sampledHammingEdgeEntropyRate / 2 =
        sampledHammingEdgeEntropyRate / 2 := by
    ring
  apply tendsto_atTop_mono' atTop _ hgrowth
  filter_upwards [hlower] with dimension hdimension
  simpa only [hhalf, mul_comm] using hdimension

theorem manuscriptExpectedRetainedEdgeCount_inv_tendsto_zero :
    Tendsto
      (fun dimension : ℕ =>
        1 / hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension))
      atTop (𝓝 0) := by
  have htendsto := tendsto_inv_atTop_zero.comp
    manuscriptExpectedRetainedEdgeCount_tendsto_atTop
  refine htendsto.congr' ?_
  filter_upwards [] with dimension
  simp only [Function.comp_apply, one_div]

theorem manuscriptSamplingFailureBound_tendsto_zero
    (depth : ℕ) :
    Tendsto
      (manuscriptSamplingFailureBound depth)
      atTop (𝓝 0) := by
  have hexclusion := pairLayerExclusionProbability_tendsto_zero depth
  have hvertices :=
    hammingExpectedRetainedVertexCount_inv_tendsto_zero.const_mul 4
  have hedges :=
    manuscriptExpectedRetainedEdgeCount_inv_tendsto_zero.const_mul 4
  have hwords :=
    hammingRetentionProbability_mul_wordCount_inv_tendsto_zero.const_mul 8
  have htotal := (hexclusion.add hvertices).add (hedges.add hwords)
  have htotal_zero :
      Tendsto
        (fun dimension : ℕ =>
          (((2 * depth : ℕ) : ℝ)) *
              Real.exp (-(dimension : ℝ) * Real.log 2) +
            4 * (1 / hammingExpectedRetainedVertexCount dimension) +
            (4 * (1 / hammingExpectedRetainedEdgeCount dimension
                (manuscriptHammingRadius dimension)) +
              8 * (1 / (hammingRetentionProbability dimension *
                ((2 ^ dimension : ℕ) : ℝ)))))
        atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using htotal
  apply htotal_zero.congr'
  filter_upwards [] with dimension
  unfold manuscriptSamplingFailureBound
  push_cast
  simp only [div_eq_mul_inv]
  ring

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ᶠ dimension : ℕ in Filter.atTop,
        ∃ retained : Set (Bool × HammingWord dimension),
          (pairGraphOverFin baseSize depth).Free
              (retainedHammingHost dimension
                (manuscriptHammingRadius dimension) retained) ∧
          hammingRetainedVertexCount dimension retained <
            3 * hammingRetentionProbability dimension *
              ((2 ^ dimension : ℕ) : ℝ) ∧
          hammingExpectedRetainedEdgeCount dimension
              (manuscriptHammingRadius dimension) / 2 ≤
            hammingRetainedEdgeCount dimension
              (manuscriptHammingRadius dimension) retained := by
  obtain ⟨baseSize, depth, hbase, hdepth, hdepth_window, hlayers⟩ :=
    exists_actualPairLayer_exclusion_parameters
  let layerSizes : Fin depth → ℕ := fun layer =>
    Fintype.card (PairLayer baseSize layer.val)
  have hparents : ∀ layer, 4 ≤ layerSizes layer :=
    fun layer => (hlayers layer).1
  have hfirst_moment :
      ∀ layer,
        (layerSizes layer : ℝ) +
          3 * logTwo
            (((layerSizes layer).choose 2 + 1 : ℕ) : ℝ) -
            entropySlack * ((layerSizes layer).choose 2 : ℝ) < -1 :=
    fun layer => (hlayers layer).2.2
  have hsmall :
      ∀ᶠ dimension : ℕ in Filter.atTop,
        manuscriptSamplingFailureBound depth dimension < 1 :=
    (tendsto_order.1
      (manuscriptSamplingFailureBound_tendsto_zero depth)).2
        1 (by norm_num)
  refine ⟨baseSize, depth, hbase, hdepth, hdepth_window, ?_⟩
  filter_upwards [hsmall, Filter.eventually_gt_atTop 0] with dimension
    hbound hdimension
  obtain ⟨retained, houtside⟩ :=
    exists_hammingRetention_outside_event dimension
      (manuscriptSamplingFailureEvent layerSizes dimension)
      ((manuscriptSamplingFailureEvent_real_le layerSizes
        hdimension hparents hfirst_moment).trans_lt hbound)
  have hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (layerSizes layer) dimension side
              (midpointBeta - entropySlack) := by
    intro side layer hbad
    exact houtside (Or.inl (Or.inl (Set.mem_iUnion.mpr
      ⟨side, Set.mem_iUnion.mpr ⟨layer, hbad⟩⟩)))
  have hvertices :
      hammingRetainedVertexCount dimension retained <
        3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) :=
    lt_of_not_ge fun hlarge => houtside (Or.inl (Or.inr hlarge))
  have hedges :
      hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2 ≤
        hammingRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) retained :=
    le_of_not_gt fun hlow => houtside (Or.inr hlow)
  exact ⟨retained,
    pairGraphOverFin_free_of_manuscript_exclusion
      hbase hdimension hdepth_window retained hexclusion
      (fun layer => (hlayers layer).2.1),
    hvertices, hedges⟩
