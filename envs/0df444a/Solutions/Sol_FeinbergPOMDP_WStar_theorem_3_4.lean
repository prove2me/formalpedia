-- Prove2me | solution 1 for FeinbergPOMDP.WStar.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T17:51:39.835246+00:00
-- url     : https://prove2.me/submissions/6214f1a6-bf13-4379-aee9-b7eb9b195f67

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_FeinbergPOMDP_WStar_Model
import Theorems.Thm_SchalAvg_AvgOpt_lemma_2_3_ii
import Theorems.Thm_FeinbergPOMDP_WStar_lemma_6_1

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE FeinbergPOMDP.WStar

/-- `K ≤ lower + u` in `EReal` for `u : ℝ≥0∞`, in terms of `ENNReal.ofReal (K - lower) ≤ u`. -/
lemma fpw_ereal_le_iff (K lower : ℝ) (u : ℝ≥0∞) :
    (K : EReal) ≤ (lower : EReal) + (u : EReal) ↔ ENNReal.ofReal (K - lower) ≤ u := by
  induction u using ENNReal.recTopCoe with
  | top => simp [EReal.coe_ennreal_top, EReal.coe_add_top]
  | coe t =>
    rw [EReal.coe_nnreal_eq_coe_real, ← EReal.coe_add, EReal.coe_le_coe_iff,
      ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal]
    constructor <;> intro h <;> linarith

theorem solution {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (lower : ℝ) (f : X → A → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (hK : KInfCompact f) :
    (∀ K : ℝ, (∀ (x : X) (a : A), (K : EReal) ≤ (lower : EReal) + (f x a : EReal)) →
        ∀ (z : ProbabilityMeasure X) (a : A),
          (K : EReal) ≤ (lower : EReal) + (beliefCost f z a : EReal)) ∧
    KInfCompact (beliefCost f) := by
  refine ⟨?_, ?_⟩
  · intro K hKx z a
    rw [fpw_ereal_le_iff]
    have h1 : ∀ x, ENNReal.ofReal (K - lower) ≤ f x a := fun x =>
      (fpw_ereal_le_iff K lower _).1 (hKx x a)
    calc ENNReal.ofReal (K - lower) = ∫⁻ _x, ENNReal.ofReal (K - lower) ∂(z : Measure X) := by
          simp
      _ ≤ beliefCost f z a := lintegral_mono h1
  -- K-inf-compactness
  -- Step 0: f is lower semicontinuous (its sublevel sets are closed).
  have hflsc : LowerSemicontinuous (fun p : X × A => f p.1 p.2) := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro y
    induction y using ENNReal.recTopCoe with
    | top => simp
    | coe l =>
      apply IsSeqClosed.isClosed
      intro ps p hps hlim
      have hx : Tendsto (fun n => (ps n).1) atTop (𝓝 p.1) := (continuous_fst.tendsto _).comp hlim
      have hc := hK _ (Set.insert_nonempty _ _) hx.isCompact_insert_range l
      have hmem : ∀ n, ps n ∈ {q : X × A | q.1 ∈ insert p.1 (Set.range fun n => (ps n).1) ∧
          f q.1 q.2 ≤ (l : ℝ≥0∞)} := fun n =>
        ⟨Set.mem_insert_of_mem _ ⟨n, rfl⟩, hps n⟩
      exact (hc.isClosed.mem_of_tendsto hlim (Eventually.of_forall hmem)).2
  have hcbar := FeinbergPOMDP.WStar.lemma_6_1 f hf hflsc
  intro K hKne hKc l
  let S := {p : ProbabilityMeasure X × A | p.1 ∈ K ∧ beliefCost f p.1 p.2 ≤ (l : ℝ≥0∞)}
  have hSclosed_l : IsClosed {p : ProbabilityMeasure X × A | beliefCost f p.1 p.2 ≤ (l : ℝ≥0∞)} :=
    (lowerSemicontinuous_iff_isClosed_preimage.1 hcbar) _
  let _ : MetricSpace (ProbabilityMeasure X × A) :=
    TopologicalSpace.metrizableSpaceMetric _
  apply IsSeqCompact.isCompact
  intro s hs
  -- Step 1: extract a subsequence with z converging in K.
  obtain ⟨z, hzK, φ1, hφ1, hz1⟩ :=
    hKc.isSeqCompact (x := fun n => (s n).1) (fun n => (hs n).1)
  set b : ℕ → A := fun k => (s (φ1 k)).2 with hb
  set ζ : ℕ → ProbabilityMeasure X := fun k => (s (φ1 k)).1 with hζ
  -- Step 2: generalized Fatou.
  let _ : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  have hw : ∀ k, Measurable (fun x => f x (b k)) := fun k =>
    hf.comp (measurable_id.prodMk measurable_const)
  have hfat := SchalAvg.AvgOpt.lemma_2_3_ii z ζ hz1 (fun k x => f x (b k)) hw
  have hle : liminf (fun k => ∫⁻ x, f x (b k) ∂(ζ k : Measure X)) atTop ≤ (l : ℝ≥0∞) :=
    Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun k => (hs (φ1 k)).2)
  -- Step 3: a point x0 with small lower limit.
  obtain ⟨x0, hx0⟩ : ∃ x0, liminf (fun q : ℕ × X => f q.2 (b q.1)) (atTop ×ˢ 𝓝 x0) <
      ((l + 1 : ℝ≥0) : ℝ≥0∞) := by
    by_contra hcon
    push Not at hcon
    have : ((l + 1 : ℝ≥0) : ℝ≥0∞) ≤ (l : ℝ≥0∞) := by
      calc ((l + 1 : ℝ≥0) : ℝ≥0∞) = ∫⁻ _x, ((l + 1 : ℝ≥0) : ℝ≥0∞) ∂(z : Measure X) := by simp
        _ ≤ _ := lintegral_mono hcon
        _ ≤ _ := hfat
        _ ≤ _ := hle
    have h2 : (l : ℝ≥0∞) < ((l + 1 : ℝ≥0) : ℝ≥0∞) := by
      exact_mod_cast (lt_add_one l)
    exact absurd this (not_le.2 h2)
  -- Step 4: a sequence (k_j, y_j) → (∞, x0) with f(y_j, b k_j) < l + 1.
  obtain ⟨ns, hns, hnsP⟩ := Filter.exists_seq_forall_of_frequently
    (Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hx0)
  have hy : Tendsto (fun j => (ns j).2) atTop (𝓝 x0) := tendsto_snd.comp hns
  have hk : Tendsto (fun j => (ns j).1) atTop atTop := tendsto_fst.comp hns
  -- Step 5: compactness from K-inf-compactness of f.
  have hT := hK _ (Set.insert_nonempty _ _) hy.isCompact_insert_range (l + 1)
  obtain ⟨⟨x', a⟩, -, ψ, hψ, hconv⟩ := hT.tendsto_subseq
    (x := fun j => ((ns j).2, b (ns j).1))
    (fun j => ⟨Set.mem_insert_of_mem _ ⟨j, rfl⟩, (hnsP j).le⟩)
  -- Step 6: assemble a cluster point.
  set m : ℕ → ℕ := fun i => (ns (ψ i)).1 with hm
  have hmt : Tendsto m atTop atTop := hk.comp hψ.tendsto_atTop
  have hφm : Tendsto (fun i => φ1 (m i)) atTop atTop := hφ1.tendsto_atTop.comp hmt
  have hzconv : Tendsto (fun i => (s (φ1 (m i))).1) atTop (𝓝 z) := hz1.comp hmt
  have haconv : Tendsto (fun i => (s (φ1 (m i))).2) atTop (𝓝 a) :=
    (continuous_snd.tendsto _).comp hconv
  have hpconv : Tendsto (s ∘ fun i => φ1 (m i)) atTop (𝓝 (z, a)) :=
    hzconv.prodMk_nhds haconv
  have hcl : MapClusterPt (z, a) atTop s := MapClusterPt.of_comp hφm hpconv.mapClusterPt
  obtain ⟨ρ, hρ, hρconv⟩ := hcl.tendsto_subseq
  refine ⟨(z, a), ⟨hzK, ?_⟩, ρ, hρ, hρconv⟩
  exact hSclosed_l.mem_of_tendsto hρconv (Eventually.of_forall fun n => (hs (ρ n)).2)
