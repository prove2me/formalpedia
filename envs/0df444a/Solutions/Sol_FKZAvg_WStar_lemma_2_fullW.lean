-- Prove2me | solution 1 for FKZAvg.WStar.lemma_2_fullW
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T15:22:32.733083+00:00
-- url     : https://prove2.me/submissions/a47e9e0f-26e2-41e8-ba74-4c1fadc4c0f2

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions
import Theorems.Thm_SchalAvg_AvgOpt_lemma_2_3_ii

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter SchalAvg.AvgOpt FKZAvg.WStar

/-- The common compactness argument: under (W*(i, ii)), adding to `c(x, ·)` any nonnegative
function that is sequentially lower semicontinuous on `A(x)` keeps it inf-compact on `A(x)`. -/
theorem fkz_lemma2_key {X A : Type*}
    [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [MeasurableSpace A]
    (M : Model X A) (x : X) (hi : CondWStar_i M) (hii : CondWStar_ii M)
    (h : A → ℝ≥0∞)
    (hh : ∀ (as : ℕ → A) (a : A), (∀ n, as n ∈ M.Aset x) → a ∈ M.Aset x →
      Tendsto as atTop (𝓝 a) → h a ≤ liminf (fun n => h (as n)) atTop) :
    InfCompactOn (fun a => M.toMDP.cost x a + h a) (M.Aset x) := by
  intro l
  apply IsSeqCompact.isCompact
  intro as has
  have hc : ∀ n, M.toMDP.cost x (as n) ≤ (l : ℝ≥0∞) :=
    fun n => le_trans le_self_add (has n).2
  obtain ⟨a, haA, hcl⟩ := hii (fun _ => x) x as tendsto_const_nhds (fun n => (has n).1) ⟨l, hc⟩
  obtain ⟨ψ, hψ, hlim⟩ := hcl.tendsto_subseq
  refine ⟨a, ⟨haA, ?_⟩, ψ, hψ, hlim⟩
  -- lower semicontinuity of the cost along the subsequence
  have hgr : Tendsto (fun k => (x, as (ψ k))) atTop (𝓝[graphA M] (x, a)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => (has (ψ k)).1⟩
    exact tendsto_const_nhds.prodMk_nhds hlim
  have hc1 : M.toMDP.cost x a ≤ liminf (fun k => M.toMDP.cost x (as (ψ k))) atTop := by
    refine le_of_forall_lt_imp_le_of_dense fun y hy => ?_
    have hev := hgr.eventually ((hi (x, a) haA) y hy)
    exact le_liminf_of_le (by isBoundedDefault) (hev.mono fun k hk => le_of_lt hk)
  have hh1 := hh (fun k => as (ψ k)) a (fun k => (has (ψ k)).1) haA hlim
  show M.toMDP.cost x a + h a ≤ (l : ℝ≥0∞)
  by_contra H
  push_neg at H
  have hb : ∀ k, M.toMDP.cost x (as (ψ k)) + h (as (ψ k)) ≤ (l : ℝ≥0∞) := fun k => (has (ψ k)).2
  rcases eq_or_ne (M.toMDP.cost x a) 0 with h0 | h0
  · rw [h0, zero_add] at H
    obtain ⟨k, hk⟩ := (eventually_lt_of_lt_liminf (lt_of_lt_of_le H hh1)).exists
    exact absurd ((hk.trans_le le_add_self).trans_le (hb k)) (lt_irrefl _)
  rcases eq_or_ne (h a) 0 with h0' | h0'
  · rw [h0', add_zero] at H
    obtain ⟨k, hk⟩ := (eventually_lt_of_lt_liminf (lt_of_lt_of_le H hc1)).exists
    exact absurd ((hk.trans_le le_self_add).trans_le (hb k)) (lt_irrefl _)
  obtain ⟨y', hy', z', hz', hl⟩ := ENNReal.exists_lt_add_of_lt_add H h0 h0'
  obtain ⟨k, hk1, hk2⟩ := ((eventually_lt_of_lt_liminf (lt_of_lt_of_le hy' hc1)).and
    (eventually_lt_of_lt_liminf (lt_of_lt_of_le hz' hh1))).exists
  exact absurd ((hl.trans_le (add_le_add hk1.le hk2.le)).trans_le (hb k)) (lt_irrefl _)

theorem solution {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model X A) (hsel : HasSelector M) (x : X) :
    (CondWStar_i M → CondWStar_ii M → InfCompactOn (fun a => M.toMDP.cost x a) (M.Aset x)) ∧
    (CondWStar M →
      ∀ u : X → ℝ≥0∞, InL u → ∀ α : ℝ, 0 ≤ α →
        InfCompactOn (fun a => eta M u α x a) (M.Aset x)) := by
  constructor
  · intro hi hii
    have := fkz_lemma2_key M x hi hii (fun _ => 0) (fun _ _ _ _ _ => by simp)
    simpa using this
  · rintro ⟨hi, hii, hiii⟩ u hu α _
    have hum : Measurable u := hu.1.measurable
    -- Portmanteau for the lower semicontinuous `u` (Lemma 4 = Schäl, Lemma 2.3(ii))
    have hI : ∀ (as : ℕ → A) (a : A), (∀ n, as n ∈ M.Aset x) → a ∈ M.Aset x →
        Tendsto as atTop (𝓝 a) →
        ∫⁻ y, u y ∂(M.toMDP.q (x, a)) ≤
          liminf (fun n => ∫⁻ y, u y ∂(M.toMDP.q (x, as n))) atTop := by
      intro as a has ha hlim
      letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
      let μ : ProbabilityMeasure X := ⟨M.toMDP.q (x, a), inferInstance⟩
      let μs : ℕ → ProbabilityMeasure X := fun n => ⟨M.toMDP.q (x, as n), inferInstance⟩
      have hgr : Tendsto (fun k => (x, as k)) atTop (𝓝[graphA M] (x, a)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => has k⟩
        exact tendsto_const_nhds.prodMk_nhds hlim
      have hμ : Tendsto μs atTop (𝓝 μ) := by
        rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
        intro f
        exact ((hiii f) (x, a) ha).tendsto.comp hgr
      have h4 := SchalAvg.AvgOpt.lemma_2_3_ii μ μs hμ (fun _ => u) (fun _ => hum)
      refine le_trans (lintegral_mono fun z => ?_) h4
      show u z ≤ liminf (fun p : ℕ × X => u p.2) (atTop ×ˢ 𝓝 z)
      rw [show (fun p : ℕ × X => u p.2) = u ∘ Prod.snd from rfl, liminf_comp, map_snd_prod]
      exact hu.1.le_liminf z
    have := fkz_lemma2_key M x hi hii
      (fun a => ENNReal.ofReal α * ∫⁻ y, u y ∂(M.toMDP.q (x, a)))
      (fun as a has ha hlim => by
        rw [ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top]
        exact mul_le_mul_right (hI as a has ha hlim) _)
    simpa [eta] using this
