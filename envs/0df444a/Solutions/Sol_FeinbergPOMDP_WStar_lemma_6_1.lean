-- Prove2me | solution 1 for FeinbergPOMDP.WStar.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T17:48:38.687253+00:00
-- url     : https://prove2.me/submissions/5fc65a68-f6e4-4755-bec8-20ad607b4abf

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model
import Theorems.Thm_SchalAvg_AvgOpt_lemma_2_3_ii

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergPOMDP.WStar

theorem solution {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (f : X → A → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (hlsc : LowerSemicontinuous (fun p : X × A => f p.1 p.2)) :
    LowerSemicontinuous (fun p : ProbabilityMeasure X × A => beliefCost f p.1 p.2) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  apply IsSeqClosed.isClosed
  intro ps p hps hlim
  simp only [Set.mem_preimage, Set.mem_Iic] at hps ⊢
  let _ : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  have hz : Tendsto (fun n => (ps n).1) atTop (𝓝 p.1) := (continuous_fst.tendsto _).comp hlim
  have ha : Tendsto (fun n => (ps n).2) atTop (𝓝 p.2) := (continuous_snd.tendsto _).comp hlim
  have hw : ∀ n, Measurable (fun x => f x (ps n).2) := fun n =>
    hf.comp (measurable_id.prodMk measurable_const)
  have key := SchalAvg.AvgOpt.lemma_2_3_ii p.1 (fun n => (ps n).1) hz
    (fun n x => f x (ps n).2) hw
  have hpt : ∀ x, f x p.2 ≤
      liminf (fun q : ℕ × X => f q.2 (ps q.1).2) (atTop ×ˢ 𝓝 x) := by
    intro x
    refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
    have hev : ∀ᶠ q in 𝓝 (x, p.2), c < f q.1 q.2 := hlsc (x, p.2) c hc
    have htend : Tendsto (fun q : ℕ × X => (q.2, (ps q.1).2)) (atTop ×ˢ 𝓝 x) (𝓝 (x, p.2)) := by
      refine Tendsto.prodMk_nhds (tendsto_snd) ?_
      exact ha.comp tendsto_fst
    exact Filter.le_liminf_of_le (by isBoundedDefault)
      ((htend.eventually hev).mono fun q hq => hq.le)
  have h1 : beliefCost f p.1 p.2 ≤
      liminf (fun n => ∫⁻ x, f x (ps n).2 ∂((ps n).1 : Measure X)) atTop :=
    (lintegral_mono hpt).trans key
  refine h1.trans ?_
  refine Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
  exact hps n
