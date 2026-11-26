-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.measurable_path_version
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:47:28.528048+00:00
-- url     : https://prove2.me/submissions/e9d2a26c-d553-4309-8c5d-fb90e22ff898

import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal

open MeasureTheory Filter Topology Set
open scoped NNReal

theorem solution {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [Zero E]
    (P : Measure Ω) (f : Ω → ℝ → E) (Good : (ℝ → E) → Prop)
    (hZero : Good (fun _ => 0)) (hGood : ∀ᵐ ω ∂P, Good (f ω))
    (hRight : ∀ x, Good x → ∀ s : ℝ, 0 ≤ s → ContinuousWithinAt x (Ici s) s)
    (hM : ∀ t : ℝ, 0 ≤ t → AEMeasurable (fun ω => f ω t) P) :
    ∃ g : Ω → ℝ → E, (∀ ω, Good (g ω)) ∧ (g =ᵐ[P] f) ∧
      ∀ t : ℝ, 0 ≤ t → Measurable (fun ω => g ω t) := by
  classical
  let time (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (2 : ℝ≥0)^n
  have hex (n k : ℕ) : ∃ g : Ω → E, Measurable g ∧ (fun ω => f ω (time n k)) =ᵐ[P] g := by
    exact ⟨_, (hM (time n k) (time n k).2).measurable_mk,
      (hM (time n k) (time n k).2).ae_eq_mk⟩
  choose w hw hW using hex
  have hAll : ∀ᵐ ω ∂P, Good (f ω) ∧ ∀ n k, f ω (time n k) = w n k ω :=
    hGood.and (ae_all_iff.2 (fun n => ae_all_iff.2 (hW n)))
  obtain ⟨S,hS,hSm,hSz⟩ := exists_measurable_superset_of_null (ae_iff.1 hAll)
  have hOn (ω : Ω) (hω : ω ∉ S) : Good (f ω) ∧ ∀ n k, f ω (time n k) = w n k ω := by
    by_contra hn
    exact hω (hS hn)
  let g (ω : Ω) : ℝ → E := if ω ∈ S then fun _ => 0 else f ω
  have hG : ∀ ω, Good (g ω) := by
    intro ω
    by_cases hω : ω ∈ S
    · simpa only [g,if_pos hω] using hZero
    · simpa only [g,if_neg hω] using (hOn ω hω).1
  have hg : g =ᵐ[P] f := by
    have h : ∀ᵐ ω ∂P, ω ∉ S := ae_iff.2 (by simpa using hSz)
    exact h.mono fun ω hn => if_neg hn
  refine ⟨g,hG,hg,?_⟩
  intro t ht
  let u : ℝ≥0 := ⟨t,ht⟩
  let j (n : ℕ) := Nat.ceil ((u:ℝ)*(2:ℝ)^n)
  let approx (n : ℕ) (ω : Ω) := if ω ∈ S then (0:E) else w n (j n) ω
  have hmeas (n : ℕ) : Measurable (approx n) := measurable_const.piecewise hSm (hw n (j n))
  refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 fun ω => ?_)
  by_cases hω : ω ∈ S
  · simpa only [approx,g,if_pos hω] using tendsto_const_nhds
  have htime : Tendsto (fun n => (time n (j n):ℝ)) atTop (𝓝 t) :=
    (NNReal.continuous_coe.tendsto u).comp
      (AvramDividend.Classical.dyadic_ceiling_nnreal_tendsto u)
  have habove : ∀ᶠ n in atTop, (time n (j n):ℝ) ∈ Ici t := by
    refine Eventually.of_forall fun n => ?_
    exact (AvramDividend.Classical.dyadic_ceiling_time_ge_nnreal u n)
  have hc := (hRight (f ω) (hOn ω hω).1 t ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨htime,habove⟩)
  rw [show g ω t = f ω t from by simp only [g,if_neg hω]]
  refine hc.congr fun n => ?_
  exact ((hOn ω hω).2 n (j n)).trans (if_neg hω).symm
