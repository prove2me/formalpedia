-- Prove2me | solution 1 for DiscreteChoiceProx.Simplex.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T08:02:41.855916+00:00
-- url     : https://prove2.me/submissions/f8dff43a-cd84-42f4-8e9b-cf0b9c6b6c17

import Mathlib
import Definitions.Def_DiscreteChoiceProx_Simplex_Model

open MeasureTheory

namespace Aux_DCPl1

lemma integrable_sup {n : ℕ} [NeZero n] (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hint : ∀ i, Integrable (fun e : Fin n → ℝ => e i) μ) (u : Fin n → ℝ) :
    Integrable (fun e : Fin n → ℝ =>
      Finset.univ.sup' Finset.univ_nonempty (fun i => u i + e i)) μ := by
  have hc : Continuous (fun e : Fin n → ℝ =>
      Finset.univ.sup' Finset.univ_nonempty (fun i => u i + e i)) := by
    have hci : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Continuous ((fun i (e : Fin n → ℝ) => u i + e i) i) := fun i _ => by
      show Continuous (fun e : Fin n → ℝ => u i + e i)
      fun_prop
    have h := Continuous.finset_sup' (L := ℝ) (s := Finset.univ)
      (f := fun i (e : Fin n → ℝ) => u i + e i) Finset.univ_nonempty hci
    refine h.congr fun e => ?_
    rw [Finset.sup'_apply]
  have hB : Integrable (fun e : Fin n → ℝ => ∑ i, (|u i| + |e i|)) μ :=
    integrable_finsetSum Finset.univ (f := fun i (e : Fin n → ℝ) => |u i| + |e i|)
      (fun i _ => ((integrable_const (|u i|)).add (hint i).abs :
        Integrable (fun e : Fin n → ℝ => |u i| + |e i|) μ))
  refine hB.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun e => ?_)
  rw [Real.norm_eq_abs, abs_le]
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => u i + e i)
  have hle : ∀ i, |u i| + |e i| ≤ ∑ k, (|u k| + |e k|) := fun i =>
    Finset.single_le_sum (f := fun k => |u k| + |e k|)
      (fun k _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)
  rw [hj]
  have h1 := hle j
  have h2 := neg_abs_le (u j)
  have h3 := neg_abs_le (e j)
  have h4 := le_abs_self (u j)
  have h5 := le_abs_self (e j)
  constructor <;> linarith

end Aux_DCPl1

open DiscreteChoiceProx.Simplex Aux_DCPl1 in
theorem solution {n : ℕ} [NeZero n] (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hA : Assumption1 μ) :
    (∀ (u : Fin n → ℝ) (γ : ℝ),
      surplus μ (u + fun _ => γ) = surplus μ u + γ) ∧
    (∀ u v : Fin n → ℝ, (∀ i, v i ≤ u i) → surplus μ v ≤ surplus μ u) ∧
    (∀ u : Fin n → ℝ,
      (Finset.univ.sup' Finset.univ_nonempty fun i => u i) +
        (Finset.univ.inf' Finset.univ_nonempty fun i => ∫ e, e i ∂μ) ≤ surplus μ u) := by
  have hint := hA.integrable
  refine ⟨fun u γ => ?_, fun u v huv => ?_, fun u => ?_⟩
  · unfold surplus
    simp only [Pi.add_apply]
    have hpt : ∀ e : Fin n → ℝ,
        Finset.univ.sup' Finset.univ_nonempty (fun i => u i + γ + e i)
          = Finset.univ.sup' Finset.univ_nonempty (fun i => u i + e i) + γ := by
      intro e
      apply le_antisymm
      · refine Finset.sup'_le _ _ fun i _ => ?_
        have : u i + e i ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => u i + e i) :=
          Finset.le_sup' (fun i => u i + e i) (Finset.mem_univ i)
        linarith
      · obtain ⟨j, -, hj⟩ :=
          Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => u i + e i)
        rw [hj]
        have : u j + γ + e j ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => u i + γ + e i) :=
          Finset.le_sup' (fun i => u i + γ + e i) (Finset.mem_univ j)
        linarith
    simp_rw [hpt]
    rw [integral_add (integrable_sup μ hint u) (integrable_const γ), integral_const]
    simp
  · unfold surplus
    refine integral_mono (integrable_sup μ hint v) (integrable_sup μ hint u) fun e => ?_
    refine Finset.sup'_le _ _ fun i _ => ?_
    have h1 : u i + e i ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => u i + e i) :=
      Finset.le_sup' (fun i => u i + e i) (Finset.mem_univ i)
    have := huv i
    linarith
  · unfold surplus
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => u i)
    rw [hj]
    have h1 : Finset.univ.inf' Finset.univ_nonempty (fun i => ∫ e, e i ∂μ) ≤ ∫ e, e j ∂μ :=
      Finset.inf'_le _ (Finset.mem_univ j)
    have h2 : ∫ e, (u j + e j) ∂μ ≤
        ∫ e, Finset.univ.sup' Finset.univ_nonempty (fun i => u i + e i) ∂μ :=
      integral_mono ((integrable_const _).add (hint j)) (integrable_sup μ hint u)
        fun e => Finset.le_sup' (fun i => u i + e i) (Finset.mem_univ j)
    rw [integral_add (integrable_const _) (hint j), integral_const] at h2
    simp only [probReal_univ, smul_eq_mul, one_mul] at h2
    linarith
