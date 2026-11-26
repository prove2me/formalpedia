-- Prove2me | solution 1 for GEPPGrowth.Main.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T21:38:16.980442+00:00
-- url     : https://prove2.me/submissions/7b850dd7-f242-423b-bb6f-9eecdfb07199

import Definitions.Def_GEPPGrowth_Main_Process
import Theorems.Thm_GEPPGrowth_Main_lemma_4_1
open MeasureTheory ProbabilityTheory

theorem solution (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    GEPPGrowth.Main.prob (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      {x | t ≤ GEPPGrowth.Main.maxEntry (fun i (_ : Fin 1) => x i)} ≤
        (n:ℝ)*Real.sqrt 2 / (t*Real.sqrt Real.pi) * Real.exp (-t^2/2) := by
  set μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  set A : Set ℝ := {x | t ≤ |x|}
  -- a large maximum entry means some coordinate is large
  have hsub : {x : Fin n → ℝ | t ≤ GEPPGrowth.Main.maxEntry (fun i (_ : Fin 1) => x i)} ⊆
      ⋃ i, (fun x : Fin n → ℝ => x i) ⁻¹' A := by
    intro x hx
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨ij, -, hij⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n × Fin 1))
      Finset.univ_nonempty (fun ij => ‖x ij.1‖₊)
    simp only [Set.mem_ofPred_eq, GEPPGrowth.Main.maxEntry, hij, coe_nnnorm,
      Real.norm_eq_abs] at hx
    exact Set.mem_iUnion.2 ⟨ij.1, hx⟩
  -- each coordinate is standard normal
  have hcoord : ∀ i, μ ((fun x : Fin n → ℝ => x i) ⁻¹' A) = gaussianReal 0 1 A := fun i =>
    (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).measure_preimage
      (measurableSet_le measurable_const measurable_abs).nullMeasurableSet
  have hμ : μ {x | t ≤ GEPPGrowth.Main.maxEntry (fun i (_ : Fin 1) => x i)} ≤
      n * gaussianReal 0 1 A :=
    calc _ ≤ μ (⋃ i, (fun x : Fin n → ℝ => x i) ⁻¹' A) := measure_mono hsub
      _ ≤ ∑ i, μ ((fun x : Fin n → ℝ => x i) ⁻¹' A) := measure_iUnion_fintype_le _ _
      _ = n * gaussianReal 0 1 A := by simp [hcoord]
  have h41 := GEPPGrowth.Main.lemma_4_1 t ht
  unfold GEPPGrowth.Main.prob at h41 ⊢
  calc (μ _).toReal ≤ (n * gaussianReal 0 1 A).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)) hμ
    _ = n * (gaussianReal 0 1 A).toReal := by simp
    _ ≤ n * (Real.sqrt 2 / (t*Real.sqrt Real.pi) * Real.exp (-t^2/2)) :=
        mul_le_mul_of_nonneg_left h41 (by positivity)
    _ = _ := by ring
