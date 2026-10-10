-- Prove2me | solution 1 for BookProof.MollifierL2.tendsto_translate_Lp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T22:05:53.652978+00:00
-- url     : https://prove2.me/submissions/97958c4f-0f1a-47fc-817d-60a340101738

-- Generated from ChapterMollifierL2.lean — solution of BookProof.MollifierL2.tendsto_translate_Lp
import Mathlib
import Definitions.Def_ChapterMollifierL2
import Theorems.Thm_BookProof_MollifierL2_eLpNorm_translate
import Theorems.Thm_BookProof_MollifierL2_tendsto_translate_cc
open BookProof.MollifierL2




open MeasureTheory Filter ENNReal Pointwise
open scoped NNReal Topology

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

set_option maxHeartbeats 1000000 in
theorem solution {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) (hp1 : 1 ≤ p) {f : E → F}
    (hf : MemLp f p μ) :
    Tendsto (fun a : E => eLpNorm (fun x => f (x - a) - f x) p μ) (𝓝 0) (𝓝 0) := by

  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨g, hgcs, hgle, hgc, hgmem⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (p := p) hp (ε := ε / 4) (by simp [hε.ne'])
  set h : E → F := fun x => f x - g x with hh
  have hhmeas : AEStronglyMeasurable h μ := hf.1.sub hgmem.1
  have hhle : eLpNorm h p μ ≤ ε / 4 := hgle
  have hmid := tendsto_translate_cc (μ := μ) hp0 hp hgc hgcs
  rw [ENNReal.tendsto_nhds_zero] at hmid
  filter_upwards [hmid (ε / 4) (by simp [hε.ne'])] with a hamid
  have hsplit : (fun x => f (x - a) - f x)
      = ((fun y : E => h (y - a)) + (fun y : E => g (y - a) - g y)) + (fun y : E => -h y) := by
    funext x
    simp only [Pi.add_apply, hh]
    abel
  have hm1 : AEStronglyMeasurable (fun x : E => h (x - a)) μ :=
    hhmeas.comp_measurePreserving (measurePreserving_sub_right μ a)
  have hm2 : AEStronglyMeasurable (fun x : E => g (x - a) - g x) μ :=
    ((hgc.comp (continuous_id.sub continuous_const)).sub hgc).aestronglyMeasurable
  have hstep : eLpNorm (fun x => f (x - a) - f x) p μ
      ≤ (eLpNorm (fun x : E => h (x - a)) p μ + eLpNorm (fun x : E => g (x - a) - g x) p μ)
        + eLpNorm (fun x : E => -h x) p μ := by
    rw [hsplit]
    refine le_trans (eLpNorm_add_le (hm1.add hm2) hhmeas.neg hp1) ?_
    gcongr
    exact eLpNorm_add_le hm1 hm2 hp1
  have e1 : eLpNorm (fun x : E => h (x - a)) p μ = eLpNorm h p μ := eLpNorm_translate hhmeas a
  have e3 : eLpNorm (fun x : E => -h x) p μ = eLpNorm h p μ := by
    rw [show (fun x : E => -h x) = -h from rfl, eLpNorm_neg]
  rw [e1, e3] at hstep
  have hbound : eLpNorm h p μ + eLpNorm (fun x : E => g (x - a) - g x) p μ + eLpNorm h p μ
      ≤ ε / 4 + ε / 4 + ε / 4 := by gcongr
  have hfin : ε / 4 + ε / 4 + ε / 4 ≤ ε := by
    have h4 : ε / 4 + ε / 4 + ε / 4 + ε / 4 = ε := by
      rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same,
        show ε + ε + ε + ε = ε * 4 by ring]
      exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
    calc ε / 4 + ε / 4 + ε / 4 ≤ ε / 4 + ε / 4 + ε / 4 + ε / 4 := le_self_add
      _ = ε := h4
  exact hstep.trans (hbound.trans hfin)
