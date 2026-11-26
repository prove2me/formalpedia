-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.admissible_discounted_cost_aemeasurable
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:30:35.776636+00:00
-- url     : https://prove2.me/submissions/bfdbb553-cc9f-44b7-91de-f52adafe3e86

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_admissible_queue_regularity
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal

open BellWilliams2001.ThresholdPolicy
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

private theorem measurable_select_countable {Ω : Type*} [MeasurableSpace Ω]
    (w : ℕ → Ω → ℝ) (hw : ∀ k, Measurable (w k)) (idx : ℝ → ℕ)
    (hi : Measurable idx) : Measurable (fun z : Ω × ℝ => w (idx z.2) z.1) := by
  let select (z : Ω × ℕ) : ℝ := w z.2 z.1
  let project (z : Ω × ℝ) : Ω × ℕ := (z.1, idx z.2)
  have hselect : Measurable select := measurable_from_prod_countable_left hw
  have hproject : Measurable project := measurable_fst.prodMk (hi.comp measurable_snd)
  exact hselect.comp hproject

set_option maxHeartbeats 1300000 in
private theorem ae_joint_positive_part {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ → ℝ) (hm : ∀ t : ℝ, 0 ≤ t → AEMeasurable (fun ω => f ω t) P)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (f ω) (Ici t) t) :
    AEMeasurable (fun z : Ω × ℝ => ENNReal.ofReal (f z.1 z.2))
      (P.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let ceilIdx (n : ℕ) (t : ℝ) := Nat.ceil (t * (2:ℝ)^n)
  let time (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (2 : ℝ≥0)^n
  have hex (n k : ℕ) : ∃ g : Ω → ℝ, Measurable g ∧ (fun ω => f ω (time n k)) =ᵐ[P] g := by
    exact ⟨_, (hm (time n k) (time n k).2).measurable_mk,
      (hm (time n k) (time n k).2).ae_eq_mk⟩
  choose w hw hEq using hex
  let value (n : ℕ) (z : Ω × ℝ) := ENNReal.ofReal (w n (ceilIdx n z.2) z.1)
  have hv (n : ℕ) : Measurable (value n) := by
    have hidx : Measurable (ceilIdx n) := Nat.measurable_ceil.comp (measurable_id.mul_const _)
    exact (measurable_select_countable (w n) (hw n) (ceilIdx n) hidx).ennreal_ofReal
  let G (z : Ω × ℝ) := liminf (fun n => value n z) atTop
  have hG : Measurable G := Measurable.liminf hv
  refine hG.aemeasurable.congr ?_
  have hW : ∀ᵐ ω ∂P, ∀ n k : ℕ, f ω (time n k) = w n k ω := by
    exact ae_all_iff.2 (fun n => ae_all_iff.2 (hEq n))
  have hA : ∀ᵐ z : Ω × ℝ ∂P.prod (volume.restrict (Ioi (0 : ℝ))),
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (f z.1) (Ici t) t) ∧
        (∀ n k : ℕ, f z.1 (time n k) = w n k z.1) := by
    exact (Measure.quasiMeasurePreserving_fst (μ := P) (ν := volume.restrict (Ioi (0 : ℝ)))).ae
      (hR.and hW)
  have hT : ∀ᵐ z : Ω × ℝ ∂P.prod (volume.restrict (Ioi (0 : ℝ))), 0 ≤ z.2 := by
    apply (Measure.quasiMeasurePreserving_snd (μ := P) (ν := volume.restrict (Ioi (0 : ℝ)))).ae
    exact (ae_restrict_mem measurableSet_Ioi).mono fun _ ht => ht.le
  filter_upwards [hA,hT] with z hz ht
  have heq (n : ℕ) : time n (ceilIdx n z.2) =
      (Nat.ceil ((z.2.toNNReal : ℝ) * (2 : ℝ)^n) : ℝ≥0) / (2 : ℝ≥0)^n := by
    simp [time,ceilIdx,Real.coe_toNNReal,ht]
  have hConv : Tendsto (fun n => (time n (ceilIdx n z.2) : ℝ)) atTop (𝓝 z.2) := by
    have h := (NNReal.continuous_coe.tendsto z.2.toNNReal).comp
      (AvramDividend.Classical.dyadic_ceiling_nnreal_tendsto z.2.toNNReal)
    simpa only [Function.comp_def, Real.coe_toNNReal _ ht, heq] using h
  have hFrom : ∀ᶠ n in atTop, (time n (ceilIdx n z.2) : ℝ) ∈ Ici z.2 := by
    apply Eventually.of_forall
    intro n
    have h := AvramDividend.Classical.dyadic_ceiling_time_ge_nnreal z.2.toNNReal n
    have hr : (z.2.toNNReal : ℝ) ≤ (time n (ceilIdx n z.2) : ℝ) := by
      rw [heq]
      exact_mod_cast h
    exact mem_Ici.mpr (by simpa only [Real.coe_toNNReal _ ht] using hr)
  have hlim := (hz.1 z.2 ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hConv,hFrom⟩)
  have hl : Tendsto (fun n => value n z) atTop (𝓝 (ENNReal.ofReal (f z.1 z.2))) := by
    have hf := (ENNReal.continuous_ofReal.tendsto (f z.1 z.2)).comp hlim
    apply hf.congr
    intro n
    exact congrArg ENNReal.ofReal (hz.2 n (ceilIdx n z.2))
  exact hl.liminf_eq

set_option maxHeartbeats 1000000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (hT : M.IsAdmissible n T) :
    let f (ω : Ω) (t : ℝ) := ENNReal.ofReal (Real.exp (-M.gamma*t) * ∑ k, M.h k * M.Qhat n T ω t k)
    AEMeasurable (Function.uncurry f) (M.P.prod (volume.restrict (Ioi (0:ℝ)))) ∧
    AEMeasurable (fun ω => ∫⁻ t in Ioi (0:ℝ), f ω t ∂volume) M.P := by
  let S (ω : Ω) (t : ℝ) := ∑ k, M.h k*M.Qhat n T ω t k
  obtain ⟨hQ,hM⟩ := admissible_queue_regularity M n T hT
  have hs (t : ℝ) (ht : 0 ≤ t) : AEMeasurable (fun ω => S ω t) M.P := by
    simpa only [S,Fin.sum_univ_two,Pi.add_def] using
      ((hM t ht 0).const_mul (M.h 0)).add ((hM t ht 1).const_mul (M.h 1))
  have hr : ∀ᵐ ω ∂M.P, ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (S ω) (Ici t) t := by
    apply ae_of_all
    intro ω t ht
    simpa only [S,Fin.sum_univ_two,Pi.add_def] using
      (((hQ ω 0).1 t ht).const_mul (M.h 0)).add (((hQ ω 1).1 t ht).const_mul (M.h 1))
  have h := ae_joint_positive_part M.P S hs hr
  have hExp : Measurable (fun x : Ω × ℝ => ENNReal.ofReal (Real.exp (-M.gamma*x.2))) := by fun_prop
  have h' := hExp.aemeasurable.mul h
  have hJ : AEMeasurable (fun x : Ω × ℝ => ENNReal.ofReal
      (Real.exp (-M.gamma*x.2) * ∑ k, M.h k * M.Qhat n T x.1 x.2 k))
      (M.P.prod (volume.restrict (Ioi (0:ℝ)))) := by
    simpa only [S,Pi.mul_def,ENNReal.ofReal_mul (Real.exp_nonneg _)] using h'
  exact ⟨hJ,hJ.lintegral_prod_right'⟩
