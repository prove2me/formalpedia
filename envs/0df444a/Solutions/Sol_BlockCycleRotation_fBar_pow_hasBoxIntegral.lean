-- Prove2me | solution 1 for BlockCycleRotation.fBar_pow_hasBoxIntegral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:04:07.254449+00:00
-- url     : https://prove2.me/submissions/cfb04a32-9565-4631-aecc-f2a390729f8a

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_Outt_le
import Theorems.Thm_BlockCycleRotation_continuousAt_fCost
import Mathlib

open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem Inn_nonneg (x : ℝ) : 0 ≤ Inn x := by
  unfold Inn
  split_ifs
  · exact le_refl 0
  · have h1 : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
    positivity

/-- **`In` maps into `[0,1/2)`.**  Since `{1/x} < 1`, `{1/x}/(1+{1/x}) < 1/2`. -/
theorem Inn_lt_half (x : ℝ) : Inn x < 1 / 2 := by
  unfold Inn
  split_ifs
  · norm_num
  · have h1 : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
    have h2 : Int.fract (1 / x) < 1 := Int.fract_lt_one _
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith

theorem Outt_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Outt x := by
  unfold Outt
  split_ifs
  · exact le_refl 0
  · have h1 : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
    positivity

theorem iterate_Inn_mem {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    0 ≤ Inn^[i] x ∧ Inn^[i] x ≤ 1 / 2 := by
  cases i with
  | zero => exact ⟨hx0, hx⟩
  | succ j =>
    rw [Function.iterate_succ_apply']
    exact ⟨Inn_nonneg _, le_of_lt (Inn_lt_half _)⟩

theorem prod_Outt_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    (0 ≤ ∏ m ∈ Finset.range i, Outt (Inn^[m] x))
      ∧ (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) ≤ (2 / 3) ^ i := by
  constructor
  · refine Finset.prod_nonneg fun m _ => Outt_nonneg (iterate_Inn_mem hx0 hx m).1
  · calc (∏ m ∈ Finset.range i, Outt (Inn^[m] x))
        ≤ ∏ _m ∈ Finset.range i, (2 / 3 : ℝ) := by
          refine Finset.prod_le_prod (fun m _ => Outt_nonneg (iterate_Inn_mem hx0 hx m).1)
            (fun m _ => Outt_le (iterate_Inn_mem hx0 hx m).1 (iterate_Inn_mem hx0 hx m).2)
      _ = (2 / 3 : ℝ) ^ i := by rw [Finset.prod_const, Finset.card_range]

theorem psiTerm_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) : 0 ≤ psiTerm x i := by
  unfold psiTerm
  have h1 := (prod_Outt_le hx0 hx i).1
  have h2 := (iterate_Inn_mem hx0 hx i).1
  positivity

theorem psiTerm_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    psiTerm x i ≤ (2 / 3 : ℝ) ^ i := by
  unfold psiTerm
  obtain ⟨hp0, hp⟩ := prod_Outt_le hx0 hx i
  obtain ⟨hi0, hi⟩ := iterate_Inn_mem hx0 hx i
  have hpow : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ i := by positivity
  nlinarith

theorem psi_summable {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : Summable (psiTerm x) := by
  refine Summable.of_nonneg_of_le (psiTerm_nonneg hx0 hx) (psiTerm_le hx0 hx) ?_
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

theorem psi_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : 0 ≤ psi x :=
  tsum_nonneg (psiTerm_nonneg hx0 hx)

theorem psi_le_three {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : psi x ≤ 3 := by
  have hgeo : ∑' i : ℕ, (2 / 3 : ℝ) ^ i = 3 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  calc psi x ≤ ∑' i : ℕ, (2 / 3 : ℝ) ^ i :=
        (psi_summable hx0 hx).tsum_le_tsum (psiTerm_le hx0 hx)
          (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    _ = 3 := hgeo

theorem irrational_ne_zero {x : ℝ} (h : Irrational x) : x ≠ 0 := by
  intro hx
  exact Irrational.ne_int h 0 (by simp [hx])

theorem fCost_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) : 1 ≤ fCost x ∧ fCost x ≤ 4 := by
  have hm0 : 0 ≤ min x (1 - x) := le_min hx0 (by linarith)
  have hm : min x (1 - x) ≤ 1 / 2 := by
    rcases le_total x (1 - x) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  constructor
  · unfold fCost; linarith [psi_nonneg hm0 hm]
  · unfold fCost; linarith [psi_le_three hm0 hm]

theorem fBar_bounds (x : ℝ) : 1 ≤ fBar x ∧ fBar x ≤ 4 := by
  unfold fBar
  split_ifs with h
  · exact fCost_bounds h.1 h.2
  · constructor <;> norm_num

theorem abs_fBar_le (x : ℝ) : |fBar x| ≤ 4 := by
  obtain ⟨h1, h2⟩ := fBar_bounds x
  rw [abs_le]
  constructor <;> linarith

theorem fBar_eq_fCost {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) : fBar x = fCost x := by
  unfold fBar; rw [if_pos ⟨hx0, hx⟩]

theorem continuousAt_fBar {x : ℝ} (hirr : Irrational x) : ContinuousAt fBar x := by
  have hconst : ContinuousAt (fun _ : ℝ => (1 : ℝ)) x := continuousAt_const
  rcases lt_trichotomy x 0 with h | h | h
  · refine hconst.congr ?_
    filter_upwards [Iio_mem_nhds h] with y hy
    unfold fBar
    rw [if_neg (by simp only [not_and, not_le]; intro hc; linarith [Set.mem_Iio.1 hy])]
  · exact absurd h (irrational_ne_zero hirr)
  · rcases lt_trichotomy x 1 with h1 | h1 | h1
    · refine ContinuousAt.congr (continuousAt_fCost hirr h h1) ?_
      filter_upwards [Ioo_mem_nhds h h1] with y hy
      rw [fBar_eq_fCost (le_of_lt (Set.mem_Ioo.1 hy).1) (le_of_lt (Set.mem_Ioo.1 hy).2)]
    · exfalso
      have hx1 : x ≠ ((1 : ℤ) : ℝ) := Irrational.ne_int hirr 1
      simp only [Int.cast_one] at hx1
      exact hx1 h1
    · refine hconst.congr ?_
      filter_upwards [Ioi_mem_nhds h1] with y hy
      unfold fBar
      rw [if_neg (by simp only [not_and, not_le]; intro _; linarith [Set.mem_Ioi.1 hy])]

theorem ae_irrational : ∀ᵐ x : ℝ, Irrational x := by
  have hc : (Set.range ((↑) : ℚ → ℝ)).Countable := Set.countable_range _
  have h0 : volume (Set.range ((↑) : ℚ → ℝ)) = 0 := hc.measure_zero _
  rw [Filter.eventually_iff, mem_ae_iff]
  refine measure_mono_null (fun x hx => ?_) h0
  by_contra hcon
  exact hx hcon

theorem measurePreserving_eval :
    MeasureTheory.MeasurePreserving (fun v : Fin 1 → ℝ => v 0) volume volume := by
  have h := MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ
  exact h

theorem ae_continuousAt_FBar :
    ∀ᵐ v : Fin 1 → ℝ, ContinuousAt FBar v := by
  have hmeas : MeasurableSet {x : ℝ | ¬ Irrational x} := by
    have : {x : ℝ | ¬ Irrational x} = Set.range ((↑) : ℚ → ℝ) := by
      ext x
      simp only [Set.mem_setOf_eq, Irrational, not_not]
    rw [this]
    exact (Set.countable_range _).measurableSet
  have hnull : volume {x : ℝ | ¬ Irrational x} = 0 := by
    have := ae_irrational
    rw [Filter.eventually_iff, mem_ae_iff] at this
    exact this
  have hpre : volume ((fun v : Fin 1 → ℝ => v 0) ⁻¹' {x : ℝ | ¬ Irrational x}) = 0 := by
    rw [measurePreserving_eval.measure_preimage hmeas.nullMeasurableSet]
    exact hnull
  rw [Filter.eventually_iff, mem_ae_iff]
  refine measure_mono_null (fun v hv => ?_) hpre
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hv ⊢
  intro hirr
  exact hv (ContinuousAt.comp (g := fBar) (f := fun w : Fin 1 → ℝ => w 0)
    (continuousAt_fBar hirr) (continuous_apply (0 : Fin 1)).continuousAt)

theorem abs_fBar_pow_le (j : ℕ) (x : ℝ) : |fBar x ^ j| ≤ 4 ^ j := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_fBar_le x) j

theorem ae_continuousAt_FBar_pow (j : ℕ) :
    ∀ᵐ v : Fin 1 → ℝ, ContinuousAt (fun w : Fin 1 → ℝ => FBar w ^ j) v :=
  ae_continuousAt_FBar.mono fun v hv => hv.pow j

end BlockCycleRotation

open BlockCycleRotation in
set_option maxHeartbeats 1000000 in
-- The Riemann-Lebesgue criterion carries a large elaboration burden.
/-- **`f^j` is Riemann integrable**, so the `j`-th moment exists. -/
theorem solution (j : ℕ) :
    HasIntegral unitBox IntegrationParams.Riemann (fun v : Fin 1 → ℝ => FBar v ^ j)
      (BoxAdditiveMap.toSMul (MeasureTheory.Measure.toBoxAdditive volume))
      (∫ v in (unitBox : Set (Fin 1 → ℝ)), FBar v ^ j):= by
  refine AEContinuous.hasBoxIntegral (volume : MeasureTheory.Measure (Fin 1 → ℝ))
    ⟨4 ^ j, fun x _ => ?_⟩ (ae_continuousAt_FBar_pow j) IntegrationParams.Riemann
  rw [Real.norm_eq_abs, FBar]
  exact abs_fBar_pow_le j _
