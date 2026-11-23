-- Prove2me | solution 1 for CalibeatBandit.expected_swapRegret_ge_proxy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T18:47:36.150941+00:00
-- url     : https://prove2.me/submissions/401e6df0-0d8b-48b4-bfc8-52fd2246a266

import Mathlib
import Definitions.Def_CalibeatBandit_lower_bound_models
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_hard_tree_environment
import Definitions.Def_CalibeatBandit_hard_tree_analysis
import Theorems.Thm_CalibeatBandit_lemma_4_10

section

set_option autoImplicit false
set_option maxHeartbeats 150000

open Matrix MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}

theorem measurable_select {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {a : Ω → α} (ha : Measurable a)
    {f : α → Ω → ℝ} (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => f (a ω) ω) := by
  classical
  have heq : (fun ω => f (a ω) ω) =
      fun ω => ∑ i, if a ω = i then f i ω else 0 := by
    funext ω
    simp
  rw [heq]
  exact Finset.measurable_sum _ fun i _ => Measurable.ite (ha (measurableSet_singleton i)) (hf i) measurable_const

end Measurability

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

theorem integrable_of_abs_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → ℝ} (hm : Measurable f) {B : ℝ}
    (hb : ∀ ω, |f ω| ≤ B) : Integrable f P :=
  (integrable_const B).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hb ω)

theorem integrable_finset_max {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsFiniteMeasure P] (hne : (Finset.univ : Finset ι).Nonempty)
    (F : ι → Ω → ℝ) {B : ℝ} (hm : ∀ i, Measurable (F i)) (hb : ∀ i ω, |F i ω| ≤ B) :
    Integrable (fun ω => Finset.univ.sup' hne (fun i => F i ω)) P := by
  let _ : Nonempty ι := hne.to_subtype.map Subtype.val
  apply integrable_of_abs_bound
  · simp_rw [Finset.sup'_univ_eq_ciSup]
    exact Measurable.iSup hm
  · intro ω
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (fun i => F i ω)
    exact hi.symm ▸ hb i ω

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit

theorem swapGain_le_best {K T : ℕ} (q u : ℕ → Fin K → ℝ) (i j : Fin K) :
    swapGain T q u i j ≤ bestSwapGain T q u i :=
  Finset.le_sup' (swapGain T q u i) (Finset.mem_univ j)

/-- The swap map can maximize every row independently. -/
theorem pseudoSwapRegret_eq_sum_bestSwapGain {K : ℕ} (T : ℕ) (q u : ℕ → Fin K → ℝ) :
    pseudoSwapRegret T q u = ∑ i, bestSwapGain T q u i := by
  classical
  have score (f : Fin K → Fin K) :
      (∑ t ∈ Finset.range T, ((∑ i, q t i * u t (f i)) - q t ⬝ᵥ u t)) =
        ∑ i, swapGain T q u i (f i) := by
    unfold swapGain dotProduct
    have h (t : ℕ) : (∑ i, q t i * u t (f i)) - ∑ i, q t i * u t i =
        ∑ i, q t i * (u t (f i) - u t i) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    simp_rw [h]
    exact Finset.sum_comm
  unfold pseudoSwapRegret
  simp_rw [score]
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun f _ => Finset.sum_le_sum fun i _ => swapGain_le_best q u i (f i)
  · have exists_best (i : Fin K) : ∃ j, bestSwapGain T q u i = swapGain T q u i j := by
      obtain ⟨j, _, h⟩ := Finset.exists_mem_eq_sup' ⟨i, Finset.mem_univ i⟩ (swapGain T q u i)
      exact ⟨j, h⟩
    choose f hf using exists_best
    calc
      _ = ∑ i, swapGain T q u i (f i) := Finset.sum_congr rfl fun i _ => hf i
      _ ≤ _ := Finset.le_sup' (fun f : Fin K → Fin K => ∑ i, swapGain T q u i (f i))
        (Finset.mem_univ f)

/-- The conversion from the proxy swap gain to realized swap regret.
The error for each action is bounded by its largest row deviation. -/
theorem swapRegret_ge_proxy {K T : ℕ} (a : ℝ)
    (q u y : ℕ → Fin K → ℝ) (I : ℕ → Fin K) :
    a * pseudoSwapRegret T q u -
      (∑ i : Fin K, Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ (fun j =>
        |swapGain T (fun t => Pi.single (I t) 1) y i j - a * swapGain T q u i j|)) ≤
      swapRegret T y I := by
  classical
  let played (t : ℕ) : Fin K → ℝ := Pi.single (I t) 1
  have hplayed : swapRegret T y I = pseudoSwapRegret T played y := by
    unfold swapRegret pseudoSwapRegret
    simp [played, dotProduct, Pi.single_apply, Finset.sum_ite_eq']
  rw [hplayed, pseudoSwapRegret_eq_sum_bestSwapGain, pseudoSwapRegret_eq_sum_bestSwapGain,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup' ⟨i, Finset.mem_univ i⟩ (swapGain T q u i)
  change bestSwapGain T q u i = swapGain T q u i j at heq
  have herr := Finset.le_sup' (fun j => |swapGain T played y i j - a * swapGain T q u i j|) hj
  change a * bestSwapGain T q u i -
      Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ (fun j =>
        |swapGain T played y i j - a * swapGain T q u i j|) ≤ bestSwapGain T played y i
  rw [heq]
  have h₁ := neg_le_abs (swapGain T played y i j - a * swapGain T q u i j)
  have h₂ := swapGain_le_best (T := T) played y i j
  linarith only [herr, h₁, h₂]

set_option maxHeartbeats 450000 in
/-- The final martingale comparison for the discrete lower bound. Each
increment is the observed swap gain minus its conditional prediction. -/
theorem expected_swapRegret_ge_proxy {K T : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (info : Filtration ℕ mΩ)
    (anchor : Fin K) (a c : ℝ) (hc : 0 < c)
    (q u y : Ω → ℕ → Fin K → ℝ) (I : Ω → ℕ → Fin K)
    (hy : ∀ t < T, ∀ ω j, y ω t j ∈ Set.Icc (0 : ℝ) 1)
    (hym : ∀ t < T, ∀ j, Measurable (fun ω => y ω t j))
    (hI : ∀ t < T, Measurable (fun ω => I ω t))
    (hq : ∀ t < T, ∀ ω, IsProbVec (q ω t))
    (hu : ∀ t < T, ∀ ω j, u ω t j ∈ Set.Icc (0 : ℝ) 1)
    (hqm : ∀ t < T, ∀ j, Measurable (fun ω => q ω t j))
    (hum : ∀ t < T, ∀ j, Measurable (fun ω => u ω t j)) :
    let d (i : Fin K) (t : ℕ) (j : Fin K) (ω : Ω) :=
      (Pi.single (I ω t) (1 : ℝ) : Fin K → ℝ) i * (y ω t j - y ω t i) -
        a * (q ω t i * (u ω t j - u ω t i))
    (∀ t < T, ∀ i j, Measurable[info (t + 1)] (d i t j)) →
    (∀ t < T, ∀ i j ω, |d i t j ω| ≤ c) →
    (∀ t < T, ∀ i j, condExp (info t) P (d i t j) =ᵐ[P] 0) →
    a * (∫ ω, pseudoSwapRegret T (q ω) (u ω) ∂P) -
      K * (c * Real.sqrt (2 * T * Real.log (2 * K))) ≤
      ∫ ω, swapRegret T (y ω) (I ω) ∂P := by
  classical
  intro d hdm hdb hdc
  let _ : Nonempty (Fin K) := ⟨anchor⟩
  let D (i : Fin K) (ω : Ω) :=
    Finset.univ.sup' Finset.univ_nonempty (fun j => |∑ t ∈ Finset.range T, d i t j ω|)
  have hD (i : Fin K) : Integrable (D i) P := by
    apply integrable_finset_max Finset.univ_nonempty _ (B := (T : ℝ) * c)
    · intro j
      have h : Measurable (fun ω => ∑ t ∈ Finset.range T, d i t j ω) :=
        Finset.measurable_sum _ fun t ht =>
          (hdm t (Finset.mem_range.mp ht) i j).mono (info.le _) le_rfl
      exact continuous_abs.measurable.comp h
    · intro j ω
      rw [abs_abs]
      calc
        _ ≤ ∑ t ∈ Finset.range T, |d i t j ω| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ Finset.range T, c := Finset.sum_le_sum fun t ht =>
          hdb t (Finset.mem_range.mp ht) i j ω
        _ = _ := by simp
  have d_bound (i : Fin K) : ∫ ω, D i ω ∂P ≤ c * Real.sqrt (2 * T * Real.log (2 * K)) := by
    simpa only [Fintype.card_fin] using lemma_4_10 P info hc (d i)
      (fun t ht j => hdm t ht i j) (fun t ht j => hdb t ht i j) (fun t ht j => hdc t ht i j)
  have sum_bound (F : ℕ → Ω → ℝ) (hF : ∀ t < T, ∀ ω, |F t ω| ≤ 1) (ω : Ω) :
      |∑ t ∈ Finset.range T, F t ω| ≤ (T : ℝ) := by
    calc
      _ ≤ ∑ t ∈ Finset.range T, |F t ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum fun t ht =>
        hF t (Finset.mem_range.mp ht) ω
      _ = _ := by simp
  have diff_bound {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
      |x - y| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
  have hreal : Integrable (fun ω => swapRegret T (y ω) (I ω)) P := by
    unfold swapRegret
    apply integrable_finset_max ⟨id, Finset.mem_univ _⟩ _ (B := T)
    · intro f
      exact Finset.measurable_sum _ fun t ht =>
        (measurable_select (hI t (Finset.mem_range.mp ht)) (fun j => hym t (Finset.mem_range.mp ht) (f j))).sub
          (measurable_select (hI t (Finset.mem_range.mp ht)) (hym t (Finset.mem_range.mp ht)))
    · intro f ω
      exact sum_bound (fun t ω => y ω t (f (I ω t)) - y ω t (I ω t))
        (fun t ht ω => diff_bound (hy t ht ω _) (hy t ht ω _)) ω
  have hproxy : Integrable (fun ω => pseudoSwapRegret T (q ω) (u ω)) P := by
    unfold pseudoSwapRegret
    apply integrable_finset_max ⟨id, Finset.mem_univ _⟩ _ (B := T)
    · intro f
      exact Finset.measurable_sum _ fun t ht =>
        (Finset.measurable_sum _ fun i _ => (hqm t (Finset.mem_range.mp ht) i).mul
          (hum t (Finset.mem_range.mp ht) (f i))).sub (Finset.measurable_sum _ fun i _ =>
          (hqm t (Finset.mem_range.mp ht) i).mul (hum t (Finset.mem_range.mp ht) i))
    · intro f ω
      apply sum_bound (fun t ω => (∑ i, q ω t i * u ω t (f i)) - q ω t ⬝ᵥ u ω t) _ ω
      intro t ht ω
      have he : (∑ i, q ω t i * u ω t (f i)) - q ω t ⬝ᵥ u ω t =
          ∑ i, q ω t i * (u ω t (f i) - u ω t i) := by
        simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
      rw [he]
      calc
        _ ≤ ∑ i, |q ω t i * (u ω t (f i) - u ω t i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, q ω t i := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_nonneg ((hq t ht ω).1 i)]
          exact mul_le_of_le_one_right ((hq t ht ω).1 i) (diff_bound (hu t ht ω _) (hu t ht ω _))
        _ = 1 := (hq t ht ω).2
  have heq (ω : Ω) (i : Fin K) :
      Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ (fun j =>
        |swapGain T (fun t => Pi.single (I ω t) 1) (y ω) i j -
          a * swapGain T (q ω) (u ω) i j|) = D i ω := by
    unfold D
    congr 1
    funext j
    congr 1
    simp only [d, swapGain, Finset.mul_sum, Finset.sum_sub_distrib]
  have hp (ω : Ω) := swapRegret_ge_proxy (T := T) a (q ω) (u ω) (y ω) (I ω)
  simp_rw [heq] at hp
  have hi : Integrable (fun ω => ∑ i, D i ω) P := integrable_finsetSum _ fun i _ => hD i
  have hi' : Integrable (fun ω => a * pseudoSwapRegret T (q ω) (u ω) - ∑ i, D i ω) P :=
    (hproxy.const_mul a).sub hi
  have hle := integral_mono hi' hreal hp
  have h' : (∫ ω, a * pseudoSwapRegret T (q ω) (u ω) - ∑ i, D i ω ∂P) =
      a * (∫ ω, pseudoSwapRegret T (q ω) (u ω) ∂P) - ∑ i, ∫ ω, D i ω ∂P := by
    rw [integral_sub (hproxy.const_mul a) hi, integral_const_mul, integral_finsetSum _ (fun i _ => hD i)]
  rw [h'] at hle
  have hs : (∑ i, ∫ ω, D i ω ∂P) ≤ K * (c * Real.sqrt (2 * T * Real.log (2 * K))) := by
    calc
      _ ≤ ∑ _ : Fin K, c * Real.sqrt (2 * T * Real.log (2 * K)) :=
        Finset.sum_le_sum fun i _ => d_bound i
      _ = _ := by simp
  linarith only [hs, hle]

end CalibeatBandit

end

theorem solution : type_of% @CalibeatBandit.expected_swapRegret_ge_proxy := @CalibeatBandit.expected_swapRegret_ge_proxy
