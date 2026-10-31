-- Prove2me | solution 1 for FiniteMemQL.Convergence.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T06:06:26.694997+00:00
-- url     : https://prove2.me/submissions/3f4a1cd9-7ba5-483b-bb84-c4d78585246f

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_FiniteMemQL_Convergence_Model
import Definitions.Def_FiniteMemQL_Convergence_Setting
import Theorems.Thm_FiniteMemQL_Convergence_qStar_fixed_point
import Theorems.Thm_FiniteMemQL_Convergence_qStar_min_eq_JN

open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace FMQC

open FiniteMemQL.Convergence
open scoped ENNReal

lemma inf_diff {U : Type*} [Fintype U] [Nonempty U] (f g : U → ℝ) (d : ℝ)
    (h : ∀ v, |f v - g v| ≤ d) : |(⨅ v, f v) - ⨅ v, g v| ≤ d := by
  rw [abs_le]
  constructor
  · have : (⨅ v, g v) - d ≤ ⨅ v, f v := le_ciInf fun v => by
      linarith [ciInf_le (Finite.bddBelow_range g) v, (abs_le.mp (h v)).1]
    linarith
  · have : (⨅ v, f v) - d ≤ ⨅ v, g v := le_ciInf fun v => by
      linarith [ciInf_le (Finite.bddBelow_range f) v, (abs_le.mp (h v)).2]
    linarith

lemma inf_lip {U : Type*} [Fintype U] [Nonempty U] :
    Continuous (fun f : U → ℝ => ⨅ v : U, f v) := by
  have : LipschitzWith 1 (fun f : U → ℝ => ⨅ v : U, f v) := by
    refine LipschitzWith.of_dist_le_mul fun f g => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul]
    exact inf_diff _ _ _ fun v => by rw [← Real.dist_eq]; exact dist_le_pi_dist f g v
  exact this.continuous

variable {X Y U : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]

lemma normalize_univ_le (μ : Measure X) : FiniteMemQL.Convergence.normalize μ Set.univ ≤ 1 := by
  unfold FiniteMemQL.Convergence.normalize
  rw [Measure.smul_apply, smul_eq_mul]
  rcases eq_or_ne (μ Set.univ) 0 with h0 | h0
  · rw [h0, mul_zero]; exact zero_le_one
  rcases eq_or_ne (μ Set.univ) ⊤ with ht | ht
  · rw [ht]; simp
  · rw [ENNReal.inv_mul_cancel h0 ht]

lemma predict_univ (M : POMDP X Y U) (μ : Measure X) (u : U) :
    predict M μ u Set.univ = μ Set.univ := by
  unfold predict
  have hm : Measurable (fun x => M.T (x, u)) :=
    M.T.measurable.comp (measurable_id.prodMk measurable_const)
  rw [Measure.bind_apply MeasurableSet.univ hm.aemeasurable]
  simp

lemma sum_correct [Fintype Y] [MeasurableSingletonClass Y] (M : POMDP X Y U) (ν : Measure X) :
    ∑ y : Y, correct M ν y Set.univ = ν Set.univ := by
  unfold correct
  simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← lintegral_finset_sum _ (fun y _ => M.O.measurable_coe (measurableSet_singleton y))]
  have : ∀ x, ∑ y : Y, M.O x {y} = 1 := by
    intro x
    rw [sum_measure_singleton]
    simp
  simp only [this, lintegral_const, one_mul]

lemma correct_univ_le [Fintype Y] [MeasurableSingletonClass Y] (M : POMDP X Y U)
    (ν : Measure X) (y : Y) : correct M ν y Set.univ ≤ ν Set.univ := by
  rw [← sum_correct M ν]
  exact Finset.single_le_sum (f := fun y => correct M ν y Set.univ) (fun _ _ => zero_le)
    (Finset.mem_univ y)

lemma correct_smul (M : POMDP X Y U) (c : ℝ≥0∞) (μ : Measure X) (y : Y) :
    correct M (c • μ) y = c • correct M μ y := by
  unfold correct; exact withDensity_smul_measure c _

lemma predict_smul (M : POMDP X Y U) (c : ℝ≥0∞) (μ : Measure X) (u : U) :
    predict M (c • μ) u = c • predict M μ u := by
  unfold predict; exact Measure.bind_smul c μ _

lemma unnormPost_smul (M : POMDP X Y U) (N : ℕ) :
    ∀ (c : ℝ≥0∞) (π : Measure X) (I : Window Y U N),
      unnormPost M N (c • π) I = c • unnormPost M N π I := by
  induction N with
  | zero => intro c π I; exact correct_smul M c π _
  | succ N ih =>
    intro c π I
    simp only [unnormPost]
    rw [correct_smul, predict_smul, ih]

lemma normalize_smul (μ : Measure X) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hμ : μ Set.univ ≠ ⊤) : FiniteMemQL.Convergence.normalize (c • μ) =
      FiniteMemQL.Convergence.normalize μ := by
  unfold FiniteMemQL.Convergence.normalize
  rw [Measure.smul_apply, smul_eq_mul, smul_smul]
  rcases eq_or_ne (μ Set.univ) 0 with h0 | h0
  · rw [Measure.measure_univ_eq_zero.1 h0]; simp
  · congr 1
    rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), mul_comm c⁻¹, mul_assoc,
      ENNReal.inv_mul_cancel hc0 hct, mul_one]

lemma eq_smul_normalize (μ : Measure X) (hμ : μ Set.univ ≠ ⊤) :
    μ = μ Set.univ • FiniteMemQL.Convergence.normalize μ := by
  unfold FiniteMemQL.Convergence.normalize
  rw [smul_smul]
  rcases eq_or_ne (μ Set.univ) 0 with h0 | h0
  · rw [Measure.measure_univ_eq_zero.1 h0]; simp
  · rw [ENNReal.mul_inv_cancel h0 hμ, one_smul]

lemma tail_snoc' {α : Type*} {n : ℕ} (p : Fin (n + 1) → α) (x : α) :
    Fin.tail (Fin.snoc (α := fun _ => α) p x) = Fin.snoc (α := fun _ => α) (Fin.tail p) x := by
  conv_lhs => rw [← Fin.cons_self_tail p]
  rw [← Fin.cons_snoc_eq_snoc_cons, Fin.tail_cons]

lemma unnormPost_snoc (M : POMDP X Y U) (N : ℕ) :
    ∀ (π : Measure X) (ys : Fin (N + 1) → Y) (us : Fin N → U) (u : U) (y : Y),
      unnormPost M (N + 1) π (Fin.snoc (α := fun _ => Y) ys y, Fin.snoc (α := fun _ => U) us u) =
        correct M (predict M (unnormPost M N π (ys, us)) u) y := by
  induction N with
  | zero =>
    intro π ys us u y
    simp only [unnormPost]
    congr 2
  | succ N ih =>
    intro π ys us u y
    rw [unnormPost]
    simp only
    rw [tail_snoc', tail_snoc', ih]
    simp only [unnormPost]
    rw [Fin.snoc_apply_zero, Fin.snoc_apply_zero]

lemma unnormPost_univ_le [Fintype Y] [MeasurableSingletonClass Y] (M : POMDP X Y U) (N : ℕ) :
    ∀ (π : Measure X) (I : Window Y U N), unnormPost M N π I Set.univ ≤ π Set.univ := by
  induction N with
  | zero => intro π I; exact correct_univ_le M π _
  | succ N ih =>
    intro π I
    simp only [unnormPost]
    refine (ih _ _).trans ?_
    rw [predict_univ]
    exact correct_univ_le M π _

/-- Bayes consistency of the window posterior with the filter update. -/
lemma post_nextPrior [Fintype Y] [MeasurableSingletonClass Y] (M : POMDP X Y U) {N : ℕ}
    (π : Measure X) [IsFiniteMeasure π] (I : Window Y U N) (u : U) (y : Y)
    (hc : correct M π (I.1 0) Set.univ ≠ 0) :
    post M (nextPrior M π I u) (shift I u y) = filterUpdate M (post M π I) u y := by
  set a := correct M π (I.1 0) with ha
  have hat : a Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top π _) (correct_univ_le M π _)
  have hm : unnormPost M N π I Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top π _) (unnormPost_univ_le M N π I)
  have e1 : unnormPost M N (nextPrior M π I u) (shift I u y) =
      (a Set.univ)⁻¹ • correct M (predict M (unnormPost M N π I) u) y := by
    unfold nextPrior FiniteMemQL.Convergence.normalize
    rw [predict_smul, unnormPost_smul, ← ha]
    congr 1
    rw [← unnormPost_snoc]
    simp only [unnormPost, shift]
    simp only [Fin.snoc_apply_zero, ha]
  unfold post filterUpdate
  rw [e1]
  have hfin : correct M (predict M (unnormPost M N π I) u) y Set.univ ≠ ⊤ := by
    refine ne_top_of_le_ne_top hm ?_
    exact (correct_univ_le M _ y).trans (predict_univ M _ u).le
  rw [normalize_smul _ _ (ENNReal.inv_ne_zero.2 hat) (ENNReal.inv_ne_top.2 hc) hfin]
  -- normalize (correct (predict m)) = normalize (correct (predict (normalize m)))
  conv_lhs => rw [eq_smul_normalize (unnormPost M N π I) hm]
  rw [predict_smul, correct_smul]
  rcases eq_or_ne (unnormPost M N π I Set.univ) 0 with h0 | h0
  · rw [h0, zero_smul]
    have : FiniteMemQL.Convergence.normalize (unnormPost M N π I) = 0 := by
      unfold FiniteMemQL.Convergence.normalize
      rw [Measure.measure_univ_eq_zero.1 h0, smul_zero]
    rw [this]
    unfold FiniteMemQL.Convergence.normalize
    simp [predict, correct]
  · have hfin2 : correct M (predict M (FiniteMemQL.Convergence.normalize
        (unnormPost M N π I)) u) y Set.univ ≠ ⊤ := by
      refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      exact (correct_univ_le M _ y).trans ((predict_univ M _ u).le.trans (normalize_univ_le _))
    rw [normalize_smul _ _ h0 hm hfin2]

lemma unnormPost_univ_le_correct [Fintype Y] [MeasurableSingletonClass Y] (M : POMDP X Y U)
    (N : ℕ) (π : Measure X) (I : Window Y U N) :
    unnormPost M N π I Set.univ ≤ correct M π (I.1 0) Set.univ := by
  cases N with
  | zero => exact le_rfl
  | succ N =>
    simp only [unnormPost]
    refine (unnormPost_univ_le M N _ _).trans ?_
    rw [predict_univ]

section JS

variable [Fintype Y] [Fintype U] [Nonempty U] [MeasurableSingletonClass Y]

lemma sum_obsProb_le (M : POMDP X Y U) (z : Measure X) (hz : z Set.univ ≤ 1) (u : U) :
    ∑ y : Y, obsProb M z u y ≤ 1 := by
  set ν := predict M z u with hν
  have hνle : ν Set.univ ≤ 1 := by rw [hν, predict_univ]; exact hz
  have hfin : ∀ y, correct M ν y Set.univ ≠ ⊤ := fun y =>
    ne_top_of_le_ne_top ENNReal.one_ne_top ((correct_univ_le M ν y).trans hνle)
  have : ∑ y : Y, obsProb M z u y = (∑ y : Y, correct M ν y Set.univ).toReal := by
    rw [ENNReal.toReal_sum (fun y _ => hfin y)]
    rfl
  rw [this, sum_correct]
  calc (ν Set.univ).toReal ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hνle
    _ = 1 := ENNReal.toReal_one

lemma beliefCost_bdd (M : POMDP X Y U) (B : ℝ) (hB : ∀ x u, |M.c x u| ≤ B) (hB0 : 0 ≤ B)
    (z : Measure X) (hz : z Set.univ ≤ 1) (u : U) : |beliefCost M z u| ≤ B := by
  haveI : IsFiniteMeasure z := ⟨lt_of_le_of_lt hz ENNReal.one_lt_top⟩
  unfold beliefCost
  have h := norm_integral_le_of_norm_le_const (μ := z) (f := fun x => M.c x u) (C := B)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x u)
  rw [Real.norm_eq_abs] at h
  refine h.trans ?_
  have : z.real Set.univ ≤ 1 := by
    unfold Measure.real
    calc (z Set.univ).toReal ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hz
      _ = 1 := ENNReal.toReal_one
  have h0 : 0 ≤ z.real Set.univ := measureReal_nonneg
  nlinarith

lemma bellman_lip (M : POMDP X Y U) (V W : Measure X → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (h : ∀ F : Measure X, F Set.univ ≤ 1 → |V F - W F| ≤ d) (z : Measure X)
    (hz : z Set.univ ≤ 1) : |beliefBellman M V z - beliefBellman M W z| ≤ M.β * d := by
  have hβ0 := M.β_pos
  unfold beliefBellman
  apply inf_diff
  intro u
  rw [add_sub_add_left_eq_sub, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos hβ0]
  apply mul_le_mul_of_nonneg_left _ hβ0.le
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ y : Y, |obsProb M z u y * V (filterUpdate M z u y)
        - obsProb M z u y * W (filterUpdate M z u y)|
      ≤ ∑ y : Y, obsProb M z u y * d := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ obsProb M z u y from
          ENNReal.toReal_nonneg)]
        exact mul_le_mul_of_nonneg_left (h _ (normalize_univ_le _)) ENNReal.toReal_nonneg
    _ = (∑ y : Y, obsProb M z u y) * d := by rw [Finset.sum_mul]
    _ ≤ 1 * d := mul_le_mul_of_nonneg_right (sum_obsProb_le M z hz u) hd
    _ = d := one_mul _

/-- `J*_β` is a fixed point of the belief Bellman operator at every sub-probability measure. -/
lemma jstar_fix (M : POMDP X Y U) (z : Measure X) (hz : z Set.univ ≤ 1) :
    Jstar M z = beliefBellman M (Jstar M) z := by
  obtain ⟨B0, hB0⟩ := M.c_bdd
  set B := max B0 0 with hBdef
  have hB : ∀ x u, |M.c x u| ≤ B := fun x u => (hB0 x u).trans (le_max_left _ _)
  have hBnn : 0 ≤ B := le_max_right _ _
  have hβ0 := M.β_pos
  have hβ1 := M.β_lt_one
  set V : ℕ → Measure X → ℝ := fun n => (beliefBellman M)^[n] 0 with hVdef
  have hFU : ∀ z u y, filterUpdate M z u y Set.univ ≤ 1 := fun _ _ _ => normalize_univ_le _
  have hstep : ∀ n z, z Set.univ ≤ 1 → |V (n + 1) z - V n z| ≤ B * M.β ^ n := by
    intro n
    induction n with
    | zero =>
      intro z hz
      simp only [hVdef, Function.iterate_zero, id, pow_zero, mul_one]
      unfold beliefBellman
      have e : (0 : Measure X → ℝ) z = ⨅ _ : U, (0 : ℝ) := by simp
      rw [e]
      apply inf_diff
      intro v
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, sub_zero]
      exact beliefCost_bdd M B hB hBnn z hz v
    | succ n ih =>
      intro z hz
      have e : ∀ m, V (m + 1) = beliefBellman M (V m) := fun m =>
        Function.iterate_succ_apply' _ _ _
      have := bellman_lip M (V (n + 1)) (V n) (B * M.β ^ n) (by positivity)
        (fun F hF => ih F hF) z hz
      rw [← e (n + 1), ← e n] at this
      calc |V (n + 1 + 1) z - V (n + 1) z| ≤ M.β * (B * M.β ^ n) := this
        _ = B * M.β ^ (n + 1) := by ring
  have hconv : ∀ z, z Set.univ ≤ 1 → Tendsto (fun n => V n z) atTop (𝓝 (Jstar M z)) := by
    intro z hz
    have hc : CauchySeq (fun n => V n z) := by
      refine cauchySeq_of_le_geometric M.β B hβ1 fun n => ?_
      rw [Real.dist_eq, abs_sub_comm]
      exact hstep n z hz
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have : Jstar M z = L := hL.limUnder_eq
    rw [this]; exact hL
  have h1 : Tendsto (fun n => V (n + 1) z) atTop (𝓝 (Jstar M z)) :=
    (hconv z hz).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => V (n + 1) z) atTop (𝓝 (beliefBellman M (Jstar M) z)) := by
    have e : (fun n => V (n + 1) z) = fun n => ⨅ u : U, (beliefCost M z u + M.β *
        ∑ y : Y, obsProb M z u y * V n (filterUpdate M z u y)) := by
      funext n
      simp only [hVdef]
      rw [Function.iterate_succ_apply']
      rfl
    rw [e]
    unfold beliefBellman
    refine (inf_lip.tendsto _).comp (tendsto_pi_nhds.2 fun u => ?_)
    refine tendsto_const_nhds.add (Tendsto.const_mul _ (tendsto_finsetSum _ fun y _ => ?_))
    exact (hconv _ (hFU z u y)).const_mul _
  exact tendsto_nhds_unique h1 h2

end JS


theorem eq33_fin {X Y U : Type*} [MeasurableSpace X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [Fintype U] [Nonempty U] [MeasurableSpace U]
    (M : POMDP X Y U)
    {N : ℕ} (π : Measure X) [IsFiniteMeasure π] (I : Window Y U N) :
    JstarW M π I = ⨅ u : U, (chat M π I u +
      M.β * ∑ y : Y, predY M π I u y * JstarW M (nextPrior M π I u) (shift I u y)) := by
  unfold JstarW
  rw [jstar_fix M (post M π I) (normalize_univ_le _)]
  unfold beliefBellman
  refine iInf_congr fun u => ?_
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  show obsProb M (post M π I) u y * Jstar M (filterUpdate M (post M π I) u y) =
    obsProb M (post M π I) u y * Jstar M (post M (nextPrior M π I u) (shift I u y))
  by_cases hc : correct M π (I.1 0) Set.univ = 0
  · have hm : unnormPost M N π I = 0 :=
      Measure.measure_univ_eq_zero.1 (le_antisymm ((unnormPost_univ_le_correct M N π I).trans
        hc.le) zero_le)
    have hp : post M π I = 0 := by
      unfold post FiniteMemQL.Convergence.normalize; rw [hm, smul_zero]
    have h0 : obsProb M (post M π I) u y = 0 := by
      unfold obsProb
      rw [le_antisymm ((correct_univ_le M _ y).trans (by rw [predict_univ, hp]; simp)) zero_le]
      rfl
    rw [h0, zero_mul, zero_mul]
  · rw [post_nextPrior M π I u y hc]

end FMQC


open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace FMQC

open FiniteMemQL.Convergence
open scoped ENNReal

variable {X Y U : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]

/-- Forward (unnormalised) filtering along sequences, from time `s`, for `n` more steps. -/
noncomputable def Fwd (M : POMDP X Y U) (π : Measure X) (Ys : ℕ → Y) (Us : ℕ → U) (s : ℕ) :
    ℕ → Measure X
  | 0 => correct M π (Ys s)
  | n + 1 => correct M (predict M (Fwd M π Ys Us s n) (Us (s + n))) (Ys (s + n + 1))

/-- Unnormalised predictor. -/
noncomputable def Pu (M : POMDP X Y U) (π : Measure X) (Ys : ℕ → Y) (Us : ℕ → U) :
    ℕ → Measure X
  | 0 => π
  | t + 1 => predict M (correct M (Pu M π Ys Us t) (Ys t)) (Us t)

lemma Fwd_front (M : POMDP X Y U) (Ys : ℕ → Y) (Us : ℕ → U) (n : ℕ) :
    ∀ (π : Measure X) (s : ℕ), Fwd M π Ys Us s (n + 1) =
      Fwd M (predict M (correct M π (Ys s)) (Us s)) Ys Us (s + 1) n := by
  induction n with
  | zero => intro π s; simp [Fwd]
  | succ n ih =>
    intro π s
    rw [Fwd, ih]
    simp only [Fwd]
    rw [show s + (n + 1) = s + 1 + n by omega]

lemma unnormPost_seq (M : POMDP X Y U) (Ys : ℕ → Y) (Us : ℕ → U) (n : ℕ) :
    ∀ (π : Measure X) (s : ℕ),
      unnormPost M n π ((fun j : Fin (n + 1) => Ys (s + j)), (fun j : Fin n => Us (s + j))) =
        Fwd M π Ys Us s n := by
  induction n with
  | zero => intro π s; simp [unnormPost, Fwd]
  | succ n ih =>
    intro π s
    simp only [unnormPost]
    have h1 : Fin.tail (fun j : Fin (n + 2) => Ys (s + j)) =
        fun j : Fin (n + 1) => Ys (s + 1 + j) := by
      funext j; simp [Fin.tail]; ring_nf
    have h2 : Fin.tail (fun j : Fin (n + 1) => Us (s + j)) =
        fun j : Fin n => Us (s + 1 + j) := by
      funext j; simp [Fin.tail]; ring_nf
    rw [h1, h2, ih, Fwd_front]
    simp

lemma unnormPost_seq0 (M : POMDP X Y U) (Ys : ℕ → Y) (Us : ℕ → U) (n : ℕ) (π : Measure X) :
    unnormPost M n π ((fun j : Fin (n + 1) => Ys j), (fun j : Fin n => Us j)) =
      Fwd M π Ys Us 0 n := by
  have := unnormPost_seq M Ys Us n π 0
  simpa using this

lemma Fwd_zero_eq (M : POMDP X Y U) (π : Measure X) (Ys : ℕ → Y) (Us : ℕ → U) (t : ℕ) :
    Fwd M π Ys Us 0 t = correct M (Pu M π Ys Us t) (Ys t) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [Fwd, Pu, ih, zero_add]

lemma Fwd_split (M : POMDP X Y U) (π : Measure X) (Ys : ℕ → Y) (Us : ℕ → U) (t n : ℕ) :
    Fwd M π Ys Us 0 (t + n) = Fwd M (Pu M π Ys Us t) Ys Us t n := by
  induction n with
  | zero => rw [add_zero, Fwd_zero_eq]; rfl
  | succ n ih =>
    rw [← add_assoc]
    simp only [Fwd]
    rw [ih, zero_add]

lemma Fwd_smul (M : POMDP X Y U) (Ys : ℕ → Y) (Us : ℕ → U) (s n : ℕ) (c : ℝ≥0∞)
    (π : Measure X) : Fwd M (c • π) Ys Us s n = c • Fwd M π Ys Us s n := by
  rw [← unnormPost_seq, ← unnormPost_seq, unnormPost_smul]

lemma Fwd_congr (M : POMDP X Y U) (π : Measure X) (Ys Ys' : ℕ → Y) (Us Us' : ℕ → U) (s : ℕ) :
    ∀ n : ℕ, (∀ k, s ≤ k → k ≤ s + n → Ys k = Ys' k) → (∀ k, s ≤ k → k < s + n → Us k = Us' k) →
      Fwd M π Ys Us s n = Fwd M π Ys' Us' s n := by
  intro n
  induction n with
  | zero => intro hY _; simp only [Fwd]; rw [hY s le_rfl (by omega)]
  | succ n ih =>
    intro hY hU
    simp only [Fwd]
    rw [ih (fun k h1 h2 => hY k h1 (by omega)) (fun k h1 h2 => hU k h1 (by omega)),
      hU (s + n) (by omega) (by omega), hY (s + n + 1) (by omega) (by omega)]

lemma fp_congr (M : POMDP X Y U) (π : Measure X) (Ys Ys' : ℕ → Y) (Us Us' : ℕ → U) :
    ∀ t : ℕ, (∀ k, k < t → Ys k = Ys' k) → (∀ k, k < t → Us k = Us' k) →
      filterPred M π Ys Us t = filterPred M π Ys' Us' t := by
  intro t
  induction t with
  | zero => intro _ _; rfl
  | succ t ih =>
    intro hY hU
    simp only [filterPred]
    rw [ih (fun k h => hY k (by omega)) (fun k h => hU k (by omega)), hY t (by omega),
      hU t (by omega)]

variable [Fintype Y] [MeasurableSingletonClass Y]

lemma fp_fin (M : POMDP X Y U) (π : Measure X) [IsFiniteMeasure π] (Ys : ℕ → Y) (Us : ℕ → U) :
    ∀ t, filterPred M π Ys Us t Set.univ ≠ ⊤ := by
  intro t
  cases t with
  | zero => exact measure_ne_top π _
  | succ t =>
    simp only [filterPred]
    rw [predict_univ]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (normalize_univ_le _)

lemma Pu_smul (M : POMDP X Y U) (π : Measure X) [IsFiniteMeasure π] (Ys : ℕ → Y)
    (Us : ℕ → U) : ∀ t, ∃ κ : ℝ≥0∞, κ ≠ ⊤ ∧ Pu M π Ys Us t = κ • filterPred M π Ys Us t := by
  intro t
  induction t with
  | zero => exact ⟨1, ENNReal.one_ne_top, by simp [Pu, filterPred]⟩
  | succ t ih =>
    obtain ⟨κ, hκ, he⟩ := ih
    set fp := filterPred M π Ys Us t
    have hfin : correct M fp (Ys t) Set.univ ≠ ⊤ :=
      ne_top_of_le_ne_top (fp_fin M π Ys Us t) (correct_univ_le M fp _)
    refine ⟨κ * correct M fp (Ys t) Set.univ, ENNReal.mul_ne_top hκ hfin, ?_⟩
    simp only [Pu, filterPred]
    rw [he, correct_smul, predict_smul]
    conv_lhs => rw [eq_smul_normalize (correct M fp (Ys t)) hfin]
    rw [predict_smul, smul_smul]

lemma Fwd_univ_le (M : POMDP X Y U) (π : Measure X) (Ys : ℕ → Y) (Us : ℕ → U) (s n : ℕ) :
    Fwd M π Ys Us s n Set.univ ≤ π Set.univ := by
  rw [← unnormPost_seq]; exact unnormPost_univ_le M n π _

/-- Filter consistency: the full-history posterior equals the window posterior under the
normalised predictor. -/
lemma filter_consistency (M : POMDP X Y U) (π : Measure X) [IsFiniteMeasure π] (Ys : ℕ → Y)
    (Us : ℕ → U) (t N : ℕ) (h : Fwd M π Ys Us 0 (t + N) Set.univ ≠ 0) :
    FiniteMemQL.Convergence.normalize (Fwd M π Ys Us 0 (t + N)) =
      FiniteMemQL.Convergence.normalize (Fwd M (filterPred M π Ys Us t) Ys Us t N) := by
  obtain ⟨κ, hκ, he⟩ := Pu_smul M π Ys Us t
  rw [Fwd_split, he, Fwd_smul] at h ⊢
  have hκ0 : κ ≠ 0 := by
    rintro rfl; simp at h
  have hfin : Fwd M (filterPred M π Ys Us t) Ys Us t N Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top (fp_fin M π Ys Us t) (Fwd_univ_le M _ Ys Us t N)
  exact normalize_smul _ _ hκ0 hκ hfin

lemma mass_split (M : POMDP X Y U) (m : Measure X) (hm : m Set.univ ≠ ⊤) (a : U) (y : Y) :
    (correct M (predict M m a) y Set.univ).toReal =
      (m Set.univ).toReal * obsProb M (FiniteMemQL.Convergence.normalize m) a y := by
  conv_lhs => rw [eq_smul_normalize m hm]
  rw [predict_smul, correct_smul, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rfl

end FMQC


open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace FMQC

open FiniteMemQL.Convergence
open scoped ENNReal

variable {X Y U : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]

/-- The action sequence produced by a history policy along a (finite) observation history. -/
def Useq (γ : HistPolicy Y U) {n : ℕ} (ys : Fin (n + 1) → Y) : ℕ → U :=
  fun k => γ k (fun j => extSeq ys j)

lemma extSeq_lt {n : ℕ} (ys : Fin (n + 1) → Y) (k : ℕ) (hk : k < n + 1) :
    extSeq ys k = ys ⟨k, hk⟩ := by simp [extSeq, hk]

lemma hist_congr (γ : HistPolicy Y U) {k k' : ℕ} (hk : k = k') (f : Fin (k + 1) → Y)
    (f' : Fin (k' + 1) → Y)
    (h : ∀ i : ℕ, ∀ (hi : i < k + 1) (hi' : i < k' + 1), f ⟨i, hi⟩ = f' ⟨i, hi'⟩) :
    γ k f = γ k' f' := by
  subst hk; congr 1; funext i; exact h i i.2 i.2

lemma histActs_eq (γ : HistPolicy Y U) {n : ℕ} (ys : Fin (n + 1) → Y) :
    histActs γ ys = fun j : Fin n => Useq γ ys j := by
  funext j
  unfold histActs Useq
  apply hist_congr γ rfl
  intro i hi hi'
  rw [extSeq_lt ys i (by omega)]

lemma histMass_eq (M : POMDP X Y U) (π : Measure X) (γ : HistPolicy Y U) {n : ℕ}
    (ys : Fin (n + 1) → Y) :
    histMass M π γ ys = (Fwd M π (extSeq ys) (Useq γ ys) 0 n Set.univ).toReal := by
  unfold histMass
  rw [histActs_eq, ← unnormPost_seq0]
  congr 4
  funext j
  rw [extSeq_lt ys j j.2]

lemma windowAt_eq (γ : HistPolicy Y U) {t N : ℕ} (ys : Fin (t + N + 1) → Y) :
    windowAt γ t ys = ((fun j : Fin (N + 1) => extSeq ys (t + j)),
      (fun j : Fin N => Useq γ ys (t + j))) := by
  unfold windowAt
  rw [histActs_eq]
  congr 1
  funext j
  rw [extSeq_lt ys (t + j) (by omega)]

/-- Splitting a history into its prefix and its last observation. -/
def snocEqv (n : ℕ) {m : ℕ} (h : m = n + 1) : (Fin (m + 1) → Y) ≃ (Fin (n + 1) → Y) × Y where
  toFun ys' := (fun j => ys' ⟨j, by omega⟩, ys' ⟨n + 1, by omega⟩)
  invFun p := fun i => if hi : i.val < n + 1 then p.1 ⟨i, hi⟩ else p.2
  left_inv ys' := by
    funext i
    by_cases hi : i.val < n + 1
    · simp [hi]
    · simp only [hi, dite_false]
      congr 1; ext; simp; omega
  right_inv p := by
    ext j
    · simp [j.isLt]
    · simp

lemma ext_snoc (n : ℕ) {m : ℕ} (h : m = n + 1) (ys : Fin (n + 1) → Y) (y : Y) (k : ℕ)
    (hk : k ≤ n) : extSeq ((snocEqv n h).symm (ys, y)) k = extSeq ys k := by
  rw [extSeq_lt _ k (by omega), extSeq_lt _ k (by omega)]
  simp [snocEqv, hk]

lemma ext_snoc_last (n : ℕ) {m : ℕ} (h : m = n + 1) (ys : Fin (n + 1) → Y) (y : Y) :
    extSeq ((snocEqv n h).symm (ys, y)) (n + 1) = y := by
  rw [extSeq_lt _ (n + 1) (by omega)]
  simp [snocEqv]

lemma Useq_snoc (γ : HistPolicy Y U) (n : ℕ) {m : ℕ} (h : m = n + 1) (ys : Fin (n + 1) → Y)
    (y : Y) (k : ℕ) (hk : k ≤ n) : Useq γ ((snocEqv n h).symm (ys, y)) k = Useq γ ys k := by
  unfold Useq
  apply hist_congr γ rfl
  intro i hi _
  exact ext_snoc n h ys y i (by omega)

lemma Useq_last (γ : HistPolicy Y U) (n : ℕ) (ys : Fin (n + 1) → Y) :
    Useq γ ys n = γ n ys := by
  unfold Useq
  apply hist_congr γ rfl
  intro i hi _
  rw [extSeq_lt ys i hi]

variable [Fintype Y] [MeasurableSingletonClass Y]

section chain

variable (M : POMDP X Y U) (π₀ : Measure X) [IsFiniteMeasure π₀] (γ : HistPolicy Y U) (t N : ℕ)

lemma chain_predictor (ys : Fin (t + N + 1) → Y) (y : Y) :
    predictor M π₀ γ (t + 1) ((snocEqv (t + N) (m := t + 1 + N) (by omega)).symm (ys, y)) =
      nextPrior M (predictor M π₀ γ t ys) (windowAt γ t ys) (γ (t + N) ys) := by
  set e := snocEqv (Y := Y) (t + N) (m := t + 1 + N) (by omega)
  show filterPred M π₀ (extSeq (e.symm (ys, y))) (Useq γ (e.symm (ys, y))) (t + 1) =
    nextPrior M (filterPred M π₀ (extSeq ys) (Useq γ ys) t) (windowAt γ t ys) (γ (t + N) ys)
  simp only [filterPred]
  rw [fp_congr M π₀ (extSeq (e.symm (ys, y))) (extSeq ys) (Useq γ (e.symm (ys, y)))
    (Useq γ ys) t (fun k hk => ext_snoc _ _ ys y k (by omega))
    (fun k hk => Useq_snoc γ _ _ ys y k (by omega))]
  unfold nextPrior
  rw [windowAt_eq]
  have h1 : extSeq (e.symm (ys, y)) t = extSeq ys (t + ((0 : Fin (N + 1)) : ℕ)) := by
    rw [ext_snoc _ _ ys y t (by omega)]; simp
  have h2 : Useq γ (e.symm (ys, y)) t =
      Fin.snoc (α := fun _ => U) (fun j : Fin N => Useq γ ys (t + j)) (γ (t + N) ys) 0 := by
    rw [Useq_snoc γ _ _ ys y t (by omega)]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      rw [Fin.snoc_zero]
      exact Useq_last γ (t + 0) ys
    · haveI : NeZero N := ⟨by omega⟩
      rw [Fin.snoc_apply_zero]
      simp
  rw [h2, h1]

lemma chain_window (ys : Fin (t + N + 1) → Y) (y : Y) :
    windowAt γ (t + 1) ((snocEqv (t + N) (m := t + 1 + N) (by omega)).symm (ys, y)) =
      shift (windowAt γ t ys) (γ (t + N) ys) y := by
  set e := snocEqv (Y := Y) (t + N) (m := t + 1 + N) (by omega)
  rw [windowAt_eq, windowAt_eq]
  unfold shift
  ext j
  · simp only [Fin.tail, Fin.snoc]
    by_cases hj : (j : ℕ) + 1 < N + 1
    · simp only [Fin.val_succ, hj, dite_true, cast_eq, Fin.castLT]
      rw [ext_snoc _ _ ys y _ (by omega)]
      congr 1; omega
    · simp only [Fin.val_succ, hj, dite_false, cast_eq]
      have : t + 1 + (j : ℕ) = t + N + 1 := by omega
      rw [this, ext_snoc_last]
  · simp only [Fin.tail, Fin.snoc]
    by_cases hj : (j : ℕ) + 1 < N
    · simp only [Fin.val_succ, hj, dite_true, cast_eq, Fin.castLT]
      rw [Useq_snoc γ _ _ ys y _ (by omega)]
      congr 1; omega
    · simp only [Fin.val_succ, hj, dite_false, cast_eq]
      have : t + 1 + (j : ℕ) = t + N := by omega
      rw [this, Useq_snoc γ _ _ ys y _ le_rfl, Useq_last]

lemma chain_mass (ys : Fin (t + N + 1) → Y) (y : Y) :
    histMass M π₀ γ ((snocEqv (t + N) (m := t + 1 + N) (by omega)).symm (ys, y)) =
      histMass M π₀ γ ys *
        predY M (predictor M π₀ γ t ys) (windowAt γ t ys) (γ (t + N) ys) y := by
  set e := snocEqv (Y := Y) (t + N) (m := t + 1 + N) (by omega)
  rw [histMass_eq, histMass_eq]
  rw [congrArg (Fwd M π₀ (extSeq (e.symm (ys, y))) (Useq γ (e.symm (ys, y))) 0)
    (show t + 1 + N = t + N + 1 by omega)]
  simp only [Fwd]
  rw [Fwd_congr M π₀ (extSeq (e.symm (ys, y))) (extSeq ys) (Useq γ (e.symm (ys, y)))
    (Useq γ ys) 0 (t + N) (fun k _ hk => ext_snoc _ _ ys y k (by omega))
    (fun k _ hk => Useq_snoc γ _ _ ys y k (by omega))]
  rw [zero_add, Useq_snoc γ _ _ ys y _ le_rfl, Useq_last, ext_snoc_last]
  set m := Fwd M π₀ (extSeq ys) (Useq γ ys) 0 (t + N) with hm
  have hmfin : m Set.univ ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top π₀ _) (Fwd_univ_le M _ _ _ _ _)
  rw [mass_split M m hmfin]
  rcases eq_or_ne (m Set.univ) 0 with h0 | h0
  · rw [h0]; simp
  · congr 1
    unfold predY post
    rw [windowAt_eq, unnormPost_seq, hm, filter_consistency M π₀ _ _ t N h0]
    rfl

/-- The chain rule for expectations over histories. -/
lemma chain (F : Measure X × Window Y U N → ℝ) :
    ∑ ys' : Fin (t + 1 + N + 1) → Y, histMass M π₀ γ ys' *
        F (predictor M π₀ γ (t + 1) ys', windowAt γ (t + 1) ys') =
      ∑ ys : Fin (t + N + 1) → Y, histMass M π₀ γ ys * ∑ y : Y,
        predY M (predictor M π₀ γ t ys) (windowAt γ t ys) (Useq γ ys (t + N)) y *
          F (nextPrior M (predictor M π₀ γ t ys) (windowAt γ t ys) (Useq γ ys (t + N)),
            shift (windowAt γ t ys) (Useq γ ys (t + N)) y) := by
  set e := snocEqv (Y := Y) (t + N) (m := t + 1 + N) (by omega)
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ys _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [chain_mass, chain_predictor, chain_window, Useq_last]
  ring

end chain

end FMQC


open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace FMQC

open FiniteMemQL.Convergence
open scoped ENNReal

section TV

variable {X : Type*} [MeasurableSpace X]

lemma tv_bdd (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    BddAbove {r | ∃ A : Set X, MeasurableSet A ∧ r = |(μ A).toReal - (ν A).toReal|} := by
  refine ⟨(μ Set.univ).toReal + (ν Set.univ).toReal, ?_⟩
  rintro r ⟨A, hA, rfl⟩
  have h1 : (μ A).toReal ≤ (μ Set.univ).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
  have h2 : (ν A).toReal ≤ (ν Set.univ).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
  have h3 : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have h4 : 0 ≤ (ν A).toReal := ENNReal.toReal_nonneg
  rw [abs_le]; constructor <;> linarith

lemma le_tv (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (A : Set X)
    (hA : MeasurableSet A) :
    |(μ A).toReal - (ν A).toReal| ≤ MarkovChainCLT.tvDist μ ν :=
  le_csSup (tv_bdd μ ν) ⟨A, hA, rfl⟩

lemma tv_nonneg (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 ≤ MarkovChainCLT.tvDist μ ν :=
  (abs_nonneg _).trans (le_tv μ ν ∅ MeasurableSet.empty)

lemma tv_le_one (μ ν : Measure X) (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1) :
    MarkovChainCLT.tvDist μ ν ≤ 1 := by
  refine csSup_le ⟨0, ∅, MeasurableSet.empty, by simp⟩ ?_
  rintro r ⟨A, hA, rfl⟩
  have h1 : (μ A).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top ((measure_mono (Set.subset_univ A)).trans hμ)
    simpa using this
  have h2 : (ν A).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top ((measure_mono (Set.subset_univ A)).trans hν)
    simpa using this
  have h3 : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have h4 : 0 ≤ (ν A).toReal := ENNReal.toReal_nonneg
  rw [abs_le]; constructor <;> linarith

lemma tv_symm (μ ν : Measure X) : MarkovChainCLT.tvDist μ ν = MarkovChainCLT.tvDist ν μ := by
  unfold MarkovChainCLT.tvDist
  congr 1
  ext r
  simp only [Set.mem_setOf_eq]
  constructor <;> rintro ⟨A, hA, rfl⟩ <;> exact ⟨A, hA, abs_sub_comm _ _⟩

/-- One-sided bound: for `0 ≤ G ≤ 1`, `∫ G dμ - ∫ G dν ≤ tvDist μ ν` (Hahn decomposition). -/
lemma lint_sub_le_tv (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (G : X → ℝ≥0∞) (hG1 : ∀ x, G x ≤ 1) :
    (∫⁻ x, G x ∂μ).toReal - (∫⁻ x, G x ∂ν).toReal ≤ MarkovChainCLT.tvDist μ ν := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition ν μ
  have hsm := hs.measurableSet
  have hle : ν.restrict s ≤ μ.restrict s := hs.le_on
  have hge : μ.restrict sᶜ ≤ ν.restrict sᶜ := hs.ge_on_compl
  have hfinG : ∀ (m : Measure X) [IsFiniteMeasure m], ∫⁻ x, G x ∂m ≠ ∞ := by
    intro m _
    refine ne_top_of_le_ne_top (measure_ne_top m Set.univ) ?_
    calc ∫⁻ x, G x ∂m ≤ ∫⁻ _, 1 ∂m := lintegral_mono hG1
      _ = m Set.univ := by rw [lintegral_one]
  have h1 : ∫⁻ x, G x ∂μ = ∫⁻ x in s, G x ∂μ + ∫⁻ x in sᶜ, G x ∂μ :=
    (lintegral_add_compl _ hsm).symm
  have h2 : ∫⁻ x in sᶜ, G x ∂μ ≤ ∫⁻ x in sᶜ, G x ∂ν := lintegral_mono' hge le_rfl
  have h3 : ∫⁻ x in s, G x ∂μ = ∫⁻ x, G x ∂(μ.restrict s - ν.restrict s)
      + ∫⁻ x in s, G x ∂ν := by
    rw [← lintegral_add_measure, Measure.sub_add_cancel_of_le hle]
  have h4 : ∫⁻ x, G x ∂(μ.restrict s - ν.restrict s) ≤ μ s - ν s := by
    calc ∫⁻ x, G x ∂(μ.restrict s - ν.restrict s) ≤ ∫⁻ _, 1 ∂(μ.restrict s - ν.restrict s) :=
          lintegral_mono hG1
      _ = (μ.restrict s - ν.restrict s) Set.univ := lintegral_one
      _ = μ s - ν s := by
          rw [Measure.sub_apply MeasurableSet.univ hle, Measure.restrict_apply_univ,
            Measure.restrict_apply_univ]
  have h5 : ∫⁻ x, G x ∂ν = ∫⁻ x in s, G x ∂ν + ∫⁻ x in sᶜ, G x ∂ν :=
    (lintegral_add_compl _ hsm).symm
  have key : ∫⁻ x, G x ∂μ ≤ (μ s - ν s) + ∫⁻ x, G x ∂ν := by
    rw [h1, h3, h5]
    calc ∫⁻ x, G x ∂(μ.restrict s - ν.restrict s) + ∫⁻ x in s, G x ∂ν + ∫⁻ x in sᶜ, G x ∂μ
        ≤ (μ s - ν s) + ∫⁻ x in s, G x ∂ν + ∫⁻ x in sᶜ, G x ∂ν := by gcongr
      _ = (μ s - ν s) + (∫⁻ x in s, G x ∂ν + ∫⁻ x in sᶜ, G x ∂ν) := by rw [add_assoc]
  have hνs : ν s ≤ μ s := by
    simpa [Measure.restrict_apply_univ] using (Measure.le_iff'.1 hle Set.univ)
  have hfin1 : μ s - ν s ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top μ s) tsub_le_self
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin1, hfinG ν⟩) key
  rw [ENNReal.toReal_add hfin1 (hfinG ν), ENNReal.toReal_sub_of_le hνs (measure_ne_top μ s)]
    at hreal
  have := le_tv μ ν s hsm
  have := le_abs_self ((μ s).toReal - (ν s).toReal)
  linarith

/-- Integrals of a bounded function against two finite measures differ by at most
`2 B tvDist`. -/
lemma int_diff_tv (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (f : X → ℝ)
    (hf : Measurable f) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x, |f x| ≤ B) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ 2 * B * MarkovChainCLT.tvDist μ ν := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition ν μ
  have hsm := hs.measurableSet
  have hle : ν.restrict s ≤ μ.restrict s := hs.le_on
  have hge : μ.restrict sᶜ ≤ ν.restrict sᶜ := hs.ge_on_compl
  have hint : ∀ (m : Measure X) [IsFiniteMeasure m], Integrable f m := fun m _ =>
    Integrable.of_bound hf.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  set d1 := μ.restrict s - ν.restrict s
  set d2 := ν.restrict sᶜ - μ.restrict sᶜ
  have e1 : ∫ x in s, f x ∂μ = ∫ x, f x ∂d1 + ∫ x in s, f x ∂ν := by
    rw [← integral_add_measure (hint _) (hint _), Measure.sub_add_cancel_of_le hle]
  have e2 : ∫ x in sᶜ, f x ∂ν = ∫ x, f x ∂d2 + ∫ x in sᶜ, f x ∂μ := by
    rw [← integral_add_measure (hint _) (hint _), Measure.sub_add_cancel_of_le hge]
  have eμ := (integral_add_compl hsm (hint μ)).symm
  have eν := (integral_add_compl hsm (hint ν)).symm
  have hd1 : |∫ x, f x ∂d1| ≤ B * MarkovChainCLT.tvDist μ ν := by
    have h := norm_integral_le_of_norm_le_const (μ := d1) (f := f) (C := B)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
    rw [Real.norm_eq_abs] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hB0)
    have hνs : ν s ≤ μ s := by
      simpa [Measure.restrict_apply_univ] using (Measure.le_iff'.1 hle Set.univ)
    have : d1.real Set.univ = (μ s).toReal - (ν s).toReal := by
      unfold Measure.real
      rw [Measure.sub_apply MeasurableSet.univ hle, Measure.restrict_apply_univ,
        Measure.restrict_apply_univ, ENNReal.toReal_sub_of_le hνs (measure_ne_top μ s)]
    rw [this]
    exact (le_abs_self _).trans (le_tv μ ν s hsm)
  have hd2 : |∫ x, f x ∂d2| ≤ B * MarkovChainCLT.tvDist μ ν := by
    have h := norm_integral_le_of_norm_le_const (μ := d2) (f := f) (C := B)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
    rw [Real.norm_eq_abs] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hB0)
    have hμs : μ sᶜ ≤ ν sᶜ := by
      simpa [Measure.restrict_apply_univ] using (Measure.le_iff'.1 hge Set.univ)
    have : d2.real Set.univ = (ν sᶜ).toReal - (μ sᶜ).toReal := by
      unfold Measure.real
      rw [Measure.sub_apply MeasurableSet.univ hge, Measure.restrict_apply_univ,
        Measure.restrict_apply_univ, ENNReal.toReal_sub_of_le hμs (measure_ne_top ν _)]
    rw [this]
    exact (le_abs_self _).trans (by rw [abs_sub_comm]; exact le_tv μ ν sᶜ hsm.compl)
  have : ∫ x, f x ∂μ - ∫ x, f x ∂ν = ∫ x, f x ∂d1 - ∫ x, f x ∂d2 := by
    rw [eμ, eν, e1, e2]; ring
  rw [this]
  calc |∫ x, f x ∂d1 - ∫ x, f x ∂d2| ≤ |∫ x, f x ∂d1| + |∫ x, f x ∂d2| := abs_sub _ _
    _ ≤ B * MarkovChainCLT.tvDist μ ν + B * MarkovChainCLT.tvDist μ ν := add_le_add hd1 hd2
    _ = 2 * B * MarkovChainCLT.tvDist μ ν := by ring

lemma sum_abs_le_tv {Y : Type*} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (P Q : Measure Y) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    ∑ y : Y, |(P {y}).toReal - (Q {y}).toReal| ≤ 2 * MarkovChainCLT.tvDist P Q := by
  classical
  set A := Finset.univ.filter (fun y => (Q {y}).toReal ≤ (P {y}).toReal)
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun y => (Q {y}).toReal ≤ (P {y}).toReal) (fun y => |(P {y}).toReal - (Q {y}).toReal|)
  have hmeas : ∀ (R : Measure Y) [IsFiniteMeasure R] (s : Finset Y),
      ∑ y ∈ s, (R {y}).toReal = (R (s : Set Y)).toReal := by
    intro R _ s
    rw [← ENNReal.toReal_sum (fun y _ => measure_ne_top R _), sum_measure_singleton]
  have h1 : ∑ y ∈ A, |(P {y}).toReal - (Q {y}).toReal| =
      (P (A : Set Y)).toReal - (Q (A : Set Y)).toReal := by
    rw [← hmeas P A, ← hmeas Q A, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [abs_of_nonneg (by linarith)]
  set Ac := Finset.univ.filter (fun y => ¬ (Q {y}).toReal ≤ (P {y}).toReal)
  have h2 : ∑ y ∈ Ac, |(P {y}).toReal - (Q {y}).toReal| =
      (Q (Ac : Set Y)).toReal - (P (Ac : Set Y)).toReal := by
    rw [← hmeas P Ac, ← hmeas Q Ac, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [Ac, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [← hsplit, h1, h2]
  have := le_tv P Q (A : Set Y) (Finset.measurableSet _)
  have := le_tv P Q (Ac : Set Y) (Finset.measurableSet _)
  have := le_abs_self ((P (A : Set Y)).toReal - (Q (A : Set Y)).toReal)
  have := neg_abs_le ((P (Ac : Set Y)).toReal - (Q (Ac : Set Y)).toReal)
  linarith

end TV

end FMQC


open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace FMQC

open FiniteMemQL.Convergence
open scoped ENNReal

/-- Value iteration for an operator of the form `min_u (a + β Σ w V ∘ g)` converges on an
invariant set, to a bounded fixed point. -/
lemma vi_conv {Z A Y : Type*} [Fintype A] [Nonempty A] [Fintype Y] (S : Set Z)
    (a : Z → A → ℝ) (w : Z → A → Y → ℝ) (g : Z → A → Y → Z) (β B : ℝ) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hB0 : 0 ≤ B)
    (hB : ∀ z ∈ S, ∀ u, |a z u| ≤ B) (hw0 : ∀ z u y, 0 ≤ w z u y)
    (hw1 : ∀ z ∈ S, ∀ u, ∑ y, w z u y ≤ 1)
    (hg : ∀ z ∈ S, ∀ u y, g z u y ∈ S) (T : (Z → ℝ) → Z → ℝ)
    (hT : ∀ V z, T V z = ⨅ u, (a z u + β * ∑ y, w z u y * V (g z u y))) :
    ∀ z ∈ S, Tendsto (fun n => T^[n] 0 z) atTop (𝓝 (limUnder atTop (fun n => T^[n] 0 z))) ∧
      limUnder atTop (fun n => T^[n] 0 z) =
        T (fun z' => limUnder atTop (fun n => T^[n] 0 z')) z ∧
      |limUnder atTop (fun n => T^[n] 0 z)| ≤ B / (1 - β) := by
  set V : ℕ → Z → ℝ := fun n => T^[n] 0 with hV
  set L : Z → ℝ := fun z => limUnder atTop (fun n => V n z) with hL
  have h1β : 0 < 1 - β := by linarith
  have hlip : ∀ (P Q : Z → ℝ) (d : ℝ), 0 ≤ d → (∀ z ∈ S, |P z - Q z| ≤ d) →
      ∀ z ∈ S, |T P z - T Q z| ≤ β * d := by
    intro P Q d hd h z hz
    rw [hT, hT]
    apply inf_diff
    intro u
    rw [add_sub_add_left_eq_sub, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hβ0]
    apply mul_le_mul_of_nonneg_left _ hβ0
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ y, |w z u y * P (g z u y) - w z u y * Q (g z u y)| ≤ ∑ y, w z u y * d := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [← mul_sub, abs_mul, abs_of_nonneg (hw0 z u y)]
          exact mul_le_mul_of_nonneg_left (h _ (hg z hz u y)) (hw0 z u y)
      _ = (∑ y, w z u y) * d := by rw [Finset.sum_mul]
      _ ≤ 1 * d := mul_le_mul_of_nonneg_right (hw1 z hz u) hd
      _ = d := one_mul _
  have hT0 : ∀ z ∈ S, |T 0 z| ≤ B := by
    intro z hz
    rw [hT]
    have e : (⨅ u, (a z u + β * ∑ y, w z u y * (0 : Z → ℝ) (g z u y))) =
        (⨅ u, (a z u + β * ∑ y, w z u y * (0 : Z → ℝ) (g z u y))) - ⨅ _ : A, (0 : ℝ) := by
      simp
    rw [e]
    apply inf_diff
    intro u
    simpa using hB z hz u
  have e : ∀ m, V (m + 1) = T (V m) := fun m => Function.iterate_succ_apply' _ _ _
  have hstep : ∀ n, ∀ z ∈ S, |V (n + 1) z - V n z| ≤ B * β ^ n := by
    intro n
    induction n with
    | zero =>
      intro z hz
      rw [e 0]
      simpa [hV] using hT0 z hz
    | succ n ih =>
      intro z hz
      have := hlip (V (n + 1)) (V n) (B * β ^ n) (by positivity) ih z hz
      rw [← e (n + 1), ← e n] at this
      calc |V (n + 1 + 1) z - V (n + 1) z| ≤ β * (B * β ^ n) := this
        _ = B * β ^ (n + 1) := by ring
  have hbd : ∀ n, ∀ z ∈ S, |V n z| ≤ B / (1 - β) := by
    intro n
    induction n with
    | zero => intro z _; simp [hV]; positivity
    | succ n ih =>
      intro z hz
      rw [e n]
      have h1 := hlip (V n) 0 (B / (1 - β)) (by positivity) (fun z hz => by simpa using ih z hz)
        z hz
      have h2 := hT0 z hz
      have h3 : β * (B / (1 - β)) + B = B / (1 - β) := by field_simp; ring
      calc |T (V n) z| ≤ |T (V n) z - T 0 z| + |T 0 z| := by
            have := abs_sub_abs_le_abs_sub (T (V n) z) (T 0 z); linarith
        _ ≤ β * (B / (1 - β)) + B := add_le_add h1 h2
        _ = B / (1 - β) := h3
  have hconv : ∀ z ∈ S, Tendsto (fun n => V n z) atTop (𝓝 (L z)) := by
    intro z hz
    have hc : CauchySeq (fun n => V n z) := by
      refine cauchySeq_of_le_geometric β B hβ1 fun n => ?_
      rw [Real.dist_eq, abs_sub_comm]
      exact hstep n z hz
    obtain ⟨L', hL'⟩ := cauchySeq_tendsto_of_complete hc
    have : L z = L' := hL'.limUnder_eq
    rw [this]; exact hL'
  intro z hz
  refine ⟨hconv z hz, ?_, ?_⟩
  · have h1 : Tendsto (fun n => V (n + 1) z) atTop (𝓝 (L z)) :=
      (hconv z hz).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => V (n + 1) z) atTop (𝓝 (T L z)) := by
      have ee : (fun n => V (n + 1) z) = fun n => ⨅ u, (a z u + β *
          ∑ y, w z u y * V n (g z u y)) := by
        funext n; rw [e n, hT]
      rw [ee, hT]
      refine (inf_lip.tendsto _).comp (tendsto_pi_nhds.2 fun u => ?_)
      refine tendsto_const_nhds.add (Tendsto.const_mul _ (tendsto_finsetSum _ fun y _ => ?_))
      exact (hconv _ (hg z hz u y)).const_mul _
    exact tendsto_nhds_unique h1 h2
  · exact le_of_tendsto ((continuous_abs.tendsto _).comp (hconv z hz))
      (Filter.Eventually.of_forall fun n => hbd n z hz)

variable {X Y U : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]

lemma c_le_cNorm (M : POMDP X Y U) (x : X) (u : U) : |M.c x u| ≤ cNorm M := by
  obtain ⟨B, hB⟩ := M.c_bdd
  exact le_ciSup (f := fun p : X × U => |M.c p.1 p.2|) ⟨B, by rintro _ ⟨p, rfl⟩; exact hB _ _⟩
    (x, u)

lemma cNorm_nonneg (M : POMDP X Y U) : 0 ≤ cNorm M :=
  Real.iSup_nonneg fun _ => abs_nonneg _

lemma post_le (M : POMDP X Y U) {N : ℕ} (π : Measure X) (I : Window Y U N) :
    post M π I Set.univ ≤ 1 := normalize_univ_le _

instance post_fin (M : POMDP X Y U) {N : ℕ} (π : Measure X) (I : Window Y U N) :
    IsFiniteMeasure (post M π I) := ⟨lt_of_le_of_lt (post_le M π I) ENNReal.one_lt_top⟩

variable [Fintype Y] [MeasurableSingletonClass Y]

lemma nextPrior_le (M : POMDP X Y U) {N : ℕ} (π : Measure X) (I : Window Y U N) (u : U) :
    nextPrior M π I u Set.univ ≤ 1 := by
  unfold nextPrior; rw [predict_univ]; exact normalize_univ_le _

lemma chat_diff (M : POMDP X Y U) {N : ℕ} (π πs : Measure X) (I : Window Y U N) (u : U) :
    |chat M π I u - Cstar M πs I u| ≤
      2 * cNorm M * MarkovChainCLT.tvDist (post M π I) (post M πs I) := by
  unfold chat Cstar chat beliefCost
  exact int_diff_tv _ _ (fun x => M.c x u) (M.c_meas u) (cNorm M) (cNorm_nonneg M)
    (fun x => c_le_cNorm M x u)

lemma predY_eq (M : POMDP X Y U) {N : ℕ} (π : Measure X) (I : Window Y U N) (u : U) (y : Y) :
    predY M π I u y = (predYMeasure M π I u {y}).toReal := by
  unfold predY predYMeasure obsProb correct
  rw [Measure.bind_apply (measurableSet_singleton y) M.O.measurable.aemeasurable,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

lemma predYMeasure_univ (M : POMDP X Y U) {N : ℕ} (π : Measure X) (I : Window Y U N) (u : U) :
    predYMeasure M π I u Set.univ ≤ 1 := by
  unfold predYMeasure
  rw [Measure.bind_apply MeasurableSet.univ M.O.measurable.aemeasurable]
  simp only [measure_univ, lintegral_one]
  rw [predict_univ]; exact post_le M π I

instance predYMeasure_fin (M : POMDP X Y U) {N : ℕ} (π : Measure X) (I : Window Y U N) (u : U) :
    IsFiniteMeasure (predYMeasure M π I u) :=
  ⟨lt_of_le_of_lt (predYMeasure_univ M π I u) ENNReal.one_lt_top⟩

lemma B1_gen (M : POMDP X Y U) {N : ℕ} (π πs : Measure X) (I : Window Y U N) (u : U) :
    MarkovChainCLT.tvDist (predYMeasure M π I u) (predYMeasure M πs I u) ≤
      MarkovChainCLT.tvDist (post M π I) (post M πs I) := by
  have hTm : Measurable (fun x => M.T (x, u)) :=
    M.T.measurable.comp (measurable_id.prodMk measurable_const)
  have hrep : ∀ (p : Measure X) (A : Set Y), MeasurableSet A →
      predYMeasure M p I u A = ∫⁻ x, (∫⁻ x', M.O x' A ∂(M.T (x, u))) ∂(post M p I) := by
    intro p A hA
    unfold predYMeasure predict
    rw [Measure.bind_apply hA M.O.measurable.aemeasurable,
      Measure.lintegral_bind hTm.aemeasurable (M.O.measurable_coe hA).aemeasurable]
  have hG1 : ∀ A : Set Y, ∀ x, ∫⁻ x', M.O x' A ∂(M.T (x, u)) ≤ 1 := by
    intro A x
    calc ∫⁻ x', M.O x' A ∂(M.T (x, u)) ≤ ∫⁻ _, 1 ∂(M.T (x, u)) :=
          lintegral_mono fun x' => prob_le_one
      _ = 1 := by rw [lintegral_one, measure_univ]
  refine csSup_le ⟨0, ∅, MeasurableSet.empty, by simp⟩ ?_
  rintro r ⟨A, hA, rfl⟩
  rw [hrep π A hA, hrep πs A hA, abs_le]
  have a := lint_sub_le_tv (post M π I) (post M πs I) _ (hG1 A)
  have b := lint_sub_le_tv (post M πs I) (post M π I) _ (hG1 A)
  rw [tv_symm (post M πs I)] at b
  constructor <;> linarith

lemma predY_sum_diff [Nonempty Y] (M : POMDP X Y U) {N : ℕ} (π πs : Measure X) (I : Window Y U N) (u : U)
    (J : Y → ℝ) (R : ℝ) (hR : ∀ y, |J y| ≤ R) :
    |∑ y : Y, (predY M π I u y - Pstar M πs I u y) * J y| ≤
      R * (2 * MarkovChainCLT.tvDist (post M π I) (post M πs I)) := by
  have hR0 : 0 ≤ R := le_trans (abs_nonneg _) (hR (Classical.arbitrary Y))
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ y : Y, |(predY M π I u y - Pstar M πs I u y) * J y|
      ≤ ∑ y : Y, |predY M π I u y - Pstar M πs I u y| * R := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hR y) (abs_nonneg _)
    _ = R * ∑ y : Y, |(predYMeasure M π I u {y}).toReal - (predYMeasure M πs I u {y}).toReal| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        unfold Pstar
        rw [predY_eq, predY_eq, mul_comm]
    _ ≤ R * (2 * MarkovChainCLT.tvDist (post M π I) (post M πs I)) := by
        apply mul_le_mul_of_nonneg_left _ hR0
        exact (sum_abs_le_tv _ _).trans (by linarith [B1_gen M π πs I u])

end FMQC


open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace FMQC

open FiniteMemQL.Convergence
open scoped ENNReal


section Hist

variable {X Y U : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]
  [Fintype Y] [MeasurableSingletonClass Y]

lemma fp_le (M : POMDP X Y U) (π : Measure X) (hπ : π Set.univ ≤ 1) (Ys : ℕ → Y) (Us : ℕ → U) :
    ∀ t, filterPred M π Ys Us t Set.univ ≤ 1 := by
  intro t
  cases t with
  | zero => exact hπ
  | succ t =>
    simp only [filterPred]
    rw [predict_univ]
    exact normalize_univ_le _

lemma histMass_nonneg (M : POMDP X Y U) (π : Measure X) (γ : HistPolicy Y U) {n : ℕ}
    (ys : Fin (n + 1) → Y) : 0 ≤ histMass M π γ ys := ENNReal.toReal_nonneg

lemma sum_histMass (M : POMDP X Y U) (π : Measure X) [IsFiniteMeasure π] (γ : HistPolicy Y U) :
    ∀ n : ℕ, ∑ ys : Fin (n + 1) → Y, histMass M π γ ys = (π Set.univ).toReal := by
  intro n
  induction n with
  | zero =>
    have e : ∀ ys : Fin (0 + 1) → Y, histMass M π γ ys = (correct M π (ys 0) Set.univ).toReal := by
      intro ys; rw [histMass_eq]; simp only [Fwd]; rw [extSeq_lt ys 0 (by omega)]; rfl
    simp only [e]
    let e1 : (Fin (0 + 1) → Y) ≃ Y :=
      ⟨fun ys => ys 0, fun y _ => y, fun ys => by funext i; fin_cases i; rfl, fun y => rfl⟩
    calc ∑ ys : Fin (0 + 1) → Y, (correct M π (ys 0) Set.univ).toReal
        = ∑ ys : Fin (0 + 1) → Y, (fun y => (correct M π y Set.univ).toReal) (e1 ys) := rfl
      _ = ∑ y : Y, (correct M π y Set.univ).toReal :=
          e1.sum_comp (fun y => (correct M π y Set.univ).toReal)
      _ = (π Set.univ).toReal := by
          rw [← ENNReal.toReal_sum (fun y _ => ne_top_of_le_ne_top (measure_ne_top π _)
            (correct_univ_le M π y)), sum_correct]
  | succ n ih =>
    rw [← ih]
    set e := snocEqv (Y := Y) n (m := n + 1) rfl
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ys _ => ?_
    have hm : ∀ y, histMass M π γ (e.symm (ys, y)) = (correct M (predict M
        (Fwd M π (extSeq ys) (Useq γ ys) 0 n) (γ n ys)) y Set.univ).toReal := by
      intro y
      rw [histMass_eq]
      simp only [Fwd]
      rw [Fwd_congr M π (extSeq (e.symm (ys, y))) (extSeq ys) (Useq γ (e.symm (ys, y)))
        (Useq γ ys) 0 n (fun k _ hk => ext_snoc _ _ ys y k (by omega))
        (fun k _ hk => Useq_snoc γ _ _ ys y k (by omega))]
      rw [zero_add, Useq_snoc γ _ _ ys y _ le_rfl, Useq_last, ext_snoc_last]
    simp only [hm]
    set m := Fwd M π (extSeq ys) (Useq γ ys) 0 n
    have hmfin : m Set.univ ≠ ⊤ :=
      ne_top_of_le_ne_top (measure_ne_top π _) (Fwd_univ_le M _ _ _ _ _)
    rw [← ENNReal.toReal_sum (fun y _ => ne_top_of_le_ne_top hmfin
      ((correct_univ_le M _ y).trans (predict_univ M m _).le)), sum_correct, predict_univ,
      histMass_eq]

/-- Modify a history policy at time `n`. -/
noncomputable def modPol (γ : HistPolicy Y U) (n : ℕ) (s : (Fin (n + 1) → Y) → U) :
    HistPolicy Y U :=
  fun k h => if hk : k = n then s (hk ▸ h) else γ k h

lemma modPol_at (γ : HistPolicy Y U) (n : ℕ) (s : (Fin (n + 1) → Y) → U) (ys : Fin (n + 1) → Y) :
    modPol γ n s n ys = s ys := by
  simp [modPol]

lemma Useq_modPol_at (γ : HistPolicy Y U) (n : ℕ) (s : (Fin (n + 1) → Y) → U)
    (ys : Fin (n + 1) → Y) : Useq (modPol γ n s) ys n = s ys := by
  simp only [Useq, modPol, dite_true]
  congr 1
  funext j
  exact extSeq_lt ys j j.2

lemma Useq_modPol (γ : HistPolicy Y U) (n : ℕ) (s : (Fin (n + 1) → Y) → U) {m : ℕ}
    (ys : Fin (m + 1) → Y) (k : ℕ) (hk : k < n) : Useq (modPol γ n s) ys k = Useq γ ys k := by
  simp [Useq, modPol, show k ≠ n by omega]

variable (M : POMDP X Y U) (π₀ : Measure X) [IsFiniteMeasure π₀]

lemma histMass_modPol (γ : HistPolicy Y U) (t N : ℕ) (s : (Fin (t + N + 1) → Y) → U)
    (ys : Fin (t + N + 1) → Y) : histMass M π₀ (modPol γ (t + N) s) ys = histMass M π₀ γ ys := by
  rw [histMass_eq, histMass_eq, Fwd_congr M π₀ _ (extSeq ys) _ (Useq γ ys) 0 (t + N)
    (fun _ _ _ => rfl) (fun k _ hk => Useq_modPol γ _ s ys k (by omega))]

lemma predictor_modPol (γ : HistPolicy Y U) (t N : ℕ) (s : (Fin (t + N + 1) → Y) → U)
    (ys : Fin (t + N + 1) → Y) :
    predictor M π₀ (modPol γ (t + N) s) t ys = predictor M π₀ γ t ys := by
  show filterPred M π₀ (extSeq ys) (Useq (modPol γ (t + N) s) ys) t =
    filterPred M π₀ (extSeq ys) (Useq γ ys) t
  exact fp_congr M π₀ _ _ _ _ t (fun _ _ => rfl)
    (fun k hk => Useq_modPol γ _ s ys k (by omega))

lemma windowAt_modPol (γ : HistPolicy Y U) (t N : ℕ) (s : (Fin (t + N + 1) → Y) → U)
    (ys : Fin (t + N + 1) → Y) : windowAt (modPol γ (t + N) s) t ys = windowAt γ t ys := by
  rw [windowAt_eq, windowAt_eq]
  congr 1
  funext j
  exact Useq_modPol γ _ s ys _ (by omega)

end Hist

section Main

variable {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]

lemma Lterm_bound (M : POMDP X Y U) (πs π₀ : Measure X) [IsProbabilityMeasure π₀] (N t : ℕ)
    (γ : HistPolicy Y U) :
    ∑ ys : Fin (t + N + 1) → Y, histMass M π₀ γ ys *
      (2 * MarkovChainCLT.tvDist (post M (predictor M π₀ γ t ys) (windowAt γ t ys))
        (post M πs (windowAt γ t ys))) ≤ 2 := by
  calc ∑ ys : Fin (t + N + 1) → Y, histMass M π₀ γ ys *
      (2 * MarkovChainCLT.tvDist (post M (predictor M π₀ γ t ys) (windowAt γ t ys))
        (post M πs (windowAt γ t ys)))
      ≤ ∑ ys : Fin (t + N + 1) → Y, histMass M π₀ γ ys * 2 := by
        refine Finset.sum_le_sum fun ys _ => mul_le_mul_of_nonneg_left ?_
          (histMass_nonneg M π₀ γ ys)
        have := tv_le_one _ _ (post_le M (predictor M π₀ γ t ys) (windowAt γ t ys))
          (post_le M πs (windowAt γ t ys))
        linarith
    _ = 2 := by rw [← Finset.sum_mul, sum_histMass]; simp

lemma Lterm_ge (M : POMDP X Y U) (πs π₀ : Measure X) [IsProbabilityMeasure π₀] (N t : ℕ)
    (γ : HistPolicy Y U) :
    ∑ ys : Fin (t + N + 1) → Y, histMass M π₀ γ ys *
      (2 * MarkovChainCLT.tvDist (post M (predictor M π₀ γ t ys) (windowAt γ t ys))
        (post M πs (windowAt γ t ys))) ≤ Lterm M πs π₀ N t := by
  unfold Lterm
  exact le_ciSup (f := fun γ : HistPolicy Y U => ∑ ys : Fin (t + N + 1) → Y,
    histMass M π₀ γ ys * (2 * MarkovChainCLT.tvDist
      (post M (predictor M π₀ γ t ys) (windowAt γ t ys)) (post M πs (windowAt γ t ys))))
    ⟨2, by rintro _ ⟨γ, rfl⟩; exact Lterm_bound M πs π₀ N t γ⟩ γ

lemma Lterm_nonneg (M : POMDP X Y U) (πs π₀ : Measure X) [IsProbabilityMeasure π₀] (N t : ℕ) :
    0 ≤ Lterm M πs π₀ N t := by
  unfold Lterm
  refine Real.iSup_nonneg fun γ => Finset.sum_nonneg fun ys _ => ?_
  exact mul_nonneg (histMass_nonneg M π₀ γ ys) (mul_nonneg zero_le_two (tv_nonneg _ _))

lemma Lterm_le (M : POMDP X Y U) (πs π₀ : Measure X) [IsProbabilityMeasure π₀] (N t : ℕ) :
    Lterm M πs π₀ N t ≤ 2 := by
  haveI : Nonempty (HistPolicy Y U) := ⟨fun _ _ => Classical.arbitrary U⟩
  unfold Lterm
  exact ciSup_le fun γ => Lterm_bound M πs π₀ N t γ

/-- The unrolling argument of Appendices B and C. -/
lemma unroll (M : POMDP X Y U) (πs π₀ : Measure X) [IsProbabilityMeasure π₀] (N : ℕ)
    (D : Measure X × Window Y U N → ℝ) (K R : ℝ) (hK : 0 ≤ K) (hR0 : 0 ≤ R)
    (hD0 : ∀ z, 0 ≤ D z) (hDR : ∀ (π : Measure X) (I : Window Y U N), π Set.univ ≤ 1 → D (π, I) ≤ R)
    (hD : ∀ (π : Measure X) (I : Window Y U N), π Set.univ ≤ 1 → ∃ u : U,
      D (π, I) ≤ K * (2 * MarkovChainCLT.tvDist (post M π I) (post M πs I)) +
        M.β * ∑ y : Y, predY M π I u y * D (nextPrior M π I u, shift I u y)) :
    ∀ (k t : ℕ) (γ : HistPolicy Y U),
      ∑ ys : Fin (t + N + 1) → Y, histMass M π₀ γ ys * D (predictor M π₀ γ t ys, windowAt γ t ys)
        ≤ K * ∑ j ∈ Finset.range k, M.β ^ j * Lterm M πs π₀ N (t + j) + M.β ^ k * R := by
  have hβ0 := M.β_pos
  choose! sel hsel using hD
  have hpred : ∀ t (γ : HistPolicy Y U) (ys : Fin (t + N + 1) → Y),
      predictor M π₀ γ t ys Set.univ ≤ 1 := fun t γ ys =>
    fp_le M π₀ (by rw [measure_univ]) _ _ t
  intro k
  induction k with
  | zero =>
    intro t γ
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, pow_zero, one_mul, zero_add]
    calc ∑ ys : Fin (t + N + 1) → Y, histMass M π₀ γ ys * D (predictor M π₀ γ t ys, windowAt γ t ys)
        ≤ ∑ ys : Fin (t + N + 1) → Y, histMass M π₀ γ ys * R :=
          Finset.sum_le_sum fun ys _ => mul_le_mul_of_nonneg_left
            (hDR _ _ (hpred t γ ys)) (histMass_nonneg M π₀ γ ys)
      _ = R := by rw [← Finset.sum_mul, sum_histMass]; simp
  | succ k ih =>
    intro t γ
    set s : (Fin (t + N + 1) → Y) → U := fun ys => sel (predictor M π₀ γ t ys) (windowAt γ t ys)
    have hstep := fun ys => hsel (predictor M π₀ γ t ys) (windowAt γ t ys) (hpred t γ ys)
    have h1 : ∑ ys : Fin (t + N + 1) → Y, histMass M π₀ γ ys *
        D (predictor M π₀ γ t ys, windowAt γ t ys) ≤
        K * ∑ ys : Fin (t + N + 1) → Y, histMass M π₀ γ ys *
          (2 * MarkovChainCLT.tvDist (post M (predictor M π₀ γ t ys) (windowAt γ t ys))
            (post M πs (windowAt γ t ys))) +
        M.β * ∑ ys : Fin (t + N + 1) → Y, histMass M π₀ γ ys * ∑ y : Y,
          predY M (predictor M π₀ γ t ys) (windowAt γ t ys) (s ys) y *
            D (nextPrior M (predictor M π₀ γ t ys) (windowAt γ t ys) (s ys),
              shift (windowAt γ t ys) (s ys) y) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun ys _ => ?_
      have := mul_le_mul_of_nonneg_left (hstep ys) (histMass_nonneg M π₀ γ ys)
      calc histMass M π₀ γ ys * D (predictor M π₀ γ t ys, windowAt γ t ys) ≤ _ := this
        _ = _ := by ring
    have h2 : ∑ ys : Fin (t + N + 1) → Y, histMass M π₀ γ ys * ∑ y : Y,
          predY M (predictor M π₀ γ t ys) (windowAt γ t ys) (s ys) y *
            D (nextPrior M (predictor M π₀ γ t ys) (windowAt γ t ys) (s ys),
              shift (windowAt γ t ys) (s ys) y) =
        ∑ ys' : Fin (t + 1 + N + 1) → Y, histMass M π₀ (modPol γ (t + N) s) ys' *
          D (predictor M π₀ (modPol γ (t + N) s) (t + 1) ys', windowAt (modPol γ (t + N) s) (t + 1) ys') := by
      rw [chain M π₀ (modPol γ (t + N) s) t N D]
      refine Finset.sum_congr rfl fun ys _ => ?_
      rw [histMass_modPol, predictor_modPol, windowAt_modPol, Useq_modPol_at]
    have h3 := ih (t + 1) (modPol γ (t + N) s)
    have h4 := Lterm_ge M πs π₀ N t γ
    rw [h2] at h1
    have hsum : ∑ j ∈ Finset.range (k + 1), M.β ^ j * Lterm M πs π₀ N (t + j) =
        M.β * ∑ j ∈ Finset.range k, M.β ^ j * Lterm M πs π₀ N (t + 1 + j) +
          Lterm M πs π₀ N t := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [show t + (j + 1) = t + 1 + j by omega]; ring
      · simp
    rw [hsum]
    calc ∑ ys : Fin (t + N + 1) → Y, histMass M π₀ γ ys * D (predictor M π₀ γ t ys, windowAt γ t ys)
        ≤ K * Lterm M πs π₀ N t + M.β * (K * ∑ j ∈ Finset.range k,
            M.β ^ j * Lterm M πs π₀ N (t + 1 + j) + M.β ^ k * R) := by
          refine h1.trans (add_le_add (mul_le_mul_of_nonneg_left h4 hK)
            (mul_le_mul_of_nonneg_left h3 hβ0.le))
      _ = K * (M.β * ∑ j ∈ Finset.range k, M.β ^ j * Lterm M πs π₀ N (t + 1 + j) +
            Lterm M πs π₀ N t) + M.β ^ (k + 1) * R := by ring

/-- From the unrolled bound at time `0` to the series bound. -/
lemma unroll_limit (M : POMDP X Y U) (πs π₀ : Measure X) [IsProbabilityMeasure π₀] (N : ℕ)
    (E K R : ℝ) (hK : 0 ≤ K)
    (h : ∀ k : ℕ, E ≤ K * ∑ j ∈ Finset.range k, M.β ^ j * Lterm M πs π₀ N (0 + j) + M.β ^ k * R) :
    E ≤ K * ∑' t : ℕ, M.β ^ t * Lterm M πs π₀ N t := by
  have hβ0 := M.β_pos
  have hβ1 := M.β_lt_one
  have hnn : ∀ t, 0 ≤ M.β ^ t * Lterm M πs π₀ N t := fun t =>
    mul_nonneg (pow_nonneg hβ0.le t) (Lterm_nonneg M πs π₀ N t)
  have hsum : Summable (fun t => M.β ^ t * Lterm M πs π₀ N t) := by
    refine Summable.of_nonneg_of_le hnn (fun t => ?_)
      ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right 2)
    exact mul_le_mul_of_nonneg_left (Lterm_le M πs π₀ N t) (pow_nonneg hβ0.le t)
  have hk : ∀ k : ℕ, E ≤ K * ∑' t : ℕ, M.β ^ t * Lterm M πs π₀ N t + M.β ^ k * R := by
    intro k
    refine (h k).trans (add_le_add (mul_le_mul_of_nonneg_left ?_ hK) le_rfl)
    simp only [zero_add]
    exact hsum.sum_le_tsum _ (fun t _ => hnn t)
  have hlim : Tendsto (fun k : ℕ => K * ∑' t : ℕ, M.β ^ t * Lterm M πs π₀ N t + M.β ^ k * R)
      atTop (𝓝 (K * ∑' t : ℕ, M.β ^ t * Lterm M πs π₀ N t + 0 * R)) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const R)
  rw [zero_mul, add_zero] at hlim
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall hk)

/-- Identifying the time-`0` expectation with the sum over the first window. -/
lemma E0_eq (M : POMDP X Y U) (π₀ : Measure X) (γ : HistPolicy Y U) (N : ℕ)
    (D : Measure X × Window Y U N → ℝ) :
    ∑ ys : Fin (N + 1) → Y, histMass M π₀ γ ys * D (π₀, ((ys, histActs γ ys) : Window Y U N)) =
      ∑ ys : Fin (0 + N + 1) → Y, histMass M π₀ γ ys *
        D (predictor M π₀ γ 0 ys, windowAt γ 0 ys) := by
  let e0 : (Fin (0 + N + 1) → Y) ≃ (Fin (N + 1) → Y) :=
    { toFun := fun ys j => ys ⟨j, by omega⟩
      invFun := fun ys j => ys ⟨j, by omega⟩
      left_inv := fun ys => rfl
      right_inv := fun ys => rfl }
  rw [← e0.sum_comp]
  refine Finset.sum_congr rfl fun ys _ => ?_
  have hext : extSeq (e0 ys) = extSeq ys := by
    funext k
    unfold extSeq
    by_cases hk : k < N + 1
    · rw [dif_pos hk, dif_pos (by omega)]; rfl
    · rw [dif_neg hk, dif_neg (by omega)]
      show ys ⟨N, _⟩ = ys (Fin.last (0 + N))
      congr 1; ext; simp
  have hU : Useq γ (e0 ys) = Useq γ ys := by
    funext k; simp only [Useq, hext]
  have hm : histMass M π₀ γ (e0 ys) = histMass M π₀ γ ys := by
    rw [histMass_eq, histMass_eq, hext, hU]
    exact congrArg (fun n => (Fwd M π₀ (extSeq ys) (Useq γ ys) 0 n Set.univ).toReal)
      (zero_add N).symm
  have hw : ((e0 ys, histActs γ (e0 ys)) : Window Y U N) = windowAt γ 0 ys := by
    rw [windowAt_eq, histActs_eq, hU]
    congr 1
    · funext j
      show ys ⟨j, _⟩ = extSeq ys (0 + ↑j)
      rw [extSeq_lt ys _ (by omega)]
      congr 1; ext; simp
    · funext j; simp
  rw [hm, hw]
  rfl

end Main

end FMQC


open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace FMQC

open FiniteMemQL.Convergence
open scoped ENNReal

section Values

variable {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]

lemma jstar_bdd (M : POMDP X Y U) (z : Measure X) (hz : z Set.univ ≤ 1) :
    |Jstar M z| ≤ cNorm M / (1 - M.β) := by
  have h := vi_conv (Z := Measure X) (A := U) (Y := Y) {z | z Set.univ ≤ 1} (beliefCost M)
    (obsProb M) (filterUpdate M) M.β (cNorm M) M.β_pos.le M.β_lt_one (cNorm_nonneg M)
    (fun z hz u => beliefCost_bdd M (cNorm M) (c_le_cNorm M) (cNorm_nonneg M) z hz u)
    (fun _ _ _ => ENNReal.toReal_nonneg) (fun z hz u => sum_obsProb_le M z hz u)
    (fun z _ u y => normalize_univ_le _) (beliefBellman M) (fun V z => rfl) z hz
  exact h.2.2

lemma jpol_fix_bdd (M : POMDP X Y U) {N : ℕ} (φ : Window Y U N → U) (π : Measure X)
    (hπ : π Set.univ ≤ 1) (I : Window Y U N) :
    Jpol M φ (π, I) = chat M π I (φ I) + M.β * ∑ y : Y, predY M π I (φ I) y *
      Jpol M φ (nextPrior M π I (φ I), shift I (φ I) y) ∧
    |Jpol M φ (π, I)| ≤ cNorm M / (1 - M.β) := by
  have h := vi_conv (Z := Measure X × Window Y U N) (A := Unit) (Y := Y)
    {z | z.1 Set.univ ≤ 1} (fun z _ => chat M z.1 z.2 (φ z.2))
    (fun z _ y => predY M z.1 z.2 (φ z.2) y)
    (fun z _ y => (nextPrior M z.1 z.2 (φ z.2), shift z.2 (φ z.2) y)) M.β (cNorm M)
    M.β_pos.le M.β_lt_one (cNorm_nonneg M)
    (fun z _ _ => beliefCost_bdd M (cNorm M) (c_le_cNorm M) (cNorm_nonneg M) _
      (post_le M z.1 z.2) _)
    (fun _ _ _ => ENNReal.toReal_nonneg)
    (fun z _ _ => sum_obsProb_le M _ (post_le M z.1 z.2) _)
    (fun z _ _ _ => nextPrior_le M z.1 z.2 _) (polEval M φ)
    (fun V z => by rw [ciInf_const]; rfl) (π, I) hπ
  refine ⟨?_, h.2.2⟩
  have e : Jpol M φ = fun z' => limUnder atTop (fun n => (polEval M φ)^[n] 0 z') := rfl
  have := h.2.1
  rw [← e] at this
  exact this

lemma JN_fix (M : POMDP X Y U) {N : ℕ} (πs : Measure X) [IsProbabilityMeasure πs]
    (I : Window Y U N) :
    JN M πs I = ⨅ u : U, (Cstar M πs I u + M.β * ∑ y : Y, Pstar M πs I u y *
      JN M πs (shift I u y)) := by
  rw [← qStar_min_eq_JN M πs I]
  refine iInf_congr fun u => ?_
  rw [qStar_fixed_point M πs I u]
  simp only [qStar_min_eq_JN M πs]

lemma JN_bdd (M : POMDP X Y U) {N : ℕ} (πs : Measure X) [IsProbabilityMeasure πs]
    (I : Window Y U N) : |JN M πs I| ≤ cNorm M / (1 - M.β) := by
  have hβ0 := M.β_pos
  have hβ1 := M.β_lt_one
  obtain ⟨p0, hp0⟩ := Finite.exists_max (fun p : Window Y U N × U => |qStar M πs p.1 p.2|)
  have hinf : ∀ J : Window Y U N, |⨅ v : U, qStar M πs J v| ≤ |qStar M πs p0.1 p0.2| := by
    intro J
    have h := inf_diff (fun v => qStar M πs J v) (fun _ => (0 : ℝ)) |qStar M πs p0.1 p0.2|
      (fun v => by simpa using hp0 (J, v))
    simpa using h
  have hkey : |qStar M πs p0.1 p0.2| ≤ cNorm M + M.β * |qStar M πs p0.1 p0.2| := by
    have hfp := qStar_fixed_point M πs p0.1 p0.2
    calc |qStar M πs p0.1 p0.2| = |Cstar M πs p0.1 p0.2 + M.β * ∑ y : Y, Pstar M πs p0.1 p0.2 y *
          ⨅ v : U, qStar M πs (shift p0.1 p0.2 y) v| := by rw [hfp]
      _ ≤ |Cstar M πs p0.1 p0.2| + M.β * ∑ y : Y, Pstar M πs p0.1 p0.2 y *
          |⨅ v : U, qStar M πs (shift p0.1 p0.2 y) v| := by
          refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [abs_mul, abs_of_pos hβ0]
          refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (le_of_eq (Finset.sum_congr rfl fun y _ => ?_))) hβ0.le
          rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ Pstar M πs p0.1 p0.2 y from
            ENNReal.toReal_nonneg)]
      _ ≤ cNorm M + M.β * ∑ y : Y, Pstar M πs p0.1 p0.2 y * |qStar M πs p0.1 p0.2| := by
          refine add_le_add ?_ (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (hinf _) ENNReal.toReal_nonneg) hβ0.le)
          exact beliefCost_bdd M (cNorm M) (c_le_cNorm M) (cNorm_nonneg M) _ (post_le M _ _) _
      _ = cNorm M + M.β * ((∑ y : Y, Pstar M πs p0.1 p0.2 y) * |qStar M πs p0.1 p0.2|) := by
          rw [Finset.sum_mul]
      _ ≤ cNorm M + M.β * (1 * |qStar M πs p0.1 p0.2|) := by
          gcongr
          exact sum_obsProb_le M _ (post_le M _ _) _
      _ = cNorm M + M.β * |qStar M πs p0.1 p0.2| := by ring
  have hq : |qStar M πs p0.1 p0.2| ≤ cNorm M / (1 - M.β) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  rw [← qStar_min_eq_JN M πs I]
  exact (hinf I).trans hq

lemma step32 (M : POMDP X Y U) {N : ℕ} (πs : Measure X) [IsProbabilityMeasure πs]
    (π : Measure X) (hπ : π Set.univ ≤ 1) (I : Window Y U N) :
    ∃ u : U, |JN M πs I - JstarW M π I| ≤
      cNorm M / (1 - M.β) * (2 * MarkovChainCLT.tvDist (post M π I) (post M πs I)) +
        M.β * ∑ y : Y, predY M π I u y *
          |JN M πs (shift I u y) - JstarW M (nextPrior M π I u) (shift I u y)| := by
  haveI : IsFiniteMeasure π := ⟨lt_of_le_of_lt hπ ENNReal.one_lt_top⟩
  have hβ0 := M.β_pos
  have hβ1 := M.β_lt_one
  set f : U → ℝ := fun u => Cstar M πs I u + M.β * ∑ y : Y, Pstar M πs I u y *
    JN M πs (shift I u y) with hf
  set g : U → ℝ := fun u => chat M π I u + M.β * ∑ y : Y, predY M π I u y *
    JstarW M (nextPrior M π I u) (shift I u y) with hg
  obtain ⟨u0, hu0⟩ := Finite.exists_max (fun u => |f u - g u|)
  refine ⟨u0, ?_⟩
  rw [JN_fix M πs I, eq33_fin M π I]
  refine (inf_diff f g _ hu0).trans ?_
  set tv := MarkovChainCLT.tvDist (post M π I) (post M πs I)
  have htv : 0 ≤ tv := tv_nonneg _ _
  set S1 := ∑ y : Y, (predY M π I u0 y - Pstar M πs I u0 y) * JN M πs (shift I u0 y)
  set S2 := ∑ y : Y, predY M π I u0 y *
      (JN M πs (shift I u0 y) - JstarW M (nextPrior M π I u0) (shift I u0 y))
  have hs : (∑ y : Y, Pstar M πs I u0 y * JN M πs (shift I u0 y)) -
      (∑ y : Y, predY M π I u0 y * JstarW M (nextPrior M π I u0) (shift I u0 y)) = -S1 + S2 := by
    simp only [S1, S2]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  have e : f u0 - g u0 = (Cstar M πs I u0 - chat M π I u0) + M.β * (-S1) + M.β * S2 := by
    simp only [hf, hg]
    linear_combination M.β * hs
  rw [e]
  have h1 := chat_diff M π πs I u0
  have h2 := predY_sum_diff M π πs I u0 (fun y => JN M πs (shift I u0 y)) (cNorm M / (1 - M.β))
    (fun y => JN_bdd M πs _)
  have h3 : |∑ y : Y, predY M π I u0 y *
      (JN M πs (shift I u0 y) - JstarW M (nextPrior M π I u0) (shift I u0 y))| ≤
      ∑ y : Y, predY M π I u0 y *
        |JN M πs (shift I u0 y) - JstarW M (nextPrior M π I u0) (shift I u0 y)| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun y _ => ?_))
    rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ predY M π I u0 y from ENNReal.toReal_nonneg)]
  have key : 2 * cNorm M * tv + M.β * (cNorm M / (1 - M.β) * (2 * tv)) =
      cNorm M / (1 - M.β) * (2 * tv) := by
    have hne : (1 - M.β) ≠ 0 := by linarith
    field_simp
    ring
  have h3' : |S2| ≤ _ := h3
  calc |(Cstar M πs I u0 - chat M π I u0) + M.β * (-S1) + M.β * S2|
      ≤ |chat M π I u0 - Cstar M πs I u0| + M.β * |S1| + M.β * |S2| := by
        refine (abs_add_three _ _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos hβ0, abs_sub_comm]
    _ ≤ 2 * cNorm M * tv + M.β * (cNorm M / (1 - M.β) * (2 * tv)) + M.β * ∑ y : Y,
          predY M π I u0 y *
            |JN M πs (shift I u0 y) - JstarW M (nextPrior M π I u0) (shift I u0 y)| := by
        gcongr
    _ = _ := by rw [key]

lemma step33 (M : POMDP X Y U) {N : ℕ} (πs : Measure X) [IsProbabilityMeasure πs]
    (φ : Window Y U N → U)
    (hφ : ∀ I : Window Y U N, Cstar M πs I (φ I) +
      M.β * ∑ y : Y, Pstar M πs I (φ I) y * JN M πs (shift I (φ I) y) = JN M πs I)
    (π : Measure X) (hπ : π Set.univ ≤ 1) (I : Window Y U N) :
    ∃ u : U, |Jpol M φ (π, I) - JN M πs I| ≤
      cNorm M / (1 - M.β) * (2 * MarkovChainCLT.tvDist (post M π I) (post M πs I)) +
        M.β * ∑ y : Y, predY M π I u y *
          |Jpol M φ (nextPrior M π I u, shift I u y) - JN M πs (shift I u y)| := by
  have hβ0 := M.β_pos
  have hβ1 := M.β_lt_one
  refine ⟨φ I, ?_⟩
  set u0 := φ I
  rw [(jpol_fix_bdd M φ π hπ I).1, ← hφ I]
  set tv := MarkovChainCLT.tvDist (post M π I) (post M πs I)
  have htv : 0 ≤ tv := tv_nonneg _ _
  set S1 := ∑ y : Y, (predY M π I u0 y - Pstar M πs I u0 y) * JN M πs (shift I u0 y)
  set S2 := ∑ y : Y, predY M π I u0 y *
      (Jpol M φ (nextPrior M π I u0, shift I u0 y) - JN M πs (shift I u0 y))
  have hs : (∑ y : Y, predY M π I u0 y * Jpol M φ (nextPrior M π I u0, shift I u0 y)) -
      (∑ y : Y, Pstar M πs I u0 y * JN M πs (shift I u0 y)) = S1 + S2 := by
    simp only [S1, S2]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  have e : chat M π I u0 + M.β * ∑ y : Y, predY M π I u0 y *
      Jpol M φ (nextPrior M π I u0, shift I u0 y) -
      (Cstar M πs I u0 + M.β * ∑ y : Y, Pstar M πs I u0 y * JN M πs (shift I u0 y)) =
      (chat M π I u0 - Cstar M πs I u0) + M.β * S1 + M.β * S2 := by
    linear_combination M.β * hs
  rw [e]
  have h1 := chat_diff M π πs I u0
  have h2 := predY_sum_diff M π πs I u0 (fun y => JN M πs (shift I u0 y)) (cNorm M / (1 - M.β))
    (fun y => JN_bdd M πs _)
  have h3 : |S2| ≤ ∑ y : Y, predY M π I u0 y *
        |Jpol M φ (nextPrior M π I u0, shift I u0 y) - JN M πs (shift I u0 y)| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun y _ => ?_))
    rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ predY M π I u0 y from ENNReal.toReal_nonneg)]
  have key : 2 * cNorm M * tv + M.β * (cNorm M / (1 - M.β) * (2 * tv)) =
      cNorm M / (1 - M.β) * (2 * tv) := by
    have hne : (1 - M.β) ≠ 0 := by linarith
    field_simp
    ring
  calc |(chat M π I u0 - Cstar M πs I u0) + M.β * S1 + M.β * S2|
      ≤ |chat M π I u0 - Cstar M πs I u0| + M.β * |S1| + M.β * |S2| := by
        refine (abs_add_three _ _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_of_pos hβ0]
    _ ≤ 2 * cNorm M * tv + M.β * (cNorm M / (1 - M.β) * (2 * tv)) + M.β * ∑ y : Y,
          predY M π I u0 y *
            |Jpol M φ (nextPrior M π I u0, shift I u0 y) - JN M πs (shift I u0 y)| := by
        gcongr
    _ = _ := by rw [key]

theorem thm32 (M : POMDP X Y U)
    (N : ℕ) (πs π₀ : Measure X) [IsProbabilityMeasure πs] [IsProbabilityMeasure π₀]
    (γ₀ : HistPolicy Y U) :
    ∑ ys : Fin (N + 1) → Y, histMass M π₀ γ₀ ys *
        |JN M πs ((ys, histActs γ₀ ys) : Window Y U N) -
          JstarW M π₀ ((ys, histActs γ₀ ys) : Window Y U N)| ≤
      cNorm M / (1 - M.β) * ∑' t : ℕ, M.β ^ t * Lterm M πs π₀ N t := by
  have hβ1 := M.β_lt_one
  have hK : 0 ≤ cNorm M / (1 - M.β) := div_nonneg (cNorm_nonneg M) (by linarith)
  set D : Measure X × Window Y U N → ℝ := fun z => |JN M πs z.2 - JstarW M z.1 z.2|
  have hE := E0_eq M π₀ γ₀ N D
  apply unroll_limit M πs π₀ N _ _ (2 * (cNorm M / (1 - M.β))) hK
  intro k
  refine le_of_eq_of_le hE ?_
  refine unroll M πs π₀ N D _ _ hK (by positivity) (fun z => abs_nonneg _) ?_ ?_ k 0 γ₀
  · intro π I hπ
    have h1 := JN_bdd M πs I
    have h2 := jstar_bdd M (post M π I) (post_le M π I)
    show |JN M πs I - Jstar M (post M π I)| ≤ _
    have := abs_sub (JN M πs I) (Jstar M (post M π I))
    linarith
  · intro π I hπ
    exact step32 M πs π hπ I

theorem thm33 (M : POMDP X Y U)
    (N : ℕ) (πs π₀ : Measure X) [IsProbabilityMeasure πs] [IsProbabilityMeasure π₀]
    (γ₀ : HistPolicy Y U) (φN : Window Y U N → U)
    (hφ : ∀ I : Window Y U N, Cstar M πs I (φN I) +
      M.β * ∑ y : Y, Pstar M πs I (φN I) y * JN M πs (shift I (φN I) y) = JN M πs I) :
    ∑ ys : Fin (N + 1) → Y, histMass M π₀ γ₀ ys *
        |Jpol M φN (π₀, ((ys, histActs γ₀ ys) : Window Y U N)) -
          JstarW M π₀ ((ys, histActs γ₀ ys) : Window Y U N)| ≤
      2 * cNorm M / (1 - M.β) * ∑' t : ℕ, M.β ^ t * Lterm M πs π₀ N t := by
  have hβ1 := M.β_lt_one
  have hK : 0 ≤ cNorm M / (1 - M.β) := div_nonneg (cNorm_nonneg M) (by linarith)
  set D : Measure X × Window Y U N → ℝ := fun z => |Jpol M φN z - JN M πs z.2|
  have hE := E0_eq M π₀ γ₀ N D
  have hA : ∑ ys : Fin (N + 1) → Y, histMass M π₀ γ₀ ys *
      D (π₀, ((ys, histActs γ₀ ys) : Window Y U N)) ≤
      cNorm M / (1 - M.β) * ∑' t : ℕ, M.β ^ t * Lterm M πs π₀ N t := by
    apply unroll_limit M πs π₀ N _ _ (2 * (cNorm M / (1 - M.β))) hK
    intro k
    refine le_of_eq_of_le hE ?_
    refine unroll M πs π₀ N D _ _ hK (by positivity) (fun z => abs_nonneg _) ?_ ?_ k 0 γ₀
    · intro π I hπ
      have h1 := JN_bdd M πs I
      have h2 := (jpol_fix_bdd M φN π hπ I).2
      show |Jpol M φN (π, I) - JN M πs I| ≤ _
      have := abs_sub (Jpol M φN (π, I)) (JN M πs I)
      linarith
    · intro π I hπ
      exact step33 M πs φN hφ π hπ I
  have hB := thm32 M N πs π₀ γ₀
  calc ∑ ys : Fin (N + 1) → Y, histMass M π₀ γ₀ ys *
        |Jpol M φN (π₀, ((ys, histActs γ₀ ys) : Window Y U N)) -
          JstarW M π₀ ((ys, histActs γ₀ ys) : Window Y U N)|
      ≤ ∑ ys : Fin (N + 1) → Y, (histMass M π₀ γ₀ ys *
          D (π₀, ((ys, histActs γ₀ ys) : Window Y U N)) + histMass M π₀ γ₀ ys *
          |JN M πs ((ys, histActs γ₀ ys) : Window Y U N) -
            JstarW M π₀ ((ys, histActs γ₀ ys) : Window Y U N)|) := by
        refine Finset.sum_le_sum fun ys _ => ?_
        rw [← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ (histMass_nonneg M π₀ γ₀ ys)
        exact abs_sub_le _ _ _
    _ = _ := Finset.sum_add_distrib
    _ ≤ cNorm M / (1 - M.β) * ∑' t : ℕ, M.β ^ t * Lterm M πs π₀ N t +
          cNorm M / (1 - M.β) * ∑' t : ℕ, M.β ^ t * Lterm M πs π₀ N t := add_le_add hA hB
    _ = 2 * cNorm M / (1 - M.β) * ∑' t : ℕ, M.β ^ t * Lterm M πs π₀ N t := by ring

end Values

end FMQC

open FiniteMemQL.Convergence in
theorem solution {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (M : POMDP X Y U)
    (N : ℕ) (πs π₀ : Measure X) [IsProbabilityMeasure πs] [IsProbabilityMeasure π₀]
    (γ₀ : HistPolicy Y U) (φN : Window Y U N → U)
    (hφ : ∀ I : Window Y U N, Cstar M πs I (φN I) +
      M.β * ∑ y : Y, Pstar M πs I (φN I) y * JN M πs (shift I (φN I) y) = JN M πs I) :
    ∑ ys : Fin (N + 1) → Y, histMass M π₀ γ₀ ys *
        |Jpol M φN (π₀, ((ys, histActs γ₀ ys) : Window Y U N)) -
          JstarW M π₀ ((ys, histActs γ₀ ys) : Window Y U N)| ≤
      2 * cNorm M / (1 - M.β) * ∑' t : ℕ, M.β ^ t * Lterm M πs π₀ N t := by
  exact FMQC.thm33 M N πs π₀ γ₀ φN hφ
