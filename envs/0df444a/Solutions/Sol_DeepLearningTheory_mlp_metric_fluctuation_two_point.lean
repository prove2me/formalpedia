-- Prove2me | solution 1 for DeepLearningTheory.mlp_metric_fluctuation_two_point
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T01:17:36.186185+00:00
-- url     : https://prove2.me/submissions/f7ead209-c183-4a03-a7fa-01190ce98446

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork
import Definitions.Def_DLT_MLPInit

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open DeepLearningTheory

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem W5_DeepLearningTheory_L_gfacts {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} {v : ℝ≥0} (h : P.map f = gaussianReal 0 v) :
    AEMeasurable f P ∧ MemLp f 2 P ∧ ∫ ω, f ω ∂P = 0 ∧ ∫ ω, f ω * f ω ∂P = v := by
  have hf : AEMeasurable f P := by
    by_contra hc
    rw [Measure.map_of_not_aemeasurable hc] at h
    have h2 : (0 : Measure ℝ) Set.univ = gaussianReal 0 v Set.univ := by rw [h]
    simp at h2
  have hmem : MemLp f 2 P := by
    have h3 := memLp_id_gaussianReal' (μ := 0) (v := v) 2 (by norm_num)
    rw [← h] at h3
    exact (memLp_map_measure_iff aestronglyMeasurable_id hf).1 h3
  have hint : ∫ ω, f ω ∂P = 0 := by
    calc ∫ ω, f ω ∂P = ∫ y, y ∂(P.map f) := (integral_map hf aestronglyMeasurable_id).symm
      _ = 0 := by rw [h, integral_id_gaussianReal]
  refine ⟨hf, hmem, hint, ?_⟩
  calc ∫ ω, f ω * f ω ∂P = ∫ y, y * y ∂(P.map f) :=
        (integral_map hf (continuous_id.mul continuous_id).aestronglyMeasurable).symm
    _ = v := by
      rw [h]
      have h4 := variance_id_gaussianReal (μ := 0) (v := v)
      rw [variance_of_integral_eq_zero aemeasurable_id (by simp [integral_id_gaussianReal])] at h4
      simpa [sq] using h4

/-- First-layer parameter index: biases `b^{(1)}_i` and weights `W^{(1)}_{ij}`. -/
def W5_DeepLearningTheory_gidx (n : ℕ → ℕ) :
    Fin (n 1) ⊕ (Fin (n 1) × Fin (n 0)) → BiasIndex n ⊕ WeightIndex n
  | Sum.inl i => Sum.inl (Subtype.mk (1, (i : ℕ)) ⟨le_rfl, i.2⟩ :
      {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.2 < n p.1})
  | Sum.inr p => Sum.inr (Subtype.mk (1, (p.1 : ℕ), (p.2 : ℕ)) ⟨le_rfl, p.1.2, p.2.2⟩ :
      {q : ℕ × ℕ × ℕ // 1 ≤ q.1 ∧ q.2.1 < n q.1 ∧ q.2.2 < n (q.1 - 1)})

theorem W5_DeepLearningTheory_gidx_inj (n : ℕ → ℕ) :
    Function.Injective (W5_DeepLearningTheory_gidx n) := by
  intro a b h
  rcases a with i | ⟨i, j⟩ <;> rcases b with i' | ⟨i', j'⟩ <;>
    simp only [W5_DeepLearningTheory_gidx] at h
  · have h2 := congrArg Subtype.val (Sum.inl_injective h)
    simp only [Prod.mk.injEq, true_and] at h2
    exact congrArg Sum.inl (Fin.ext h2)
  · exact absurd h Sum.inl_ne_inr
  · exact absurd h Sum.inr_ne_inl
  · have h2 := congrArg Subtype.val (Sum.inr_injective h)
    simp only [Prod.mk.injEq, true_and] at h2
    rw [Fin.ext h2.1, Fin.ext h2.2]

/-- The first-layer parameters as a family indexed by a finite type. -/
def W5_DeepLearningTheory_Yv {Ω : Type*} {n : ℕ → ℕ} (b : Ω → ℕ → ℕ → ℝ)
    (W : Ω → ℕ → ℕ → ℕ → ℝ) : Fin (n 1) ⊕ (Fin (n 1) × Fin (n 0)) → Ω → ℝ
  | Sum.inl i => fun ω => b ω 1 i
  | Sum.inr p => fun ω => W ω 1 p.1 p.2

/-- Their variances. -/
noncomputable def W5_DeepLearningTheory_vv (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) :
    Fin (n 1) ⊕ (Fin (n 1) × Fin (n 0)) → ℝ≥0
  | Sum.inl _ => Cb 1
  | Sum.inr _ => CW 1 / (n 0 : ℝ≥0)

theorem W5_DeepLearningTheory_marg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ → ℕ} {Cb CW : ℕ → ℝ≥0}
    {b : Ω → ℕ → ℕ → ℝ} {W : Ω → ℕ → ℕ → ℕ → ℝ} (hinit : IsMLPInit P n Cb CW b W)
    (k : Fin (n 1) ⊕ (Fin (n 1) × Fin (n 0))) :
    P.map (W5_DeepLearningTheory_Yv (n := n) b W k) =
      gaussianReal 0 (W5_DeepLearningTheory_vv n Cb CW k) := by
  rcases k with i | ⟨i, j⟩
  · exact hinit.2.1 1 i le_rfl i.2
  · exact hinit.2.2 1 i j le_rfl i.2 j.2

theorem W5_DeepLearningTheory_indepY {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ → ℕ} {Cb CW : ℕ → ℝ≥0}
    {b : Ω → ℕ → ℕ → ℝ} {W : Ω → ℕ → ℕ → ℕ → ℝ} (hinit : IsMLPInit P n Cb CW b W) :
    iIndepFun (fun k => W5_DeepLearningTheory_Yv (n := n) b W k) P := by
  have h := hinit.1.precomp (W5_DeepLearningTheory_gidx_inj n)
  have e : (fun k => W5_DeepLearningTheory_Yv (n := n) b W k) =
      (fun k => (fun (p : BiasIndex n ⊕ WeightIndex n) =>
        Sum.elim (fun q (ω : Ω) => b ω q.1.1 q.1.2)
          (fun q (ω : Ω) => W ω q.1.1 q.1.2.1 q.1.2.2) p) (W5_DeepLearningTheory_gidx n k)) := by
    funext k
    rcases k with i | ⟨i, j⟩ <;> rfl
  rw [e]
  exact h

theorem W5_DeepLearningTheory_joint {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ → ℕ} {Cb CW : ℕ → ℝ≥0}
    {b : Ω → ℕ → ℕ → ℝ} {W : Ω → ℕ → ℕ → ℕ → ℝ} (hinit : IsMLPInit P n Cb CW b W) :
    P.map (fun ω k => W5_DeepLearningTheory_Yv (n := n) b W k ω) =
      Measure.pi (fun k => gaussianReal 0 (W5_DeepLearningTheory_vv n Cb CW k)) := by
  rw [(iIndepFun_iff_map_fun_eq_pi_map
    (fun k => (W5_DeepLearningTheory_L_gfacts (W5_DeepLearningTheory_marg hinit k)).1)).1
    (W5_DeepLearningTheory_indepY hinit)]
  congr 1
  funext k
  exact W5_DeepLearningTheory_marg hinit k

open Complex in
theorem W5_DeepLearningTheory_charY {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ → ℕ} {Cb CW : ℕ → ℝ≥0}
    {b : Ω → ℕ → ℕ → ℝ} {W : Ω → ℕ → ℕ → ℕ → ℝ} (hinit : IsMLPInit P n Cb CW b W)
    (c : Fin (n 1) ⊕ (Fin (n 1) × Fin (n 0)) → ℝ) :
    ∫ ω, cexp (↑(∑ k, c k * W5_DeepLearningTheory_Yv (n := n) b W k ω) * I) ∂P =
      cexp (((-(∑ k, (W5_DeepLearningTheory_vv n Cb CW k : ℝ) * c k ^ 2) / 2 : ℝ) : ℂ)) := by
  have hYm : AEMeasurable (fun ω k => W5_DeepLearningTheory_Yv (n := n) b W k ω) P :=
    aemeasurable_pi_lambda _ (fun k =>
      (W5_DeepLearningTheory_L_gfacts (W5_DeepLearningTheory_marg hinit k)).1)
  have hF : Continuous (fun y : Fin (n 1) ⊕ (Fin (n 1) × Fin (n 0)) → ℝ =>
      cexp (↑(∑ k, c k * y k) * I)) := by fun_prop
  calc ∫ ω, cexp (↑(∑ k, c k * W5_DeepLearningTheory_Yv (n := n) b W k ω) * I) ∂P
      = ∫ y, cexp (↑(∑ k, c k * y k) * I)
          ∂(P.map (fun ω k => W5_DeepLearningTheory_Yv (n := n) b W k ω)) :=
        (integral_map hYm hF.aestronglyMeasurable).symm
    _ = ∫ y, ∏ k, cexp (↑(c k * y k) * I)
          ∂(Measure.pi (fun k => gaussianReal 0 (W5_DeepLearningTheory_vv n Cb CW k))) := by
        rw [W5_DeepLearningTheory_joint hinit]
        congr 1
        funext y
        rw [← Complex.exp_sum]
        congr 1
        push_cast
        rw [Finset.sum_mul]
    _ = ∏ k, ∫ x, cexp (↑(c k * x) * I) ∂(gaussianReal 0 (W5_DeepLearningTheory_vv n Cb CW k)) :=
        integral_fintype_prod_eq_prod (f := fun k (x : ℝ) => cexp (↑(c k * x) * I))
    _ = ∏ k, cexp (((-((W5_DeepLearningTheory_vv n Cb CW k : ℝ) * c k ^ 2 / 2) : ℝ) : ℂ)) := by
        refine Finset.prod_congr rfl fun k _ => ?_
        have h := charFun_gaussianReal (μ := (0 : ℝ)) (v := W5_DeepLearningTheory_vv n Cb CW k) (c k)
        rw [charFun_apply] at h
        simp only [RCLike.inner_apply, conj_trivial] at h
        rw [h]
        congr 1
        push_cast
        ring
    _ = _ := by
        rw [← Complex.exp_sum]
        congr 1
        push_cast
        rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]

section Law

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

/-- Coefficients of `⟪Z, u⟫` in terms of the first-layer parameters. -/
noncomputable def W5_DeepLearningTheory_cc {n : ℕ → ℕ} (ν : τ → Fin (n 1)) (xs : τ → ℕ → ℝ)
    (u : τ → ℝ) : Fin (n 1) ⊕ (Fin (n 1) × Fin (n 0)) → ℝ
  | Sum.inl i => ∑ t, if ν t = i then u t else 0
  | Sum.inr p => ∑ t, if ν t = p.1 then u t * xs t p.2 else 0

theorem W5_DeepLearningTheory_I1 {Ω : Type*} {n : ℕ → ℕ} (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (ν : τ → Fin (n 1)) (xs : τ → ℕ → ℝ)
    (u : τ → ℝ) (ω : Ω) :
    ∑ t, mlpPreact n σ (b ω) (W ω) (xs t) 1 (ν t) * u t =
      ∑ k, W5_DeepLearningTheory_cc ν xs u k * W5_DeepLearningTheory_Yv (n := n) b W k ω := by
  have hz : ∀ t, mlpPreact n σ (b ω) (W ω) (xs t) 1 (ν t) =
      b ω 1 (ν t) + ∑ j : Fin (n 0), W ω 1 (ν t) j * xs t j := by
    intro t
    simp [mlpPreact, Finset.sum_range]
  simp_rw [hz]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [W5_DeepLearningTheory_cc, W5_DeepLearningTheory_Yv]
  have e1 : ∑ i : Fin (n 1), (∑ t, if ν t = i then u t else 0) * b ω 1 i =
      ∑ t, b ω 1 (ν t) * u t := by
    simp_rw [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_ite_eq]
    simp [mul_comm]
  have e2 : ∑ i : Fin (n 1), ∑ j : Fin (n 0),
      (∑ t, if ν t = i then u t * xs t j else 0) * W ω 1 i j =
      ∑ t, (∑ j : Fin (n 0), W ω 1 (ν t) j * xs t j) * u t := by
    simp_rw [Finset.sum_mul, ite_mul, zero_mul]
    calc ∑ i : Fin (n 1), ∑ j : Fin (n 0), ∑ t,
          (if ν t = i then u t * xs t j * W ω 1 i j else 0)
        = ∑ i : Fin (n 1), ∑ t, ∑ j : Fin (n 0),
          (if ν t = i then u t * xs t j * W ω 1 i j else 0) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ t, ∑ i : Fin (n 1), ∑ j : Fin (n 0),
          (if ν t = i then u t * xs t j * W ω 1 i j else 0) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.sum_eq_single (ν t)]
          · simp only [if_true]
            refine Finset.sum_congr rfl fun j _ => by ring
          · intro i _ hi
            exact Finset.sum_eq_zero fun j _ => if_neg (fun h => hi h.symm)
          · simp
  rw [e1, e2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => by ring

theorem W5_DeepLearningTheory_Lfib {n : ℕ → ℕ} (ν : τ → Fin (n 1)) (a c : τ → ℝ) :
    ∑ i : Fin (n 1), (∑ s, if ν s = i then a s else 0) * (∑ t, if ν t = i then c t else 0) =
      ∑ s, ∑ t, if ν s = ν t then a s * c t else 0 := by
  calc ∑ i : Fin (n 1), (∑ s, if ν s = i then a s else 0) * (∑ t, if ν t = i then c t else 0)
      = ∑ i : Fin (n 1), ∑ s, ∑ t,
          (if ν s = i then a s else 0) * (if ν t = i then c t else 0) :=
        Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul_sum]
    _ = ∑ s, ∑ i : Fin (n 1), ∑ t,
          (if ν s = i then a s else 0) * (if ν t = i then c t else 0) := Finset.sum_comm
    _ = ∑ s, ∑ t, ∑ i : Fin (n 1),
          (if ν s = i then a s else 0) * (if ν t = i then c t else 0) :=
        Finset.sum_congr rfl fun s _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_eq_single (ν s)]
        · by_cases h : ν s = ν t
          · simp [h]
          · simp [h, Ne.symm h]
        · intro i _ hi
          simp [Ne.symm hi]
        · simp

theorem W5_DeepLearningTheory_I2 {n : ℕ → ℕ} (Cb CW : ℕ → ℝ≥0) (ν : τ → Fin (n 1))
    (xs : τ → ℕ → ℝ) (u : τ → ℝ) :
    ∑ k, (W5_DeepLearningTheory_vv n Cb CW k : ℝ) * W5_DeepLearningTheory_cc ν xs u k ^ 2 =
      ∑ s, ∑ t, u s * (kron (ν s) (ν t) *
        ((Cb 1 : ℝ) + (CW 1 : ℝ) * inputKernel (n 0) (xs s) (xs t))) * u t := by
  have hA : ∑ i : Fin (n 1), (W5_DeepLearningTheory_vv n Cb CW (Sum.inl i) : ℝ) *
      W5_DeepLearningTheory_cc ν xs u (Sum.inl i) ^ 2 =
      (Cb 1 : ℝ) * ∑ s, ∑ t, if ν s = ν t then u s * u t else 0 := by
    simp only [W5_DeepLearningTheory_vv, W5_DeepLearningTheory_cc]
    rw [← Finset.mul_sum]
    simp_rw [sq]
    rw [W5_DeepLearningTheory_Lfib]
  have hB : ∑ p : Fin (n 1) × Fin (n 0), (W5_DeepLearningTheory_vv n Cb CW (Sum.inr p) : ℝ) *
      W5_DeepLearningTheory_cc ν xs u (Sum.inr p) ^ 2 =
      ((CW 1 / (n 0 : ℝ≥0) : ℝ≥0) : ℝ) * ∑ s, ∑ t, ∑ j : Fin (n 0),
        if ν s = ν t then (u s * xs s j) * (u t * xs t j) else 0 := by
    rw [Fintype.sum_prod_type]
    simp only [W5_DeepLearningTheory_vv, W5_DeepLearningTheory_cc]
    simp_rw [sq]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp_rw [W5_DeepLearningTheory_Lfib]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_comm
  rw [Fintype.sum_sum_type, hA, hB, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hk : kron (ν s) (ν t) = if ν s = ν t then 1 else 0 := by
    simp [kron, Fin.val_inj]
  rw [hk]
  by_cases h : ν s = ν t
  · simp only [h, if_true, one_mul]
    have e : ∑ j : Fin (n 0), (u s * xs s j) * (u t * xs t j) =
        u s * u t * ∑ j : Fin (n 0), xs s j * xs t j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, inputKernel, Finset.sum_range]
    push_cast
    ring
  · simp [h]

open Matrix in
theorem W5_DeepLearningTheory_Spsd {n : ℕ → ℕ} (Cb CW : ℕ → ℝ≥0) (ν : τ → Fin (n 1))
    (xs : τ → ℕ → ℝ) :
    Matrix.PosSemidef (fun s t : τ => kron (ν s) (ν t) *
        ((Cb 1 : ℝ) + (CW 1 : ℝ) * inputKernel (n 0) (xs s) (xs t))) := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext fun s t => ?_
    simp only [star_trivial]
    unfold kron inputKernel
    by_cases h : (ν s : ℕ) = ν t
    · simp only [h, if_true]
      first
        | rfl
        | (rw [Finset.sum_congr rfl (fun j _ => mul_comm (xs t j) (xs s j))])
        | (rw [Finset.sum_congr rfl (fun j _ => mul_comm (xs s j) (xs t j))])
    · simp [h, Ne.symm h]
  · intro x
    have hq : star x ⬝ᵥ ((fun s t : τ => kron (ν s) (ν t) *
        ((Cb 1 : ℝ) + (CW 1 : ℝ) * inputKernel (n 0) (xs s) (xs t))) *ᵥ x) =
        ∑ s, ∑ t, x s * (kron (ν s) (ν t) *
          ((Cb 1 : ℝ) + (CW 1 : ℝ) * inputKernel (n 0) (xs s) (xs t))) * x t := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    rw [hq, ← W5_DeepLearningTheory_I2]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _)

theorem W5_DeepLearningTheory_zmeas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ → ℕ} {Cb CW : ℕ → ℝ≥0} {σ : ℝ → ℝ}
    {b : Ω → ℕ → ℕ → ℝ} {W : Ω → ℕ → ℕ → ℕ → ℝ} (hinit : IsMLPInit P n Cb CW b W)
    (x : ℕ → ℝ) (i : Fin (n 1)) :
    AEMeasurable (fun ω => mlpPreact n σ (b ω) (W ω) x 1 i) P := by
  have e : (fun ω => mlpPreact n σ (b ω) (W ω) x 1 i) =
      fun ω => b ω 1 i + ∑ j ∈ Finset.range (n 0), W ω 1 i j * x j := by
    funext ω
    simp [mlpPreact]
  rw [e]
  exact (W5_DeepLearningTheory_L_gfacts (hinit.2.1 1 i le_rfl i.2)).1.add
    (Finset.aemeasurable_fun_sum _ fun j hj =>
      (W5_DeepLearningTheory_L_gfacts
        (hinit.2.2 1 i j le_rfl i.2 (Finset.mem_range.mp hj))).1.mul_const _)

open Matrix in
theorem W5_DeepLearningTheory_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ → ℕ} {Cb CW : ℕ → ℝ≥0} {σ : ℝ → ℝ}
    {b : Ω → ℕ → ℕ → ℝ} {W : Ω → ℕ → ℕ → ℕ → ℝ} (hinit : IsMLPInit P n Cb CW b W)
    (ν : τ → Fin (n 1)) (xs : τ → ℕ → ℝ) :
    P.map (fun ω => WithLp.toLp 2 (fun t => mlpPreact n σ (b ω) (W ω) (xs t) 1 (ν t : ℕ))) =
      multivariateGaussian 0 (fun s t : τ => kron (ν s) (ν t) *
        ((Cb 1 : ℝ) + (CW 1 : ℝ) * inputKernel (n 0) (xs s) (xs t))) := by
  have hZ : AEMeasurable
      (fun ω => WithLp.toLp 2 (fun t => mlpPreact n σ (b ω) (W ω) (xs t) 1 (ν t : ℕ))) P :=
    (WithLp.measurable_toLp 2 _).comp_aemeasurable
      (aemeasurable_pi_lambda _ fun t => W5_DeepLearningTheory_zmeas hinit (xs t) (ν t))
  haveI : IsProbabilityMeasure (P.map
      (fun ω => WithLp.toLp 2 (fun t => mlpPreact n σ (b ω) (W ω) (xs t) 1 (ν t : ℕ)))) :=
    Measure.isProbabilityMeasure_map hZ
  haveI hG : IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ τ) (fun s t : τ => kron (ν s) (ν t) *
        ((Cb 1 : ℝ) + (CW 1 : ℝ) * inputKernel (n 0) (xs s) (xs t)))) :=
    isGaussian_multivariateGaussian
  haveI : IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ τ)
      (fun s t : τ => kron (ν s) (ν t) *
        ((Cb 1 : ℝ) + (CW 1 : ℝ) * inputKernel (n 0) (xs s) (xs t)))) :=
    IsGaussian.toIsProbabilityMeasure _
  apply Measure.ext_of_charFun
  funext u
  rw [charFun_multivariateGaussian (W5_DeepLearningTheory_Spsd Cb CW ν xs), charFun_apply,
    integral_map hZ (by fun_prop)]
  have hin : ∀ ω, inner ℝ (WithLp.toLp 2
      (fun t => mlpPreact n σ (b ω) (W ω) (xs t) 1 (ν t : ℕ))) u =
      ∑ k, W5_DeepLearningTheory_cc ν xs (WithLp.ofLp u) k *
        W5_DeepLearningTheory_Yv (n := n) b W k ω := by
    intro ω
    rw [PiLp.inner_apply, ← W5_DeepLearningTheory_I1 σ]
    simp [RCLike.inner_apply, conj_trivial, mul_comm]
  simp_rw [hin]
  rw [W5_DeepLearningTheory_charY hinit]
  congr 1
  rw [W5_DeepLearningTheory_I2]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
  have hq : WithLp.ofLp u ⬝ᵥ (fun s t : τ => kron (ν s) (ν t) *
        ((Cb 1 : ℝ) + (CW 1 : ℝ) * inputKernel (n 0) (xs s) (xs t))) *ᵥ WithLp.ofLp u =
        ∑ s, ∑ t, WithLp.ofLp u s * (kron (ν s) (ν t) *
          ((Cb 1 : ℝ) + (CW 1 : ℝ) * inputKernel (n 0) (xs s) (xs t))) * WithLp.ofLp u t := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
  rw [hq]
  push_cast
  ring

end Law

theorem W5_DeepLearningTheory_mlp_first_layer_gaussian {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    {D : ℕ} (x : Fin D → ℕ → ℝ) :
    P.map (fun ω => WithLp.toLp 2
        (fun p : Fin (n 1) × Fin D => mlpPreact n σ (b ω) (W ω) (x p.2) 1 (p.1 : ℕ)))
      = multivariateGaussian 0
          (fun p q : Fin (n 1) × Fin D =>
            kron p.1 q.1 * firstLayerMetric (Cb 1) (CW 1) (n 0) x p.2 q.2) :=
  W5_DeepLearningTheory_law (σ := σ) hinit (fun p : Fin (n 1) × Fin D => p.1)
    (fun p : Fin (n 1) × Fin D => x p.2)

theorem W5_DeepLearningTheory_law_neuron {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ → ℕ} {Cb CW : ℕ → ℝ≥0} {σ : ℝ → ℝ}
    {b : Ω → ℕ → ℕ → ℝ} {W : Ω → ℕ → ℕ → ℕ → ℝ} (hinit : IsMLPInit P n Cb CW b W)
    {D : ℕ} (x : Fin D → ℕ → ℝ) (j : ℕ) (hj : j < n 1) :
    P.map (fun ω => WithLp.toLp 2 (fun α : Fin D => mlpPreact n σ (b ω) (W ω) (x α) 1 j)) =
      multivariateGaussian 0 (firstLayerMetric (Cb 1) (CW 1) (n 0) x) := by
  have h := W5_DeepLearningTheory_law (σ := σ) hinit (fun _ : Fin D => (⟨j, hj⟩ : Fin (n 1))) x
  have e : (fun s t : Fin D => kron ((⟨j, hj⟩ : Fin (n 1)) : ℕ) ((⟨j, hj⟩ : Fin (n 1)) : ℕ) *
      ((Cb 1 : ℝ) + (CW 1 : ℝ) * inputKernel (n 0) (x s) (x t))) =
      firstLayerMetric (Cb 1) (CW 1) (n 0) x := by
    funext s t
    simp [kron, firstLayerMetric]
  rw [e] at h
  exact h

theorem W5_DeepLearningTheory_avg_neuron {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ → ℕ} {Cb CW : ℕ → ℝ≥0} {σ : ℝ → ℝ}
    {b : Ω → ℕ → ℕ → ℝ} {W : Ω → ℕ → ℕ → ℕ → ℝ} (hinit : IsMLPInit P n Cb CW b W)
    {D : ℕ} (x : Fin D → ℕ → ℝ) (j : ℕ) (hj : j < n 1) (F : (Fin D → ℝ) → ℝ)
    (hF : Measurable F) :
    ∫ ω, F (fun α => mlpPreact n σ (b ω) (W ω) (x α) 1 j) ∂P =
      gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) F := by
  have hZ : AEMeasurable
      (fun ω => WithLp.toLp 2 (fun α : Fin D => mlpPreact n σ (b ω) (W ω) (x α) 1 j)) P :=
    (WithLp.measurable_toLp 2 _).comp_aemeasurable
      (aemeasurable_pi_lambda _ fun α => W5_DeepLearningTheory_zmeas hinit (x α) ⟨j, hj⟩)
  have hG : Measurable (fun v : EuclideanSpace ℝ (Fin D) => F (fun α => v α)) :=
    hF.comp (by fun_prop)
  unfold gaussAvg
  rw [← W5_DeepLearningTheory_law_neuron (σ := σ) hinit x j hj,
    integral_map hZ hG.aestronglyMeasurable]

theorem W5_DeepLearningTheory_mlp_first_layer_activation_two_point {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    (hσm : Measurable σ) (hσ : HasPolyGrowth σ) (x : Fin 2 → ℕ → ℝ) (j : ℕ) (hj : j < n 1) :
    ∫ ω, σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j) ∂P
      = gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 0) * σ (u 1)) :=
  W5_DeepLearningTheory_avg_neuron hinit x j hj (fun u => σ (u 0) * σ (u 1)) (by fun_prop)

theorem W5_DeepLearningTheory_mlp_first_layer_activation_four_point_same_neuron {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    (hσm : Measurable σ) (hσ : HasPolyGrowth σ) (x : Fin 4 → ℕ → ℝ) (j : ℕ) (hj : j < n 1) :
    ∫ ω, σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j) *
        σ (mlpPreact n σ (b ω) (W ω) (x 2) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 3) 1 j) ∂P
      = gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x)
          (fun u => σ (u 0) * σ (u 1) * σ (u 2) * σ (u 3)) :=
  W5_DeepLearningTheory_avg_neuron hinit x j hj
    (fun u => σ (u 0) * σ (u 1) * σ (u 2) * σ (u 3)) (by fun_prop)

/-- Neuron owning a first-layer parameter. -/
def W5_DeepLearningTheory_owner {n : ℕ → ℕ} : Fin (n 1) ⊕ (Fin (n 1) × Fin (n 0)) → Fin (n 1)
  | Sum.inl i => i
  | Sum.inr p => p.1

/-- A first-layer preactivation of neuron `j'` as a function of the parameters it owns. -/
noncomputable def W5_DeepLearningTheory_Gn {n : ℕ → ℕ} (j' : Fin (n 1)) (x : ℕ → ℝ)
    (y : (Finset.univ.filter (fun q : Fin (n 1) ⊕ (Fin (n 1) × Fin (n 0)) =>
      W5_DeepLearningTheory_owner q = j')) → ℝ) : ℝ :=
  y ⟨Sum.inl j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩ +
    ∑ l : Fin (n 0), y ⟨Sum.inr (j', l), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩ * x l

theorem W5_DeepLearningTheory_Gn_eq {Ω : Type*} {n : ℕ → ℕ} (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (j : ℕ) (hj : j < n 1) (x : ℕ → ℝ) (ω : Ω) :
    mlpPreact n σ (b ω) (W ω) x 1 j =
      W5_DeepLearningTheory_Gn ⟨j, hj⟩ x
        (fun q => W5_DeepLearningTheory_Yv (n := n) b W q.1 ω) := by
  simp [mlpPreact, W5_DeepLearningTheory_Gn, W5_DeepLearningTheory_Yv, Finset.sum_range]

theorem W5_DeepLearningTheory_Gn_meas {n : ℕ → ℕ} (j' : Fin (n 1)) (x : ℕ → ℝ) :
    Measurable (W5_DeepLearningTheory_Gn (n := n) j' x) := by
  unfold W5_DeepLearningTheory_Gn
  fun_prop

theorem W5_DeepLearningTheory_mlp_first_layer_activation_four_point_two_neurons {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    (hσm : Measurable σ) (hσ : HasPolyGrowth σ) (x : Fin 4 → ℕ → ℝ) (j k : ℕ) (hj : j < n 1) (hk : k < n 1) (hjk : j ≠ k) :
    ∫ ω, σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j) *
        σ (mlpPreact n σ (b ω) (W ω) (x 2) 1 k) * σ (mlpPreact n σ (b ω) (W ω) (x 3) 1 k) ∂P
      = gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 0) * σ (u 1)) *
          gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 2) * σ (u 3)) := by
  have hdisj : Disjoint
      (Finset.univ.filter (fun q : Fin (n 1) ⊕ (Fin (n 1) × Fin (n 0)) =>
        W5_DeepLearningTheory_owner q = ⟨j, hj⟩))
      (Finset.univ.filter (fun q : Fin (n 1) ⊕ (Fin (n 1) × Fin (n 0)) =>
        W5_DeepLearningTheory_owner q = ⟨k, hk⟩)) := by
    rw [Finset.disjoint_filter]
    intro q _ h1 h2
    apply hjk
    have := congrArg Fin.val (h1.symm.trans h2)
    simpa using this
  have hind := (W5_DeepLearningTheory_indepY hinit).indepFun_finset₀ _ _ hdisj
    (fun q => (W5_DeepLearningTheory_L_gfacts (W5_DeepLearningTheory_marg hinit q)).1)
  have hφm : Measurable (fun y => σ (W5_DeepLearningTheory_Gn ⟨j, hj⟩ (x 0) y) *
      σ (W5_DeepLearningTheory_Gn ⟨j, hj⟩ (x 1) y)) :=
    (hσm.comp (W5_DeepLearningTheory_Gn_meas _ (x 0))).mul
      (hσm.comp (W5_DeepLearningTheory_Gn_meas _ (x 1)))
  have hψm : Measurable (fun y => σ (W5_DeepLearningTheory_Gn ⟨k, hk⟩ (x 2) y) *
      σ (W5_DeepLearningTheory_Gn ⟨k, hk⟩ (x 3) y)) :=
    (hσm.comp (W5_DeepLearningTheory_Gn_meas _ (x 2))).mul
      (hσm.comp (W5_DeepLearningTheory_Gn_meas _ (x 3)))
  have hAm : ∀ (S : Finset (Fin (n 1) ⊕ (Fin (n 1) × Fin (n 0)))),
      AEMeasurable (fun ω (q : S) => W5_DeepLearningTheory_Yv (n := n) b W q.1 ω) P :=
    fun S => aemeasurable_pi_lambda _ fun q =>
      (W5_DeepLearningTheory_L_gfacts (W5_DeepLearningTheory_marg hinit q.1)).1
  have e1 : ∀ ω, σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j) *
        σ (mlpPreact n σ (b ω) (W ω) (x 2) 1 k) * σ (mlpPreact n σ (b ω) (W ω) (x 3) 1 k) =
      (σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j)) *
      (σ (mlpPreact n σ (b ω) (W ω) (x 2) 1 k) * σ (mlpPreact n σ (b ω) (W ω) (x 3) 1 k)) := by
    intro ω; ring
  simp_rw [e1, W5_DeepLearningTheory_Gn_eq σ b W j hj, W5_DeepLearningTheory_Gn_eq σ b W k hk]
  have key := (hind.comp hφm hψm).integral_fun_mul_eq_mul_integral
    (hφm.comp_aemeasurable (hAm _)).aestronglyMeasurable
    (hψm.comp_aemeasurable (hAm _)).aestronglyMeasurable
  simp only [Function.comp_apply] at key
  rw [key]
  have f1 := W5_DeepLearningTheory_avg_neuron (σ := σ) hinit x j hj
    (fun u => σ (u 0) * σ (u 1)) (by fun_prop)
  have f2 := W5_DeepLearningTheory_avg_neuron (σ := σ) hinit x k hk
    (fun u => σ (u 2) * σ (u 3)) (by fun_prop)
  simp only [W5_DeepLearningTheory_Gn_eq σ b W j hj, W5_DeepLearningTheory_Gn_eq σ b W k hk] at f1 f2
  rw [← f1, ← f2]

/-! ### All moments -/

section AM
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `f` has finite moments of every finite order. -/
def W5_DeepLearningTheory_AM (P : Measure Ω) (f : Ω → ℝ) : Prop :=
  ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp f p P

theorem W5_DeepLearningTheory_htrip (p : ℝ≥0∞) : ENNReal.HolderTriple (2 * p) (2 * p) p :=
  ⟨by
    rw [← two_mul, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top),
      ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]⟩

theorem W5_DeepLearningTheory_AM_mul {f g : Ω → ℝ} (hf : W5_DeepLearningTheory_AM P f)
    (hg : W5_DeepLearningTheory_AM P g) : W5_DeepLearningTheory_AM P (fun ω => f ω * g ω) := by
  intro p hp
  have h2 : 2 * p ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hp
  haveI := W5_DeepLearningTheory_htrip p
  exact (hg (2 * p) h2).mul' (hf (2 * p) h2)

theorem W5_DeepLearningTheory_AM_sum {ι : Type*} (s : Finset ι) {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ s, W5_DeepLearningTheory_AM P (f i)) :
    W5_DeepLearningTheory_AM P (fun ω => ∑ i ∈ s, f i ω) :=
  fun p hp => by
    have h := memLp_finset_sum' s (fun i hi => hf i hi p hp)
    rw [Finset.sum_fn] at h
    exact h

theorem W5_DeepLearningTheory_AM_const (c : ℝ) : W5_DeepLearningTheory_AM P (fun _ => c) :=
  fun p _ => memLp_const c

theorem W5_DeepLearningTheory_AM_gauss {f : Ω → ℝ} {v : ℝ≥0} (h : P.map f = gaussianReal 0 v) :
    W5_DeepLearningTheory_AM P f := by
  intro p hp
  have hf := (W5_DeepLearningTheory_L_gfacts h).1
  have h3 := memLp_id_gaussianReal' (μ := 0) (v := v) p hp
  rw [← h] at h3
  exact (memLp_map_measure_iff aestronglyMeasurable_id hf).1 h3

theorem W5_DeepLearningTheory_AM_int {f : Ω → ℝ} (hf : W5_DeepLearningTheory_AM P f) :
    Integrable f P :=
  (hf 1 ENNReal.one_ne_top).integrable le_rfl

end AM


/-! ### One-dimensional Gaussian moments -/

noncomputable def W5_DeepLearningTheory_NM (k : ℕ) : ℝ :=
  ∫ x : ℝ, x ^ k * Real.exp (-(1 / 2) * x ^ 2)

theorem W5_DeepLearningTheory_NM0 : W5_DeepLearningTheory_NM 0 = Real.sqrt (2 * Real.pi) := by
  simp only [W5_DeepLearningTheory_NM, pow_zero, one_mul]
  rw [integral_gaussian]
  congr 1
  ring

theorem W5_DeepLearningTheory_NHrec (q : ℝ) (hq : -1 < q) :
    ∫ x in Set.Ioi (0 : ℝ), x ^ (q + 2) * Real.exp (-(1 / 2) * x ^ (2 : ℝ)) =
      (q + 1) * ∫ x in Set.Ioi (0 : ℝ), x ^ q * Real.exp (-(1 / 2) * x ^ (2 : ℝ)) := by
  rw [integral_rpow_mul_exp_neg_mul_rpow two_pos (by linarith) (by norm_num),
    integral_rpow_mul_exp_neg_mul_rpow two_pos hq (by norm_num)]
  have e1 : -((q + 2) + 1) / 2 = -(q + 1) / 2 + (-1) := by ring
  have e2 : ((q + 2) + 1) / 2 = (q + 1) / 2 + 1 := by ring
  have hne : (q + 1) / 2 ≠ 0 := by
    have : 0 < (q + 1) / 2 := by linarith
    exact this.ne'
  rw [e1, e2, Real.rpow_add (by norm_num), Real.Gamma_add_one hne, Real.rpow_neg_one]
  ring

theorem W5_DeepLearningTheory_NMeven (j : ℕ) :
    W5_DeepLearningTheory_NM (2 * j) =
      2 * ∫ x in Set.Ioi (0 : ℝ), x ^ (2 * (j : ℝ)) * Real.exp (-(1 / 2) * x ^ (2 : ℝ)) := by
  unfold W5_DeepLearningTheory_NM
  have h := integral_comp_abs (f := fun x : ℝ => x ^ (2 * j) * Real.exp (-(1 / 2) * x ^ 2))
  have habs : ∀ x : ℝ, |x| ^ (2 * j) * Real.exp (-(1 / 2) * |x| ^ 2) =
      x ^ (2 * j) * Real.exp (-(1 / 2) * x ^ 2) := by
    intro x
    rw [pow_mul, sq_abs, ← pow_mul]
  simp only [habs] at h
  rw [h]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
    Real.rpow_two]

theorem W5_DeepLearningTheory_NMrec (j : ℕ) :
    W5_DeepLearningTheory_NM (2 * (j + 1)) =
      (2 * (j : ℝ) + 1) * W5_DeepLearningTheory_NM (2 * j) := by
  rw [W5_DeepLearningTheory_NMeven, W5_DeepLearningTheory_NMeven]
  have := W5_DeepLearningTheory_NHrec (2 * (j : ℝ)) (by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith)
  rw [show (2 * ((j + 1 : ℕ) : ℝ)) = 2 * (j : ℝ) + 2 by push_cast; ring, this]
  ring

theorem W5_DeepLearningTheory_NM4 : W5_DeepLearningTheory_NM 4 = 3 * Real.sqrt (2 * Real.pi) := by
  have h2 := W5_DeepLearningTheory_NMrec 0
  norm_num at h2
  have h4 := W5_DeepLearningTheory_NMrec 1
  norm_num at h4
  rw [h4, h2, W5_DeepLearningTheory_NM0]

theorem W5_DeepLearningTheory_gm4std : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hpdf : ∀ x, gaussianPDFReal 0 1 x • x ^ 4 =
      (Real.sqrt (2 * Real.pi))⁻¹ * (x ^ 4 * Real.exp (-(1 / 2) * x ^ 2)) := by
    intro x
    rw [smul_eq_mul]
    unfold gaussianPDFReal
    push_cast
    ring_nf
  simp_rw [hpdf]
  rw [integral_const_mul]
  change (Real.sqrt (2 * Real.pi))⁻¹ * W5_DeepLearningTheory_NM 4 = 3
  rw [W5_DeepLearningTheory_NM4]
  have : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

theorem W5_DeepLearningTheory_gm4 (v : ℝ≥0) :
    ∫ x, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have hmap : (gaussianReal 0 1).map (fun x => Real.sqrt v * x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt (NNReal.coe_nonneg v)]
  rw [← hmap, integral_map (by fun_prop : Measurable (fun x : ℝ => Real.sqrt v * x)).aemeasurable
    (by fun_prop : Continuous (fun x : ℝ => x ^ 4)).aestronglyMeasurable]
  simp_rw [mul_pow]
  rw [integral_const_mul, W5_DeepLearningTheory_gm4std,
    show Real.sqrt v ^ 4 = (v : ℝ) ^ 2 by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (NNReal.coe_nonneg v)]]
  ring

theorem W5_DeepLearningTheory_gm3 (v : ℝ≥0) : ∫ x, x ^ 3 ∂(gaussianReal 0 v) = 0 := by
  have h := integral_map (μ := gaussianReal 0 v) (φ := fun x : ℝ => -x) (f := fun x : ℝ => x ^ 3)
    measurable_neg.aemeasurable (by fun_prop : Continuous (fun x : ℝ => x ^ 3)).aestronglyMeasurable
  rw [gaussianReal_map_neg, neg_zero] at h
  simp only [Odd.neg_pow (by decide : Odd 3), integral_neg] at h
  linarith

theorem W5_DeepLearningTheory_gm2 (v : ℝ≥0) : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
  have h4 := variance_id_gaussianReal (μ := 0) (v := v)
  rw [variance_of_integral_eq_zero aemeasurable_id (by simp [integral_id_gaussianReal])] at h4
  simpa using h4

theorem W5_DeepLearningTheory_gm1 (v : ℝ≥0) : ∫ x, x ^ 1 ∂(gaussianReal 0 v) = 0 := by
  simp [integral_id_gaussianReal]

theorem W5_DeepLearningTheory_gm0 (v : ℝ≥0) : ∫ x, x ^ 0 ∂(gaussianReal 0 v) = 1 := by
  simp

/-! ### Fourth moments of i.i.d. centered Gaussians -/

theorem W5_DeepLearningTheory_Lfour {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ℕ → ℝ) (v : ℝ)
    (g0 : g 0 = 1) (g1 : g 1 = 0) (g2 : g 2 = v) (g3 : g 3 = 0) (g4 : g 4 = 3 * v ^ 2)
    (c1 c2 c3 c4 : ι) :
    ∏ q, g ((if c1 = q then 1 else 0) + (if c2 = q then 1 else 0) +
      (if c3 = q then 1 else 0) + (if c4 = q then 1 else 0)) =
      v ^ 2 * ((if c1 = c2 then 1 else 0) * (if c3 = c4 then 1 else 0) +
        (if c1 = c3 then 1 else 0) * (if c2 = c4 then 1 else 0) +
        (if c1 = c4 then 1 else 0) * (if c2 = c3 then 1 else 0)) := by
  by_cases a : c1 = c2 <;> by_cases b : c1 = c3 <;> by_cases c : c1 = c4
  · subst a b c
    rw [Finset.prod_eq_single c1 (fun i _ hi => by simp [Ne.symm hi, g0])
      (fun h => absurd (Finset.mem_univ _) h)]
    norm_num [g4]
    ring
  · subst a b
    rw [Finset.prod_eq_zero (Finset.mem_univ c1) (by simp [Ne.symm c, g3])]
    simp [c, Ne.symm c]
  · subst a c
    rw [Finset.prod_eq_zero (Finset.mem_univ c1) (by simp [Ne.symm b, g3])]
    simp [b, Ne.symm b]
  · subst a
    by_cases d : c3 = c4
    · subst d
      rw [Finset.prod_eq_mul c1 c3 b (fun i _ hi => by simp [Ne.symm hi.1, Ne.symm hi.2, g0])
        (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)]
      simp [b, Ne.symm b, g2]
      ring
    · rw [Finset.prod_eq_zero (Finset.mem_univ c3) (by simp [b, Ne.symm d, g1])]
      simp [b, c, d]
  · subst b c
    rw [Finset.prod_eq_zero (Finset.mem_univ c1) (by simp [Ne.symm a, g3])]
    simp [a, Ne.symm a]
  · subst b
    by_cases d : c2 = c4
    · subst d
      rw [Finset.prod_eq_mul c1 c2 a (fun i _ hi => by simp [Ne.symm hi.1, Ne.symm hi.2, g0])
        (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)]
      simp [a, Ne.symm a, g2]
      ring
    · rw [Finset.prod_eq_zero (Finset.mem_univ c2) (by simp [a, Ne.symm d, g1])]
      simp [a, c, d]
  · subst c
    by_cases d : c2 = c3
    · subst d
      rw [Finset.prod_eq_mul c1 c2 a (fun i _ hi => by simp [Ne.symm hi.1, Ne.symm hi.2, g0])
        (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)]
      simp [a, Ne.symm a, g2]
      ring
    · rw [Finset.prod_eq_zero (Finset.mem_univ c2) (by simp [a, Ne.symm d, g1])]
      simp [a, b, d]
  · rw [Finset.prod_eq_zero (Finset.mem_univ c1)
      (by simp [Ne.symm a, Ne.symm b, Ne.symm c, g1])]
    simp [a, b, c]

theorem W5_DeepLearningTheory_pimono4 {ι : Type*} [Fintype ι] [DecidableEq ι] (a b c d : ι)
    (w : ι → ℝ) :
    w a * w b * w c * w d = ∏ i, w i ^ ((if a = i then 1 else 0) + (if b = i then 1 else 0) +
      (if c = i then 1 else 0) + (if d = i then 1 else 0)) := by
  simp_rw [pow_add]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_boole, Finset.prod_pow_boole, Finset.prod_pow_boole, Finset.prod_pow_boole]
  simp

theorem W5_DeepLearningTheory_pi4 {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ℝ≥0)
    (a b c d : ι) :
    ∫ y, y a * y b * y c * y d ∂(Measure.pi (fun _ : ι => gaussianReal 0 v)) =
      (v : ℝ) ^ 2 * ((if a = b then 1 else 0) * (if c = d then 1 else 0) +
        (if a = c then 1 else 0) * (if b = d then 1 else 0) +
        (if a = d then 1 else 0) * (if b = c then 1 else 0)) := by
  simp_rw [W5_DeepLearningTheory_pimono4 a b c d]
  rw [integral_fintype_prod_eq_prod (f := fun i (x : ℝ) => x ^ ((if a = i then 1 else 0) +
    (if b = i then 1 else 0) + (if c = i then 1 else 0) + (if d = i then 1 else 0)))]
  exact W5_DeepLearningTheory_Lfour (fun k => ∫ x, x ^ k ∂(gaussianReal 0 v)) v
    (W5_DeepLearningTheory_gm0 v) (W5_DeepLearningTheory_gm1 v) (W5_DeepLearningTheory_gm2 v)
    (W5_DeepLearningTheory_gm3 v) (W5_DeepLearningTheory_gm4 v) a b c d


/-! ### Fourth moments of multivariate Gaussians -/

section MG4
variable {τ : Type*} [Fintype τ] [DecidableEq τ]

theorem W5_DeepLearningTheory_u2mul (F : τ → τ → ℝ) (h : τ → ℝ) :
    (∑ a, ∑ b, F a b) * (∑ c, h c) = ∑ a, ∑ b, ∑ c, F a b * h c := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]

theorem W5_DeepLearningTheory_u3mul (F : τ → τ → τ → ℝ) (h : τ → ℝ) :
    (∑ a, ∑ b, ∑ c, F a b c) * (∑ d, h d) = ∑ a, ∑ b, ∑ c, ∑ d, F a b c * h d := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]

theorem W5_DeepLearningTheory_U1 (F : τ → τ → τ → τ → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d * ((if a = b then (1 : ℝ) else 0) * (if c = d then 1 else 0))
      = ∑ a, ∑ c, F a a c c := by
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : ∀ b, ∑ c, ∑ d, F a b c d * ((if a = b then (1 : ℝ) else 0) * (if c = d then 1 else 0))
      = (∑ c, F a b c c) * (if a = b then 1 else 0) := by
    intro b
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp_rw [← mul_assoc]
    rw [Finset.sum_mul_boole]
    simp
  rw [Finset.sum_congr rfl fun b _ => h b, Finset.sum_mul_boole]
  simp

theorem W5_DeepLearningTheory_U2 (F : τ → τ → τ → τ → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d * ((if a = c then (1 : ℝ) else 0) * (if b = d then 1 else 0))
      = ∑ a, ∑ b, F a b a b := by
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h : ∀ c, ∑ d, F a b c d * ((if a = c then (1 : ℝ) else 0) * (if b = d then 1 else 0))
      = F a b c b * (if a = c then 1 else 0) := by
    intro c
    simp_rw [← mul_assoc]
    rw [Finset.sum_mul_boole]
    simp
  rw [Finset.sum_congr rfl fun c _ => h c, Finset.sum_mul_boole]
  simp

theorem W5_DeepLearningTheory_U3 (F : τ → τ → τ → τ → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d * ((if a = d then (1 : ℝ) else 0) * (if b = c then 1 else 0))
      = ∑ a, ∑ b, F a b b a := by
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h : ∀ c, ∑ d, F a b c d * ((if a = d then (1 : ℝ) else 0) * (if b = c then 1 else 0))
      = F a b c a * (if b = c then 1 else 0) := by
    intro c
    simp_rw [mul_comm (if a = _ then (1 : ℝ) else 0), ← mul_assoc]
    rw [Finset.sum_mul_boole]
    simp
  rw [Finset.sum_congr rfl fun c _ => h c, Finset.sum_mul_boole]
  simp

open Matrix in
open scoped MatrixOrder in
theorem W5_DeepLearningTheory_mg4 (S : Matrix τ τ ℝ) (hS : S.PosSemidef) (a b c d : τ) :
    ∫ u, u a * u b * u c * u d ∂(multivariateGaussian 0 S) =
      S a b * S c d + S a c * S b d + S a d * S b c := by
  set R := CFC.sqrt S with hRdef
  have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hRt : R.transpose = R := by
    have h := (CFC.sqrt_nonneg S).isSelfAdjoint
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      at h
    exact h
  have hSR : ∀ p q, S p q = ∑ k, R p k * R q k := by
    intro p q
    rw [← hRR, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show R k q = R.transpose q k from rfl, hRt]
  have hstep : ∫ u, u a * u b * u c * u d ∂(multivariateGaussian 0 S) =
      ∫ w, (R *ᵥ w) a * (R *ᵥ w) b * (R *ᵥ w) c * (R *ᵥ w) d
        ∂(Measure.pi (fun _ : τ => gaussianReal 0 1)) := by
    rw [multivariateGaussian, integral_map (by fun_prop) (by fun_prop),
      ← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
    simp [hRdef]
  rw [hstep]
  have hexp : ∀ w : τ → ℝ, (R *ᵥ w) a * (R *ᵥ w) b * (R *ᵥ w) c * (R *ᵥ w) d =
      ∑ p, ∑ q, ∑ r, ∑ s, (R a p * R b q * R c r * R d s) * (w p * w q * w r * w s) := by
    intro w
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul_sum, W5_DeepLearningTheory_u2mul, W5_DeepLearningTheory_u3mul]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring
  simp_rw [hexp]
  have hcoord : ∀ p : τ, W5_DeepLearningTheory_AM (Measure.pi (fun _ : τ => gaussianReal 0 1))
      (fun w : τ → ℝ => w p) :=
    fun p => W5_DeepLearningTheory_AM_gauss
      (measurePreserving_eval (fun _ : τ => gaussianReal 0 1) p).map_eq
  have hint : ∀ p q r s : τ, Integrable (fun w : τ → ℝ => (R a p * R b q * R c r * R d s) *
      (w p * w q * w r * w s)) (Measure.pi (fun _ : τ => gaussianReal 0 1)) :=
    fun p q r s => (W5_DeepLearningTheory_AM_int (W5_DeepLearningTheory_AM_mul
      (W5_DeepLearningTheory_AM_mul (W5_DeepLearningTheory_AM_mul (hcoord p) (hcoord q))
        (hcoord r)) (hcoord s))).const_mul _
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ fun q _ =>
    integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun s _ => hint p q r s)]
  rw [Finset.sum_congr rfl fun p _ => integral_finsetSum _ (fun q _ =>
    integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun s _ => hint p q r s)]
  rw [Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    integral_finsetSum _ (fun r _ => integrable_finsetSum _ fun s _ => hint p q r s)]
  rw [Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun r _ => integral_finsetSum _ (fun s _ => hint p q r s)]
  simp only [integral_const_mul, W5_DeepLearningTheory_pi4, NNReal.coe_one, one_pow, one_mul]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [W5_DeepLearningTheory_U1 (fun p q r s => R a p * R b q * R c r * R d s),
    W5_DeepLearningTheory_U2 (fun p q r s => R a p * R b q * R c r * R d s),
    W5_DeepLearningTheory_U3 (fun p q r s => R a p * R b q * R c r * R d s)]
  simp only [hSR, Finset.sum_mul_sum]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

end MG4

theorem W5_DeepLearningTheory_mlp_first_layer_four_point {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    (x : Fin 4 → ℕ → ℝ) (i : Fin 4 → ℕ) (hi : ∀ a, i a < n 1) :
    ∫ ω, mlpPreact n σ (b ω) (W ω) (x 0) 1 (i 0) * mlpPreact n σ (b ω) (W ω) (x 1) 1 (i 1) *
        mlpPreact n σ (b ω) (W ω) (x 2) 1 (i 2) * mlpPreact n σ (b ω) (W ω) (x 3) 1 (i 3) ∂P
      = kron (i 0) (i 1) * kron (i 2) (i 3) *
            firstLayerMetric (Cb 1) (CW 1) (n 0) x 0 1 * firstLayerMetric (Cb 1) (CW 1) (n 0) x 2 3
        + kron (i 0) (i 2) * kron (i 1) (i 3) *
            firstLayerMetric (Cb 1) (CW 1) (n 0) x 0 2 * firstLayerMetric (Cb 1) (CW 1) (n 0) x 1 3
        + kron (i 0) (i 3) * kron (i 1) (i 2) *
            firstLayerMetric (Cb 1) (CW 1) (n 0) x 0 3 * firstLayerMetric (Cb 1) (CW 1) (n 0) x 1 2
      := by
  set ν : Fin 4 → Fin (n 1) := fun a => ⟨i a, hi a⟩ with hν
  have hZ : AEMeasurable
      (fun ω => WithLp.toLp 2 (fun t : Fin 4 => mlpPreact n σ (b ω) (W ω) (x t) 1 (ν t : ℕ))) P :=
    (WithLp.measurable_toLp 2 _).comp_aemeasurable
      (aemeasurable_pi_lambda _ fun t => W5_DeepLearningTheory_zmeas hinit (x t) (ν t))
  have hlaw := W5_DeepLearningTheory_law (σ := σ) hinit ν x
  have hF : Continuous (fun u : EuclideanSpace ℝ (Fin 4) => u 0 * u 1 * u 2 * u 3) := by fun_prop
  calc ∫ ω, mlpPreact n σ (b ω) (W ω) (x 0) 1 (i 0) * mlpPreact n σ (b ω) (W ω) (x 1) 1 (i 1) *
        mlpPreact n σ (b ω) (W ω) (x 2) 1 (i 2) * mlpPreact n σ (b ω) (W ω) (x 3) 1 (i 3) ∂P
      = ∫ u, u 0 * u 1 * u 2 * u 3 ∂(P.map
          (fun ω => WithLp.toLp 2 (fun t : Fin 4 => mlpPreact n σ (b ω) (W ω) (x t) 1 (ν t : ℕ)))) :=
        (integral_map hZ hF.aestronglyMeasurable).symm
    _ = _ := by
        rw [hlaw, W5_DeepLearningTheory_mg4 _ (W5_DeepLearningTheory_Spsd Cb CW ν x)]
        simp only [hν, firstLayerMetric]
        ring

/-! ### Metric fluctuations -/

section Fluct
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem W5_DeepLearningTheory_AM_sub {f g : Ω → ℝ} (hf : W5_DeepLearningTheory_AM P f)
    (hg : W5_DeepLearningTheory_AM P g) : W5_DeepLearningTheory_AM P (fun ω => f ω - g ω) :=
  fun p hp => (hf p hp).sub (hg p hp)

theorem W5_DeepLearningTheory_AM_pow {f : Ω → ℝ} (hf : W5_DeepLearningTheory_AM P f) :
    ∀ k : ℕ, W5_DeepLearningTheory_AM P (fun ω => f ω ^ k) := by
  intro k
  induction k with
  | zero => simpa using W5_DeepLearningTheory_AM_const (P := P) 1
  | succ k ih =>
    simp_rw [pow_succ]
    exact W5_DeepLearningTheory_AM_mul ih hf

theorem W5_DeepLearningTheory_AM_poly {σ : ℝ → ℝ} (hσm : Measurable σ) (hσ : HasPolyGrowth σ)
    {f : Ω → ℝ} (hf : W5_DeepLearningTheory_AM P f) :
    W5_DeepLearningTheory_AM P (fun ω => σ (f ω)) := by
  obtain ⟨C, k, hb⟩ := hσ
  have habs : W5_DeepLearningTheory_AM P (fun ω => |f ω|) := fun p hp => by
    simpa [Real.norm_eq_abs] using (hf p hp).norm
  have hg : W5_DeepLearningTheory_AM P (fun ω => C * (1 + |f ω|) ^ k) :=
    W5_DeepLearningTheory_AM_mul (W5_DeepLearningTheory_AM_const C)
      (W5_DeepLearningTheory_AM_pow (W5_DeepLearningTheory_AM_sum (Finset.univ : Finset (Fin 2))
        (f := fun i ω => if i = 0 then 1 else |f ω|) (fun i _ => by
          by_cases h : i = 0
          · simp only [h, if_true]; exact W5_DeepLearningTheory_AM_const (P := P) 1
          · simp only [h, if_false]; exact habs) |> fun h => by
            simpa [Fin.sum_univ_two] using h) k)
  intro p hp
  refine (hg p hp).of_le (hσm.comp_aemeasurable ((hf 1 ENNReal.one_ne_top).1.aemeasurable)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs]
  exact (hb (f ω)).trans (le_abs_self _)

end Fluct

theorem W5_DeepLearningTheory_AMz1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ → ℕ} {Cb CW : ℕ → ℝ≥0} {σ : ℝ → ℝ}
    {b : Ω → ℕ → ℕ → ℝ} {W : Ω → ℕ → ℕ → ℕ → ℝ} (hinit : IsMLPInit P n Cb CW b W)
    (x : ℕ → ℝ) (j : ℕ) (hj : j < n 1) :
    W5_DeepLearningTheory_AM P (fun ω => mlpPreact n σ (b ω) (W ω) x 1 j) := by
  have e : (fun ω => mlpPreact n σ (b ω) (W ω) x 1 j) =
      fun ω => b ω 1 j + ∑ l ∈ Finset.range (n 0), W ω 1 j l * x l := by
    funext ω
    simp [mlpPreact]
  rw [e]
  refine W5_DeepLearningTheory_AM_sum (Finset.univ : Finset (Fin 2))
    (f := fun i ω => if i = 0 then b ω 1 j else ∑ l ∈ Finset.range (n 0), W ω 1 j l * x l)
    (fun i _ => ?_) |> fun h => by simpa [Fin.sum_univ_two] using h
  by_cases h : i = 0
  · simp only [h, if_true]
    exact W5_DeepLearningTheory_AM_gauss (hinit.2.1 1 j le_rfl hj)
  · simp only [h, if_false]
    exact W5_DeepLearningTheory_AM_sum _ fun l hl => W5_DeepLearningTheory_AM_mul
      (W5_DeepLearningTheory_AM_gauss (hinit.2.2 1 j l le_rfl hj (Finset.mem_range.mp hl)))
      (W5_DeepLearningTheory_AM_const (x l))

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    (hσm : Measurable σ) (hσ : HasPolyGrowth σ) (hn₁ : 0 < n 1) (x : Fin 4 → ℕ → ℝ) :
    ∫ ω, ((CW 2 : ℝ) * (1 / (n 1 : ℝ)) * ∑ j ∈ Finset.range (n 1),
          (σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j)
            - gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 0) * σ (u 1)))) *
        ((CW 2 : ℝ) * (1 / (n 1 : ℝ)) * ∑ j ∈ Finset.range (n 1),
          (σ (mlpPreact n σ (b ω) (W ω) (x 2) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 3) 1 j)
            - gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 2) * σ (u 3)))) ∂P
      = (1 / (n 1 : ℝ)) * (CW 2 : ℝ) ^ 2 *
          (gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x)
              (fun u => σ (u 0) * σ (u 1) * σ (u 2) * σ (u 3))
            - gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 0) * σ (u 1)) *
              gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 2) * σ (u 3))) := by
  set G := firstLayerMetric (Cb 1) (CW 1) (n 0) x with hG
  set A01 := gaussAvg G (fun u => σ (u 0) * σ (u 1)) with hA01
  set A23 := gaussAvg G (fun u => σ (u 2) * σ (u 3)) with hA23
  set A4 := gaussAvg G (fun u => σ (u 0) * σ (u 1) * σ (u 2) * σ (u 3)) with hA4
  set s := Finset.range (n 1) with hs
  set c : ℝ := (CW 2 : ℝ) * (1 / (n 1 : ℝ)) with hc
  -- the centred activation products
  set D : ℕ → Ω → ℝ := fun j ω =>
    σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j) - A01 with hD
  set D' : ℕ → Ω → ℝ := fun j ω =>
    σ (mlpPreact n σ (b ω) (W ω) (x 2) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 3) 1 j) - A23 with hD'
  have hAMs : ∀ (y : ℕ → ℝ) (j : ℕ), j < n 1 →
      W5_DeepLearningTheory_AM P (fun ω => σ (mlpPreact n σ (b ω) (W ω) y 1 j)) :=
    fun y j hj => W5_DeepLearningTheory_AM_poly hσm hσ (W5_DeepLearningTheory_AMz1 hinit y j hj)
  have hAMD : ∀ j ∈ s, W5_DeepLearningTheory_AM P (D j) := fun j hj =>
    W5_DeepLearningTheory_AM_sub (W5_DeepLearningTheory_AM_mul
      (hAMs (x 0) j (Finset.mem_range.mp hj)) (hAMs (x 1) j (Finset.mem_range.mp hj)))
      (W5_DeepLearningTheory_AM_const A01)
  have hAMD' : ∀ j ∈ s, W5_DeepLearningTheory_AM P (D' j) := fun j hj =>
    W5_DeepLearningTheory_AM_sub (W5_DeepLearningTheory_AM_mul
      (hAMs (x 2) j (Finset.mem_range.mp hj)) (hAMs (x 3) j (Finset.mem_range.mp hj)))
      (W5_DeepLearningTheory_AM_const A23)
  have e : ∀ ω, (c * ∑ j ∈ s, D j ω) * (c * ∑ k ∈ s, D' k ω) =
      ∑ j ∈ s, ∑ k ∈ s, c ^ 2 * (D j ω * D' k ω) := by
    intro ω
    rw [mul_mul_mul_comm, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  simp only [hD, hD'] at e
  simp_rw [e]
  rw [integral_finsetSum _ (fun j hj => integrable_finsetSum _ fun k hk =>
    (W5_DeepLearningTheory_AM_int (W5_DeepLearningTheory_AM_mul (hAMD j hj)
      (hAMD' k hk))).const_mul _)]
  rw [Finset.sum_congr rfl fun j hj => integral_finsetSum _ (fun k hk =>
    (W5_DeepLearningTheory_AM_int (W5_DeepLearningTheory_AM_mul (hAMD j hj)
      (hAMD' k hk))).const_mul _)]
  simp only [integral_const_mul]
  -- means of the centred products vanish
  have hmean : ∀ j ∈ s, ∫ ω, D j ω ∂P = 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have f1 := W5_DeepLearningTheory_avg_neuron (σ := σ) hinit x j hj'
      (fun u => σ (u 0) * σ (u 1)) (by fun_prop)
    simp only [hD]
    rw [integral_sub (W5_DeepLearningTheory_AM_int (W5_DeepLearningTheory_AM_mul
      (hAMs (x 0) j hj') (hAMs (x 1) j hj'))) (integrable_const _), integral_const, f1]
    simp [hA01, hG]
  have hmean' : ∀ j ∈ s, ∫ ω, D' j ω ∂P = 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have f1 := W5_DeepLearningTheory_avg_neuron (σ := σ) hinit x j hj'
      (fun u => σ (u 2) * σ (u 3)) (by fun_prop)
    simp only [hD']
    rw [integral_sub (W5_DeepLearningTheory_AM_int (W5_DeepLearningTheory_AM_mul
      (hAMs (x 2) j hj') (hAMs (x 3) j hj'))) (integrable_const _), integral_const, f1]
    simp [hA23, hG]
  -- off-diagonal terms vanish by independence of distinct neurons
  have hoff : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → ∫ ω, D j ω * D' k ω ∂P = 0 := by
    intro j hj k hk hjk
    have hj' := Finset.mem_range.mp hj
    have hk' := Finset.mem_range.mp hk
    have hdisj : Disjoint
        (Finset.univ.filter (fun q : Fin (n 1) ⊕ (Fin (n 1) × Fin (n 0)) =>
          W5_DeepLearningTheory_owner q = ⟨j, hj'⟩))
        (Finset.univ.filter (fun q : Fin (n 1) ⊕ (Fin (n 1) × Fin (n 0)) =>
          W5_DeepLearningTheory_owner q = ⟨k, hk'⟩)) := by
      rw [Finset.disjoint_filter]
      intro q _ h1 h2
      apply hjk
      have := congrArg Fin.val (h1.symm.trans h2)
      simpa using this
    have hind := (W5_DeepLearningTheory_indepY hinit).indepFun_finset₀ _ _ hdisj
      (fun q => (W5_DeepLearningTheory_L_gfacts (W5_DeepLearningTheory_marg hinit q)).1)
    have hφm : Measurable (fun y => σ (W5_DeepLearningTheory_Gn ⟨j, hj'⟩ (x 0) y) *
        σ (W5_DeepLearningTheory_Gn ⟨j, hj'⟩ (x 1) y) - A01) :=
      ((hσm.comp (W5_DeepLearningTheory_Gn_meas _ (x 0))).mul
        (hσm.comp (W5_DeepLearningTheory_Gn_meas _ (x 1)))).sub measurable_const
    have hψm : Measurable (fun y => σ (W5_DeepLearningTheory_Gn ⟨k, hk'⟩ (x 2) y) *
        σ (W5_DeepLearningTheory_Gn ⟨k, hk'⟩ (x 3) y) - A23) :=
      ((hσm.comp (W5_DeepLearningTheory_Gn_meas _ (x 2))).mul
        (hσm.comp (W5_DeepLearningTheory_Gn_meas _ (x 3)))).sub measurable_const
    have hAm : ∀ (S : Finset (Fin (n 1) ⊕ (Fin (n 1) × Fin (n 0)))),
        AEMeasurable (fun ω (q : S) => W5_DeepLearningTheory_Yv (n := n) b W q.1 ω) P :=
      fun S => aemeasurable_pi_lambda _ fun q =>
        (W5_DeepLearningTheory_L_gfacts (W5_DeepLearningTheory_marg hinit q.1)).1
    have key := (hind.comp hφm hψm).integral_fun_mul_eq_mul_integral
      (hφm.comp_aemeasurable (hAm _)).aestronglyMeasurable
      (hψm.comp_aemeasurable (hAm _)).aestronglyMeasurable
    simp only [Function.comp_apply] at key
    have eD : ∀ ω, D j ω * D' k ω =
        (σ (W5_DeepLearningTheory_Gn ⟨j, hj'⟩ (x 0)
            (fun q => W5_DeepLearningTheory_Yv (n := n) b W q.1 ω)) *
          σ (W5_DeepLearningTheory_Gn ⟨j, hj'⟩ (x 1)
            (fun q => W5_DeepLearningTheory_Yv (n := n) b W q.1 ω)) - A01) *
        (σ (W5_DeepLearningTheory_Gn ⟨k, hk'⟩ (x 2)
            (fun q => W5_DeepLearningTheory_Yv (n := n) b W q.1 ω)) *
          σ (W5_DeepLearningTheory_Gn ⟨k, hk'⟩ (x 3)
            (fun q => W5_DeepLearningTheory_Yv (n := n) b W q.1 ω)) - A23) := by
      intro ω
      simp only [hD, hD', W5_DeepLearningTheory_Gn_eq σ b W j hj', W5_DeepLearningTheory_Gn_eq σ b W k hk']
    simp_rw [eD]
    rw [key]
    have m1 := hmean j hj
    simp only [hD, W5_DeepLearningTheory_Gn_eq σ b W j hj'] at m1
    rw [m1, zero_mul]
  -- diagonal terms
  have hdiag : ∀ j ∈ s, ∫ ω, D j ω * D' j ω ∂P = A4 - A01 * A23 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have f01 := W5_DeepLearningTheory_avg_neuron (σ := σ) hinit x j hj'
      (fun u => σ (u 0) * σ (u 1)) (by fun_prop)
    have f23 := W5_DeepLearningTheory_avg_neuron (σ := σ) hinit x j hj'
      (fun u => σ (u 2) * σ (u 3)) (by fun_prop)
    have f4 := W5_DeepLearningTheory_avg_neuron (σ := σ) hinit x j hj'
      (fun u => σ (u 0) * σ (u 1) * σ (u 2) * σ (u 3)) (by fun_prop)
    simp only at f01 f23 f4
    have i01 := W5_DeepLearningTheory_AM_int (W5_DeepLearningTheory_AM_mul
      (hAMs (x 0) j hj') (hAMs (x 1) j hj'))
    have i23 := W5_DeepLearningTheory_AM_int (W5_DeepLearningTheory_AM_mul
      (hAMs (x 2) j hj') (hAMs (x 3) j hj'))
    have i4 := W5_DeepLearningTheory_AM_int (W5_DeepLearningTheory_AM_mul
      (W5_DeepLearningTheory_AM_mul (W5_DeepLearningTheory_AM_mul
        (hAMs (x 0) j hj') (hAMs (x 1) j hj')) (hAMs (x 2) j hj')) (hAMs (x 3) j hj'))
    have eD : ∀ ω, D j ω * D' j ω =
        σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j) *
          σ (mlpPreact n σ (b ω) (W ω) (x 2) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 3) 1 j)
        - A23 * (σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j))
        - A01 * (σ (mlpPreact n σ (b ω) (W ω) (x 2) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 3) 1 j))
        + A01 * A23 := by
      intro ω
      simp only [hD, hD']
      ring
    simp_rw [eD]
    have i2 := i01.const_mul A23
    have i3 := i23.const_mul A01
    have j12 : Integrable (fun ω => σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) *
        σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 2) 1 j) *
        σ (mlpPreact n σ (b ω) (W ω) (x 3) 1 j) - A23 * (σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) *
        σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j))) P := i4.sub i2
    have j123 : Integrable (fun ω => σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) *
        σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 2) 1 j) *
        σ (mlpPreact n σ (b ω) (W ω) (x 3) 1 j) - A23 * (σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) *
        σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j)) - A01 * (σ (mlpPreact n σ (b ω) (W ω) (x 2) 1 j) *
        σ (mlpPreact n σ (b ω) (W ω) (x 3) 1 j))) P := j12.sub i3
    rw [integral_add j123 (integrable_const _), integral_sub j12 i3, integral_sub i4 i2,
      integral_const_mul, integral_const_mul, integral_const, f4, f01, f23]
    simp
    ring
  -- assemble
  have hrow : ∀ j ∈ s, ∑ k ∈ s, c ^ 2 * ∫ ω, D j ω * D' k ω ∂P = c ^ 2 * (A4 - A01 * A23) := by
    intro j hj
    rw [Finset.sum_eq_single j (fun k hk hkj => by rw [hoff j hj k hk (Ne.symm hkj), mul_zero])
      (fun h => absurd hj h), hdiag j hj]
  simp only [hD, hD'] at hrow
  rw [Finset.sum_congr rfl hrow, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn : (n 1 : ℝ) ≠ 0 := by exact_mod_cast hn₁.ne'
  simp only [hc]
  field_simp
  try ring

/-! ### Second layer -/

/-- Second-layer parameter index: biases `b^{(2)}_i` and weights `W^{(2)}_{ij}`. -/
def W5_DeepLearningTheory_g2idx (n : ℕ → ℕ) :
    Fin (n 2) ⊕ (Fin (n 2) × Fin (n 1)) → BiasIndex n ⊕ WeightIndex n
  | Sum.inl i => Sum.inl (Subtype.mk (2, (i : ℕ)) ⟨by norm_num, i.2⟩ :
      {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.2 < n p.1})
  | Sum.inr p => Sum.inr (Subtype.mk (2, (p.1 : ℕ), (p.2 : ℕ)) ⟨by norm_num, p.1.2, p.2.2⟩ :
      {q : ℕ × ℕ × ℕ // 1 ≤ q.1 ∧ q.2.1 < n q.1 ∧ q.2.2 < n (q.1 - 1)})

theorem W5_DeepLearningTheory_g2idx_inj (n : ℕ → ℕ) :
    Function.Injective (W5_DeepLearningTheory_g2idx n) := by
  intro a b h
  rcases a with i | ⟨i, j⟩ <;> rcases b with i' | ⟨i', j'⟩ <;>
    simp only [W5_DeepLearningTheory_g2idx] at h
  · have h2 := congrArg Subtype.val (Sum.inl_injective h)
    simp only [Prod.mk.injEq, true_and] at h2
    exact congrArg Sum.inl (Fin.ext h2)
  · exact absurd h Sum.inl_ne_inr
  · exact absurd h Sum.inr_ne_inl
  · have h2 := congrArg Subtype.val (Sum.inr_injective h)
    simp only [Prod.mk.injEq, true_and] at h2
    rw [Fin.ext h2.1, Fin.ext h2.2]

/-- The parameter family of an MLP initialization. -/
def W5_DeepLearningTheory_XX {Ω : Type*} {n : ℕ → ℕ} (b : Ω → ℕ → ℕ → ℝ)
    (W : Ω → ℕ → ℕ → ℕ → ℝ) : BiasIndex n ⊕ WeightIndex n → Ω → ℝ :=
  fun p => Sum.elim (fun q (ω : Ω) => b ω q.1.1 q.1.2)
    (fun q (ω : Ω) => W ω q.1.1 q.1.2.1 q.1.2.2) p

noncomputable def W5_DeepLearningTheory_S1 (n : ℕ → ℕ) : Finset (BiasIndex n ⊕ WeightIndex n) :=
  Finset.univ.map ⟨W5_DeepLearningTheory_gidx n, W5_DeepLearningTheory_gidx_inj n⟩

noncomputable def W5_DeepLearningTheory_T2 (n : ℕ → ℕ) : Finset (BiasIndex n ⊕ WeightIndex n) :=
  Finset.univ.map ⟨W5_DeepLearningTheory_g2idx n, W5_DeepLearningTheory_g2idx_inj n⟩

theorem W5_DeepLearningTheory_disj12 (n : ℕ → ℕ) :
    Disjoint (W5_DeepLearningTheory_S1 n) (W5_DeepLearningTheory_T2 n) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  obtain ⟨k, -, rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨k', -, hk'⟩ := Finset.mem_map.mp hb
  rcases k with i | ⟨i, j⟩ <;> rcases k' with i' | ⟨i', j'⟩ <;>
    simp only [W5_DeepLearningTheory_gidx, W5_DeepLearningTheory_g2idx,
      Function.Embedding.coeFn_mk] at hk'
  all_goals first
    | exact absurd hk' Sum.inl_ne_inr
    | exact absurd hk' Sum.inr_ne_inl
    | (have h2 := congrArg Subtype.val (Sum.inl_injective hk'); simp at h2)
    | (have h2 := congrArg Subtype.val (Sum.inr_injective hk'); simp at h2)

theorem W5_DeepLearningTheory_memS1 {n : ℕ → ℕ} (k : Fin (n 1) ⊕ (Fin (n 1) × Fin (n 0))) :
    W5_DeepLearningTheory_gidx n k ∈ W5_DeepLearningTheory_S1 n :=
  Finset.mem_map_of_mem ⟨W5_DeepLearningTheory_gidx n, W5_DeepLearningTheory_gidx_inj n⟩
    (Finset.mem_univ k)

theorem W5_DeepLearningTheory_memT2 {n : ℕ → ℕ} (k : Fin (n 2) ⊕ (Fin (n 2) × Fin (n 1))) :
    W5_DeepLearningTheory_g2idx n k ∈ W5_DeepLearningTheory_T2 n :=
  Finset.mem_map_of_mem ⟨W5_DeepLearningTheory_g2idx n, W5_DeepLearningTheory_g2idx_inj n⟩
    (Finset.mem_univ k)

/-- A first-layer preactivation as a function of the first-layer parameter tuple. -/
noncomputable def W5_DeepLearningTheory_H {n : ℕ → ℕ} (j : Fin (n 1)) (x : ℕ → ℝ)
    (y : W5_DeepLearningTheory_S1 n → ℝ) : ℝ :=
  y ⟨_, W5_DeepLearningTheory_memS1 (Sum.inl j)⟩ +
    ∑ l : Fin (n 0), y ⟨_, W5_DeepLearningTheory_memS1 (Sum.inr (j, l))⟩ * x l

theorem W5_DeepLearningTheory_H_meas {n : ℕ → ℕ} (j : Fin (n 1)) (x : ℕ → ℝ) :
    Measurable (W5_DeepLearningTheory_H (n := n) j x) := by
  unfold W5_DeepLearningTheory_H
  fun_prop

theorem W5_DeepLearningTheory_H_eq {Ω : Type*} {n : ℕ → ℕ} (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (j : ℕ) (hj : j < n 1) (x : ℕ → ℝ) (ω : Ω) :
    mlpPreact n σ (b ω) (W ω) x 1 j =
      W5_DeepLearningTheory_H ⟨j, hj⟩ x
        (fun q => W5_DeepLearningTheory_XX (n := n) b W q.1 ω) := by
  have e1 : mlpPreact n σ (b ω) (W ω) x 1 j =
      b ω 1 j + ∑ l : Fin (n 0), W ω 1 j l * x l := by
    simp [mlpPreact, Finset.sum_range]
  rw [e1]
  rfl

theorem W5_DeepLearningTheory_factor12 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ → ℕ} {Cb CW : ℕ → ℝ≥0}
    {b : Ω → ℕ → ℕ → ℝ} {W : Ω → ℕ → ℕ → ℕ → ℝ} (hinit : IsMLPInit P n Cb CW b W)
    (Φ : (W5_DeepLearningTheory_T2 n → ℝ) → ℝ) (Ψ : (W5_DeepLearningTheory_S1 n → ℝ) → ℝ)
    (hΦ : Measurable Φ) (hΨ : Measurable Ψ) :
    ∫ ω, Φ (fun q => W5_DeepLearningTheory_XX (n := n) b W q.1 ω) *
        Ψ (fun q => W5_DeepLearningTheory_XX (n := n) b W q.1 ω) ∂P =
      (∫ ω, Φ (fun q => W5_DeepLearningTheory_XX (n := n) b W q.1 ω) ∂P) *
        ∫ ω, Ψ (fun q => W5_DeepLearningTheory_XX (n := n) b W q.1 ω) ∂P := by
  have hae : ∀ p, AEMeasurable (W5_DeepLearningTheory_XX (n := n) b W p) P := by
    intro p
    rcases p with q | q
    · exact (W5_DeepLearningTheory_L_gfacts (hinit.2.1 _ _ q.2.1 q.2.2)).1
    · exact (W5_DeepLearningTheory_L_gfacts (hinit.2.2 _ _ _ q.2.1 q.2.2.1 q.2.2.2)).1
  have hi : iIndepFun (W5_DeepLearningTheory_XX (n := n) b W) P := hinit.1
  have hind := hi.indepFun_finset₀ _ _ (W5_DeepLearningTheory_disj12 n) hae
  have hA : ∀ (S : Finset (BiasIndex n ⊕ WeightIndex n)),
      AEMeasurable (fun ω (q : S) => W5_DeepLearningTheory_XX (n := n) b W q.1 ω) P :=
    fun S => aemeasurable_pi_lambda _ fun q => hae q.1
  have key := (hind.comp hΨ hΦ).symm.integral_fun_mul_eq_mul_integral
    (hΦ.comp_aemeasurable (hA _)).aestronglyMeasurable
    (hΨ.comp_aemeasurable (hA _)).aestronglyMeasurable
  simp only [Function.comp_apply] at key
  exact key

theorem W5_DeepLearningTheory_P_indep_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f g : Ω → ℝ} {v w : ℝ≥0} (hf : P.map f = gaussianReal 0 v)
    (hg : P.map g = gaussianReal 0 w) (hfg : IndepFun f g P) :
    ∫ ω, f ω * g ω ∂P = 0 := by
  obtain ⟨hf1, -, hf3, -⟩ := W5_DeepLearningTheory_L_gfacts hf
  obtain ⟨hg1, -, -, -⟩ := W5_DeepLearningTheory_L_gfacts hg
  rw [hfg.integral_fun_mul_eq_mul_integral hf1.aestronglyMeasurable hg1.aestronglyMeasurable,
    hf3, zero_mul]

theorem W5_DeepLearningTheory_P_bb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ → ℕ} {Cb CW : ℕ → ℝ≥0}
    {b : Ω → ℕ → ℕ → ℝ} {W : Ω → ℕ → ℕ → ℕ → ℝ} (hinit : IsMLPInit P n Cb CW b W)
    {ℓ i i' : ℕ} (h1 : 1 ≤ ℓ) (hi : i < n ℓ) (hi' : i' < n ℓ) :
    ∫ ω, b ω ℓ i * b ω ℓ i' ∂P = if i = i' then (Cb ℓ : ℝ) else 0 := by
  split_ifs with h
  · subst h
    exact (W5_DeepLearningTheory_L_gfacts (hinit.2.1 ℓ i h1 hi)).2.2.2
  · apply W5_DeepLearningTheory_P_indep_zero (hinit.2.1 ℓ i h1 hi) (hinit.2.1 ℓ i' h1 hi')
    have hne : (Sum.inl (Subtype.mk (ℓ, i) ⟨h1, hi⟩ : {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.2 < n p.1}) :
        BiasIndex n ⊕ WeightIndex n) ≠
        Sum.inl (Subtype.mk (ℓ, i') ⟨h1, hi'⟩ : {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.2 < n p.1}) := by
      intro heq
      apply h
      have h2 := congrArg Subtype.val (Sum.inl_injective heq)
      simp only [Prod.mk.injEq, true_and] at h2
      exact h2
    exact hinit.1.indepFun hne

theorem W5_DeepLearningTheory_P_bW {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ → ℕ} {Cb CW : ℕ → ℝ≥0}
    {b : Ω → ℕ → ℕ → ℝ} {W : Ω → ℕ → ℕ → ℕ → ℝ} (hinit : IsMLPInit P n Cb CW b W)
    {ℓ i ℓ' i' j' : ℕ} (h1 : 1 ≤ ℓ) (hi : i < n ℓ) (h1' : 1 ≤ ℓ') (hi' : i' < n ℓ')
    (hj' : j' < n (ℓ' - 1)) :
    ∫ ω, b ω ℓ i * W ω ℓ' i' j' ∂P = 0 := by
  apply W5_DeepLearningTheory_P_indep_zero (hinit.2.1 ℓ i h1 hi) (hinit.2.2 ℓ' i' j' h1' hi' hj')
  have hne : (Sum.inl (Subtype.mk (ℓ, i) ⟨h1, hi⟩ : {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.2 < n p.1}) :
      BiasIndex n ⊕ WeightIndex n) ≠
      Sum.inr (Subtype.mk (ℓ', i', j') ⟨h1', hi', hj'⟩ :
        {p : ℕ × ℕ × ℕ // 1 ≤ p.1 ∧ p.2.1 < n p.1 ∧ p.2.2 < n (p.1 - 1)}) := Sum.inl_ne_inr
  exact hinit.1.indepFun hne

theorem W5_DeepLearningTheory_P_WW {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ → ℕ} {Cb CW : ℕ → ℝ≥0}
    {b : Ω → ℕ → ℕ → ℝ} {W : Ω → ℕ → ℕ → ℕ → ℝ} (hinit : IsMLPInit P n Cb CW b W)
    {ℓ i j i' j' : ℕ} (h1 : 1 ≤ ℓ) (hi : i < n ℓ) (hj : j < n (ℓ - 1))
    (hi' : i' < n ℓ) (hj' : j' < n (ℓ - 1)) :
    ∫ ω, W ω ℓ i j * W ω ℓ i' j' ∂P =
      if i = i' ∧ j = j' then ((CW ℓ / (n (ℓ - 1) : ℝ≥0) : ℝ≥0) : ℝ) else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact (W5_DeepLearningTheory_L_gfacts (hinit.2.2 ℓ i j h1 hi hj)).2.2.2
  · apply W5_DeepLearningTheory_P_indep_zero (hinit.2.2 ℓ i j h1 hi hj)
      (hinit.2.2 ℓ i' j' h1 hi' hj')
    have hne : (Sum.inr (Subtype.mk (ℓ, i, j) ⟨h1, hi, hj⟩ :
        {p : ℕ × ℕ × ℕ // 1 ≤ p.1 ∧ p.2.1 < n p.1 ∧ p.2.2 < n (p.1 - 1)}) :
        BiasIndex n ⊕ WeightIndex n) ≠
        Sum.inr (Subtype.mk (ℓ, i', j') ⟨h1, hi', hj'⟩ :
          {p : ℕ × ℕ × ℕ // 1 ≤ p.1 ∧ p.2.1 < n p.1 ∧ p.2.2 < n (p.1 - 1)}) := by
      intro heq
      apply h
      have h2 := congrArg Subtype.val (Sum.inr_injective heq)
      simp only [Prod.mk.injEq, true_and] at h2
      exact h2
    exact hinit.1.indepFun hne

theorem W5_DeepLearningTheory_mlp_second_layer_two_point {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    (hσm : Measurable σ) (hσ : HasPolyGrowth σ) (hn₁ : 0 < n 1) (x : Fin 2 → ℕ → ℝ) (i₁ i₂ : ℕ) (hi₁ : i₁ < n 2) (hi₂ : i₂ < n 2) :
    ∫ ω, mlpPreact n σ (b ω) (W ω) (x 0) 2 i₁ * mlpPreact n σ (b ω) (W ω) (x 1) 2 i₂ ∂P
      = kron i₁ i₂ * ((Cb 2 : ℝ) + (CW 2 : ℝ) *
          gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 0) * σ (u 1))) := by
  set s := Finset.range (n 1) with hs
  set A := gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 0) * σ (u 1)) with hA
  have hAMs : ∀ (y : ℕ → ℝ) (j : ℕ), j < n 1 →
      W5_DeepLearningTheory_AM P (fun ω => σ (mlpPreact n σ (b ω) (W ω) y 1 j)) :=
    fun y j hj => W5_DeepLearningTheory_AM_poly hσm hσ (W5_DeepLearningTheory_AMz1 hinit y j hj)
  have hz : ∀ (ω : Ω) (y : ℕ → ℝ) (i : ℕ), mlpPreact n σ (b ω) (W ω) y 2 i =
      ∑ o ∈ Finset.insertNone s,
        Option.elim o (b ω 2 i) (fun j => W ω 2 i j * σ (mlpPreact n σ (b ω) (W ω) y 1 j)) := by
    intro ω y i
    rw [Finset.sum_insertNone]
    rfl
  simp_rw [hz]
  have hmem : ∀ (y : ℕ → ℝ) (i : ℕ), i < n 2 → ∀ o ∈ Finset.insertNone s,
      MemLp (fun ω => Option.elim o (b ω 2 i)
        (fun j => W ω 2 i j * σ (mlpPreact n σ (b ω) (W ω) y 1 j))) 2 P := by
    intro y i hi o ho
    cases o with
    | none => exact (W5_DeepLearningTheory_L_gfacts (hinit.2.1 2 i (by norm_num) hi)).2.1
    | some j =>
      have hj : j < n 1 := by simpa [hs] using ho
      exact W5_DeepLearningTheory_AM_mul
        (W5_DeepLearningTheory_AM_gauss (hinit.2.2 2 i j (by norm_num) hi hj))
        (hAMs y j hj) 2 (by norm_num)
  have hB : ∫ ω, (∑ o ∈ Finset.insertNone s, Option.elim o (b ω 2 i₁)
        (fun j => W ω 2 i₁ j * σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j))) *
      (∑ o ∈ Finset.insertNone s, Option.elim o (b ω 2 i₂)
        (fun j => W ω 2 i₂ j * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j))) ∂P =
      ∑ o ∈ Finset.insertNone s, ∑ o' ∈ Finset.insertNone s,
        ∫ ω, Option.elim o (b ω 2 i₁)
            (fun j => W ω 2 i₁ j * σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j)) *
          Option.elim o' (b ω 2 i₂)
            (fun j => W ω 2 i₂ j * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j)) ∂P := by
    simp_rw [Finset.sum_mul_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun o ho => ?_
      rw [integral_finsetSum]
      intro o' ho'
      exact (hmem (x 0) i₁ hi₁ o ho).integrable_mul (hmem (x 1) i₂ hi₂ o' ho')
    · intro o ho
      exact integrable_finsetSum _ fun o' ho' =>
        (hmem (x 0) i₁ hi₁ o ho).integrable_mul (hmem (x 1) i₂ hi₂ o' ho')
  rw [hB]
  simp only [Finset.sum_insertNone, Option.elim]
  -- the four kinds of terms
  have hbb := W5_DeepLearningTheory_P_bb hinit (ℓ := 2) (by norm_num) hi₁ hi₂
  have hbW : ∀ k ∈ s, ∫ ω, b ω 2 i₁ *
      (W ω 2 i₂ k * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 k)) ∂P = 0 := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have key : ∫ ω, b ω 2 i₁ * W ω 2 i₂ k * σ (W5_DeepLearningTheory_H ⟨k, hk'⟩ (x 1)
          (fun q => W5_DeepLearningTheory_XX (n := n) b W q.1 ω)) ∂P =
        (∫ ω, b ω 2 i₁ * W ω 2 i₂ k ∂P) * ∫ ω, σ (W5_DeepLearningTheory_H ⟨k, hk'⟩ (x 1)
          (fun q => W5_DeepLearningTheory_XX (n := n) b W q.1 ω)) ∂P :=
      W5_DeepLearningTheory_factor12 hinit
        (fun v => v ⟨_, W5_DeepLearningTheory_memT2 (Sum.inl ⟨i₁, hi₁⟩)⟩ *
          v ⟨_, W5_DeepLearningTheory_memT2 (Sum.inr (⟨i₂, hi₂⟩, ⟨k, hk'⟩))⟩)
        (fun y => σ (W5_DeepLearningTheory_H ⟨k, hk'⟩ (x 1) y)) (by fun_prop)
        (hσm.comp (W5_DeepLearningTheory_H_meas _ _))
    have e : ∀ ω, b ω 2 i₁ * (W ω 2 i₂ k * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 k)) =
        b ω 2 i₁ * W ω 2 i₂ k * σ (W5_DeepLearningTheory_H ⟨k, hk'⟩ (x 1)
          (fun q => W5_DeepLearningTheory_XX (n := n) b W q.1 ω)) := by
      intro ω
      rw [W5_DeepLearningTheory_H_eq σ b W k hk' (x 1) ω]
      ring
    simp_rw [e]
    rw [key, W5_DeepLearningTheory_P_bW hinit (ℓ := 2) (ℓ' := 2) (by norm_num) hi₁ (by norm_num)
      hi₂ hk', zero_mul]
  have hWb : ∀ j ∈ s, ∫ ω, W ω 2 i₁ j * σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) *
      b ω 2 i₂ ∂P = 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have key : ∫ ω, b ω 2 i₂ * W ω 2 i₁ j * σ (W5_DeepLearningTheory_H ⟨j, hj'⟩ (x 0)
          (fun q => W5_DeepLearningTheory_XX (n := n) b W q.1 ω)) ∂P =
        (∫ ω, b ω 2 i₂ * W ω 2 i₁ j ∂P) * ∫ ω, σ (W5_DeepLearningTheory_H ⟨j, hj'⟩ (x 0)
          (fun q => W5_DeepLearningTheory_XX (n := n) b W q.1 ω)) ∂P :=
      W5_DeepLearningTheory_factor12 hinit
        (fun v => v ⟨_, W5_DeepLearningTheory_memT2 (Sum.inl ⟨i₂, hi₂⟩)⟩ *
          v ⟨_, W5_DeepLearningTheory_memT2 (Sum.inr (⟨i₁, hi₁⟩, ⟨j, hj'⟩))⟩)
        (fun y => σ (W5_DeepLearningTheory_H ⟨j, hj'⟩ (x 0) y)) (by fun_prop)
        (hσm.comp (W5_DeepLearningTheory_H_meas _ _))
    have e : ∀ ω, W ω 2 i₁ j * σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) * b ω 2 i₂ =
        b ω 2 i₂ * W ω 2 i₁ j * σ (W5_DeepLearningTheory_H ⟨j, hj'⟩ (x 0)
          (fun q => W5_DeepLearningTheory_XX (n := n) b W q.1 ω)) := by
      intro ω
      rw [W5_DeepLearningTheory_H_eq σ b W j hj' (x 0) ω]
      ring
    simp_rw [e]
    rw [key, W5_DeepLearningTheory_P_bW hinit (ℓ := 2) (ℓ' := 2) (by norm_num) hi₂ (by norm_num)
      hi₁ hj', zero_mul]
  have hWW : ∀ j ∈ s, ∀ k ∈ s, ∫ ω, W ω 2 i₁ j * σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) *
      (W ω 2 i₂ k * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 k)) ∂P =
      (if i₁ = i₂ ∧ j = k then ((CW 2 / (n (2 - 1) : ℝ≥0) : ℝ≥0) : ℝ) else 0) *
        ∫ ω, σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) *
          σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 k) ∂P := by
    intro j hj k hk
    have hj' := Finset.mem_range.mp hj
    have hk' := Finset.mem_range.mp hk
    have key : ∫ ω, W ω 2 i₁ j * W ω 2 i₂ k * (σ (W5_DeepLearningTheory_H ⟨j, hj'⟩ (x 0)
          (fun q => W5_DeepLearningTheory_XX (n := n) b W q.1 ω)) *
          σ (W5_DeepLearningTheory_H ⟨k, hk'⟩ (x 1)
          (fun q => W5_DeepLearningTheory_XX (n := n) b W q.1 ω))) ∂P =
        (∫ ω, W ω 2 i₁ j * W ω 2 i₂ k ∂P) * ∫ ω, σ (W5_DeepLearningTheory_H ⟨j, hj'⟩ (x 0)
          (fun q => W5_DeepLearningTheory_XX (n := n) b W q.1 ω)) *
          σ (W5_DeepLearningTheory_H ⟨k, hk'⟩ (x 1)
          (fun q => W5_DeepLearningTheory_XX (n := n) b W q.1 ω)) ∂P :=
      W5_DeepLearningTheory_factor12 hinit
        (fun v => v ⟨_, W5_DeepLearningTheory_memT2 (Sum.inr (⟨i₁, hi₁⟩, ⟨j, hj'⟩))⟩ *
          v ⟨_, W5_DeepLearningTheory_memT2 (Sum.inr (⟨i₂, hi₂⟩, ⟨k, hk'⟩))⟩)
        (fun y => σ (W5_DeepLearningTheory_H ⟨j, hj'⟩ (x 0) y) *
          σ (W5_DeepLearningTheory_H ⟨k, hk'⟩ (x 1) y)) (by fun_prop)
        (by
          have h1 := hσm.comp (W5_DeepLearningTheory_H_meas (n := n) ⟨j, hj'⟩ (x 0))
          have h2 := hσm.comp (W5_DeepLearningTheory_H_meas (n := n) ⟨k, hk'⟩ (x 1))
          exact h1.mul h2)
    have e : ∀ ω, W ω 2 i₁ j * σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) *
        (W ω 2 i₂ k * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 k)) =
        W ω 2 i₁ j * W ω 2 i₂ k * (σ (W5_DeepLearningTheory_H ⟨j, hj'⟩ (x 0)
          (fun q => W5_DeepLearningTheory_XX (n := n) b W q.1 ω)) *
          σ (W5_DeepLearningTheory_H ⟨k, hk'⟩ (x 1)
          (fun q => W5_DeepLearningTheory_XX (n := n) b W q.1 ω))) := by
      intro ω
      rw [W5_DeepLearningTheory_H_eq σ b W j hj' (x 0) ω,
        W5_DeepLearningTheory_H_eq σ b W k hk' (x 1) ω]
      ring
    simp_rw [e]
    rw [key, W5_DeepLearningTheory_P_WW hinit (ℓ := 2) (by norm_num) hi₁ hj' hi₂ hk']
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    try simp only
    rw [W5_DeepLearningTheory_H_eq σ b W j hj' (x 0) ω,
      W5_DeepLearningTheory_H_eq σ b W k hk' (x 1) ω]
  rw [hbb, Finset.sum_eq_zero hbW, Finset.sum_add_distrib, Finset.sum_eq_zero hWb,
    Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => hWW j hj k hk]
  have hdiag : ∀ j ∈ s, ∫ ω, σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) *
      σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j) ∂P = A := by
    intro j hj
    exact W5_DeepLearningTheory_avg_neuron (σ := σ) hinit x j (Finset.mem_range.mp hj)
      (fun u => σ (u 0) * σ (u 1)) (by fun_prop)
  have hrow : ∀ j ∈ s, ∑ k ∈ s, (if i₁ = i₂ ∧ j = k then ((CW 2 / (n (2 - 1) : ℝ≥0) : ℝ≥0) : ℝ)
      else 0) * ∫ ω, σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) *
        σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 k) ∂P =
      kron i₁ i₂ * (((CW 2 / (n 1 : ℝ≥0) : ℝ≥0) : ℝ) * A) := by
    intro j hj
    rw [Finset.sum_eq_single j (fun k _ hkj => by simp [Ne.symm hkj]) (fun h => absurd hj h),
      hdiag j hj]
    unfold kron
    by_cases h : i₁ = i₂ <;> simp [h]
  rw [Finset.sum_congr rfl hrow, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn : (n 1 : ℝ) ≠ 0 := by exact_mod_cast hn₁.ne'
  unfold kron
  by_cases h : i₁ = i₂
  · simp only [h, if_true, one_mul, add_zero, zero_add, NNReal.coe_div, NNReal.coe_natCast]
    field_simp
  · simp [h]
