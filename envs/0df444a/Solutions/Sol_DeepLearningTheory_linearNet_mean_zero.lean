-- Prove2me | solution 1 for DeepLearningTheory.linearNet_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T01:06:48.65098+00:00
-- url     : https://prove2.me/submissions/3f159aea-05a1-4dfe-98da-bc7ef23b8925

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open DeepLearningTheory

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

theorem W5_DeepLearningTheory_N_gfacts {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
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
  have hf := (W5_DeepLearningTheory_N_gfacts h).1
  have h3 := memLp_id_gaussianReal' (μ := 0) (v := v) p hp
  rw [← h] at h3
  exact (memLp_map_measure_iff aestronglyMeasurable_id hf).1 h3

theorem W5_DeepLearningTheory_AM_int {f : Ω → ℝ} (hf : W5_DeepLearningTheory_AM P f) :
    Integrable f P :=
  (hf 1 ENNReal.one_ne_top).integrable le_rfl

end AM

/-! ### Index sets of weights -/

def W5_DeepLearningTheory_Bw (n : ℕ → ℕ) (ℓ : ℕ) : ℕ := ∑ m ∈ Finset.range (ℓ + 2), n m

theorem W5_DeepLearningTheory_le_Bw (n : ℕ → ℕ) (ℓ m : ℕ) (hm : m ≤ ℓ + 1) :
    n m ≤ W5_DeepLearningTheory_Bw n ℓ :=
  Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))

def W5_DeepLearningTheory_Sset (n : ℕ → ℕ) (ℓ : ℕ) : Finset (WeightIndex n) :=
  (((Finset.range (ℓ + 1)) ×ˢ ((Finset.range (W5_DeepLearningTheory_Bw n ℓ)) ×ˢ
    (Finset.range (W5_DeepLearningTheory_Bw n ℓ)))).subtype
    (fun p : ℕ × ℕ × ℕ => 1 ≤ p.1 ∧ p.2.1 < n p.1 ∧ p.2.2 < n (p.1 - 1)) :
    Finset {p : ℕ × ℕ × ℕ // 1 ≤ p.1 ∧ p.2.1 < n p.1 ∧ p.2.2 < n (p.1 - 1)})

def W5_DeepLearningTheory_Tset (n : ℕ → ℕ) (ℓ : ℕ) : Finset (WeightIndex n) :=
  ((({ℓ + 1} : Finset ℕ) ×ˢ ((Finset.range (W5_DeepLearningTheory_Bw n ℓ)) ×ˢ
    (Finset.range (W5_DeepLearningTheory_Bw n ℓ)))).subtype
    (fun p : ℕ × ℕ × ℕ => 1 ≤ p.1 ∧ p.2.1 < n p.1 ∧ p.2.2 < n (p.1 - 1)) :
    Finset {p : ℕ × ℕ × ℕ // 1 ≤ p.1 ∧ p.2.1 < n p.1 ∧ p.2.2 < n (p.1 - 1)})

theorem W5_DeepLearningTheory_memS {n : ℕ → ℕ} {ℓ m i k : ℕ}
    (h : 1 ≤ m ∧ i < n m ∧ k < n (m - 1)) (hm : m ≤ ℓ) :
    (Subtype.mk (m, i, k) h : WeightIndex n) ∈ W5_DeepLearningTheory_Sset n ℓ := by
  unfold W5_DeepLearningTheory_Sset
  refine Finset.mem_subtype.mpr ?_
  simp only [Finset.mem_product, Finset.mem_range]
  exact ⟨by omega, lt_of_lt_of_le h.2.1 (W5_DeepLearningTheory_le_Bw n ℓ m (by omega)),
    lt_of_lt_of_le h.2.2 (W5_DeepLearningTheory_le_Bw n ℓ (m - 1) (by omega))⟩

theorem W5_DeepLearningTheory_memT {n : ℕ → ℕ} {ℓ i k : ℕ}
    (h : 1 ≤ ℓ + 1 ∧ i < n (ℓ + 1) ∧ k < n (ℓ + 1 - 1)) :
    (Subtype.mk (ℓ + 1, i, k) h : WeightIndex n) ∈ W5_DeepLearningTheory_Tset n ℓ := by
  unfold W5_DeepLearningTheory_Tset
  refine Finset.mem_subtype.mpr ?_
  simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton]
  refine ⟨by simp, lt_of_lt_of_le h.2.1 (W5_DeepLearningTheory_le_Bw n ℓ (ℓ + 1) le_rfl),
    lt_of_lt_of_le h.2.2 (W5_DeepLearningTheory_le_Bw n ℓ (ℓ + 1 - 1) (by omega))⟩

theorem W5_DeepLearningTheory_disjST (n : ℕ → ℕ) (ℓ : ℕ) :
    Disjoint (W5_DeepLearningTheory_Sset n ℓ) (W5_DeepLearningTheory_Tset n ℓ) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  unfold W5_DeepLearningTheory_Sset at ha
  unfold W5_DeepLearningTheory_Tset at hb
  have ha' := Finset.mem_subtype.mp ha
  have hb' := Finset.mem_subtype.mp hb
  simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at ha' hb'
  omega

/-! ### Representation of the preactivations through earlier weights -/

noncomputable def W5_DeepLearningTheory_Wa {n : ℕ → ℕ} (ℓ : ℕ)
    (a : W5_DeepLearningTheory_Sset n ℓ → ℝ) (m i k : ℕ) : ℝ :=
  if h : (1 ≤ m ∧ i < n m ∧ k < n (m - 1)) ∧ m ≤ ℓ then
    a ⟨Subtype.mk (m, i, k) h.1, W5_DeepLearningTheory_memS h.1 h.2⟩
  else 0

theorem W5_DeepLearningTheory_rep {Ω : Type*} {n : ℕ → ℕ} (W : Ω → ℕ → ℕ → ℕ → ℝ)
    (x : ℕ → ℝ) (ℓ : ℕ) (ω : Ω) :
    ∀ m ≤ ℓ, ∀ j < n m, linearPreact n (W ω) x m j =
      linearPreact n (W5_DeepLearningTheory_Wa (n := n) ℓ
        (fun q => W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2)) x m j := by
  intro m
  induction m with
  | zero => intro _ j _; rfl
  | succ m ih =>
    intro hm j hj
    simp only [linearPreact]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [ih (by omega) k hk']
    congr 1
    rw [W5_DeepLearningTheory_Wa, dif_pos ⟨⟨by omega, hj, by simpa using hk'⟩, hm⟩]

theorem W5_DeepLearningTheory_Gmeas {n : ℕ → ℕ} (x : ℕ → ℝ) (ℓ : ℕ) :
    ∀ m j, Measurable (fun a : W5_DeepLearningTheory_Sset n ℓ → ℝ =>
      linearPreact n (W5_DeepLearningTheory_Wa ℓ a) x m j) := by
  intro m
  induction m with
  | zero => intro j; exact measurable_const
  | succ m ih =>
    intro j
    simp only [linearPreact]
    refine Finset.measurable_fun_sum _ fun k _ => ?_
    refine Measurable.mul ?_ (ih k)
    unfold W5_DeepLearningTheory_Wa
    split_ifs
    · exact measurable_pi_apply _
    · exact measurable_const

/-! ### Basic facts from the initialization -/

section Init
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n : ℕ → ℕ} {CW : ℝ≥0} {W : Ω → ℕ → ℕ → ℕ → ℝ}

theorem W5_DeepLearningTheory_waem (hW : IsLinearNetInit P n CW W) (p : WeightIndex n) :
    AEMeasurable (fun ω => W ω p.1.1 p.1.2.1 p.1.2.2) P :=
  (W5_DeepLearningTheory_N_gfacts (hW.2 _ _ _ p.2.1 p.2.2.1 p.2.2.2)).1

theorem W5_DeepLearningTheory_hind (hW : IsLinearNetInit P n CW W) (ℓ : ℕ) :
    IndepFun (fun ω (q : W5_DeepLearningTheory_Sset n ℓ) => W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2)
      (fun ω (q : W5_DeepLearningTheory_Tset n ℓ) => W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2) P :=
  hW.1.indepFun_finset₀ _ _ (W5_DeepLearningTheory_disjST n ℓ)
    (fun p => W5_DeepLearningTheory_waem hW p)

theorem W5_DeepLearningTheory_Aaem (hW : IsLinearNetInit P n CW W) (ℓ : ℕ) :
    AEMeasurable (fun ω (q : W5_DeepLearningTheory_Sset n ℓ) =>
      W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2) P :=
  aemeasurable_pi_lambda _ fun q => W5_DeepLearningTheory_waem hW q.1

theorem W5_DeepLearningTheory_Baem (hW : IsLinearNetInit P n CW W) (ℓ : ℕ) :
    AEMeasurable (fun ω (q : W5_DeepLearningTheory_Tset n ℓ) =>
      W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2) P :=
  aemeasurable_pi_lambda _ fun q => W5_DeepLearningTheory_waem hW q.1

/-- Factorization: a function of the next-layer weights times a function of the
earlier weights. -/
theorem W5_DeepLearningTheory_factor (hW : IsLinearNetInit P n CW W) (ℓ : ℕ)
    (Φ : (W5_DeepLearningTheory_Tset n ℓ → ℝ) → ℝ) (Ψ : (W5_DeepLearningTheory_Sset n ℓ → ℝ) → ℝ)
    (hΦ : Measurable Φ) (hΨ : Measurable Ψ) :
    ∫ ω, Φ (fun q => W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2) *
        Ψ (fun q => W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2) ∂P =
      (∫ ω, Φ (fun q => W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2) ∂P) *
        ∫ ω, Ψ (fun q => W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2) ∂P := by
  have key := ((W5_DeepLearningTheory_hind hW ℓ).comp hΨ hΦ).symm.integral_fun_mul_eq_mul_integral
    (hΦ.comp_aemeasurable (W5_DeepLearningTheory_Baem hW ℓ)).aestronglyMeasurable
    (hΨ.comp_aemeasurable (W5_DeepLearningTheory_Aaem hW ℓ)).aestronglyMeasurable
  simp only [Function.comp_apply] at key
  exact key

/-- A next-layer weight as a coordinate of the `T`-vector. -/
theorem W5_DeepLearningTheory_Wcoord (ℓ i k : ℕ) (hi : i < n (ℓ + 1)) (hk : k < n ℓ) (ω : Ω) :
    W ω (ℓ + 1) i k = (fun q : W5_DeepLearningTheory_Tset n ℓ => W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2)
      ⟨Subtype.mk (ℓ + 1, i, k) ⟨by omega, hi, by simpa using hk⟩,
        W5_DeepLearningTheory_memT ⟨by omega, hi, by simpa using hk⟩⟩ := rfl

theorem W5_DeepLearningTheory_AMz (hW : IsLinearNetInit P n CW W) (x : ℕ → ℝ) :
    ∀ ℓ, ∀ k < n ℓ, W5_DeepLearningTheory_AM P (fun ω => linearPreact n (W ω) x ℓ k) := by
  intro ℓ
  induction ℓ with
  | zero => intro k _; exact W5_DeepLearningTheory_AM_const (x k)
  | succ ℓ ih =>
    intro k hk
    simp only [linearPreact]
    refine W5_DeepLearningTheory_AM_sum _ fun j hj => ?_
    exact W5_DeepLearningTheory_AM_mul
      (W5_DeepLearningTheory_AM_gauss (hW.2 (ℓ + 1) k j (by omega) hk
        (by simpa using Finset.mem_range.mp hj)))
      (ih j (Finset.mem_range.mp hj))

theorem W5_DeepLearningTheory_WW (hW : IsLinearNetInit P n CW W) {ℓ i k i' k' : ℕ}
    (hi : i < n (ℓ + 1)) (hk : k < n ℓ) (hi' : i' < n (ℓ + 1)) (hk' : k' < n ℓ) :
    ∫ ω, W ω (ℓ + 1) i k * W ω (ℓ + 1) i' k' ∂P =
      if i = i' ∧ k = k' then ((CW / (n ℓ : ℝ≥0) : ℝ≥0) : ℝ) else 0 := by
  have hmk : ∀ i k, i < n (ℓ + 1) → k < n ℓ →
      P.map (fun ω => W ω (ℓ + 1) i k) = gaussianReal 0 (CW / (n ℓ : ℝ≥0)) :=
    fun i k hi hk => hW.2 (ℓ + 1) i k (by omega) hi (by simpa using hk)
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact (W5_DeepLearningTheory_N_gfacts (hmk i k hi hk)).2.2.2
  · have hne : (Subtype.mk (ℓ + 1, i, k) ⟨by omega, hi, by simpa using hk⟩ : WeightIndex n) ≠
        Subtype.mk (ℓ + 1, i', k') ⟨by omega, hi', by simpa using hk'⟩ := by
      intro heq
      apply h
      have h2 := congrArg Subtype.val heq
      simp only [Prod.mk.injEq, true_and] at h2
      exact h2
    have hind := hW.1.indepFun hne
    obtain ⟨hf1, -, hf3, -⟩ := W5_DeepLearningTheory_N_gfacts (hmk i k hi hk)
    obtain ⟨hg1, -, -, -⟩ := W5_DeepLearningTheory_N_gfacts (hmk i' k' hi' hk')
    rw [hind.integral_fun_mul_eq_mul_integral hf1.aestronglyMeasurable hg1.aestronglyMeasurable]
    rw [show (∫ ω, W ω (ℓ + 1) i k ∂P) = 0 from hf3, zero_mul]

theorem W5_DeepLearningTheory_Wmean (hW : IsLinearNetInit P n CW W) {ℓ i k : ℕ}
    (hi : i < n (ℓ + 1)) (hk : k < n ℓ) : ∫ ω, W ω (ℓ + 1) i k ∂P = 0 :=
  (W5_DeepLearningTheory_N_gfacts (hW.2 (ℓ + 1) i k (by omega) hi (by simpa using hk))).2.2.1

/-- One-step recursion for the mean. -/
theorem W5_DeepLearningTheory_R1 (hW : IsLinearNetInit P n CW W) (x : ℕ → ℝ) (ℓ i : ℕ)
    (hi : i < n (ℓ + 1)) : ∫ ω, linearPreact n (W ω) x (ℓ + 1) i ∂P = 0 := by
  simp only [linearPreact]
  rw [integral_finsetSum _ (fun k hk => W5_DeepLearningTheory_AM_int
    (W5_DeepLearningTheory_AM_mul
      (W5_DeepLearningTheory_AM_gauss (hW.2 (ℓ + 1) i k (by omega) hi
        (by simpa using Finset.mem_range.mp hk)))
      (W5_DeepLearningTheory_AMz hW x ℓ k (Finset.mem_range.mp hk))))]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have key := W5_DeepLearningTheory_factor hW ℓ
    (fun v : W5_DeepLearningTheory_Tset n ℓ → ℝ =>
        v ⟨Subtype.mk (ℓ + 1, i, k) ⟨by omega, hi, by simpa using hk'⟩,
          W5_DeepLearningTheory_memT ⟨by omega, hi, by simpa using hk'⟩⟩)
    (fun a : W5_DeepLearningTheory_Sset n ℓ → ℝ =>
        linearPreact n (W5_DeepLearningTheory_Wa ℓ a) x ℓ k)
    (measurable_pi_apply _) (W5_DeepLearningTheory_Gmeas x ℓ ℓ k)
  simp only at key
  have e : ∀ ω, W ω (ℓ + 1) i k * linearPreact n (W ω) x ℓ k =
      W ω (ℓ + 1) i k * linearPreact n (W5_DeepLearningTheory_Wa (n := n) ℓ
        (fun q => W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2)) x ℓ k := by
    intro ω
    rw [W5_DeepLearningTheory_rep W x ℓ ω ℓ le_rfl k hk']
  simp_rw [e]
  rw [key]
  rw [show (∫ ω, W ω (ℓ + 1) i k ∂P) = 0 from W5_DeepLearningTheory_Wmean hW hi hk', zero_mul]

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (CW : ℝ≥0) (W : Ω → ℕ → ℕ → ℕ → ℝ)
    (hW : IsLinearNetInit P n CW W) (x : ℕ → ℝ) (ℓ i : ℕ) (hℓ : 1 ≤ ℓ) (hi : i < n ℓ) :
    ∫ ω, linearPreact n (W ω) x ℓ i ∂P = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  exact W5_DeepLearningTheory_R1 hW x m i hi

/-- One-step recursion for the two-point function. -/
theorem W5_DeepLearningTheory_R2 (hW : IsLinearNetInit P n CW W) (x₁ x₂ : ℕ → ℝ) (ℓ i₁ i₂ : ℕ)
    (hi₁ : i₁ < n (ℓ + 1)) (hi₂ : i₂ < n (ℓ + 1)) :
    ∫ ω, linearPreact n (W ω) x₁ (ℓ + 1) i₁ * linearPreact n (W ω) x₂ (ℓ + 1) i₂ ∂P =
      kron i₁ i₂ * ((CW / (n ℓ : ℝ≥0) : ℝ≥0) : ℝ) *
        ∑ k ∈ Finset.range (n ℓ), ∫ ω, linearPreact n (W ω) x₁ ℓ k *
          linearPreact n (W ω) x₂ ℓ k ∂P := by
  simp only [linearPreact]
  simp_rw [Finset.sum_mul_sum]
  have hAMt : ∀ k ∈ Finset.range (n ℓ), ∀ k' ∈ Finset.range (n ℓ),
      W5_DeepLearningTheory_AM P (fun ω => W ω (ℓ + 1) i₁ k * linearPreact n (W ω) x₁ ℓ k *
        (W ω (ℓ + 1) i₂ k' * linearPreact n (W ω) x₂ ℓ k')) := by
    intro k hk k' hk'
    exact W5_DeepLearningTheory_AM_mul
      (W5_DeepLearningTheory_AM_mul
        (W5_DeepLearningTheory_AM_gauss (hW.2 (ℓ + 1) i₁ k (by omega) hi₁
          (by simpa using Finset.mem_range.mp hk)))
        (W5_DeepLearningTheory_AMz hW x₁ ℓ k (Finset.mem_range.mp hk)))
      (W5_DeepLearningTheory_AM_mul
        (W5_DeepLearningTheory_AM_gauss (hW.2 (ℓ + 1) i₂ k' (by omega) hi₂
          (by simpa using Finset.mem_range.mp hk')))
        (W5_DeepLearningTheory_AMz hW x₂ ℓ k' (Finset.mem_range.mp hk')))
  rw [integral_finsetSum _ (fun k hk => integrable_finsetSum _ fun k' hk' =>
    W5_DeepLearningTheory_AM_int (hAMt k hk k' hk'))]
  rw [Finset.sum_congr rfl fun k hk => integral_finsetSum _ fun k' hk' =>
    W5_DeepLearningTheory_AM_int (hAMt k hk k' hk')]
  have hterm : ∀ k ∈ Finset.range (n ℓ), ∀ k' ∈ Finset.range (n ℓ),
      ∫ ω, W ω (ℓ + 1) i₁ k * linearPreact n (W ω) x₁ ℓ k *
        (W ω (ℓ + 1) i₂ k' * linearPreact n (W ω) x₂ ℓ k') ∂P =
      (if i₁ = i₂ ∧ k = k' then ((CW / (n ℓ : ℝ≥0) : ℝ≥0) : ℝ) else 0) *
        ∫ ω, linearPreact n (W ω) x₁ ℓ k * linearPreact n (W ω) x₂ ℓ k' ∂P := by
    intro k hk k' hk'
    have hkl := Finset.mem_range.mp hk
    have hkl' := Finset.mem_range.mp hk'
    have key := W5_DeepLearningTheory_factor hW ℓ
      (fun v : W5_DeepLearningTheory_Tset n ℓ → ℝ =>
          v ⟨Subtype.mk (ℓ + 1, i₁, k) ⟨by omega, hi₁, by simpa using hkl⟩,
            W5_DeepLearningTheory_memT ⟨by omega, hi₁, by simpa using hkl⟩⟩ *
          v ⟨Subtype.mk (ℓ + 1, i₂, k') ⟨by omega, hi₂, by simpa using hkl'⟩,
            W5_DeepLearningTheory_memT ⟨by omega, hi₂, by simpa using hkl'⟩⟩)
      (fun a : W5_DeepLearningTheory_Sset n ℓ → ℝ =>
          linearPreact n (W5_DeepLearningTheory_Wa ℓ a) x₁ ℓ k *
            linearPreact n (W5_DeepLearningTheory_Wa ℓ a) x₂ ℓ k')
      (by fun_prop)
      (by
        have h1 := W5_DeepLearningTheory_Gmeas (n := n) x₁ ℓ ℓ k
        have h2 := W5_DeepLearningTheory_Gmeas (n := n) x₂ ℓ ℓ k'
        fun_prop)
    simp only at key
    have e : ∀ ω, W ω (ℓ + 1) i₁ k * linearPreact n (W ω) x₁ ℓ k *
        (W ω (ℓ + 1) i₂ k' * linearPreact n (W ω) x₂ ℓ k') =
        W ω (ℓ + 1) i₁ k * W ω (ℓ + 1) i₂ k' *
          (linearPreact n (W5_DeepLearningTheory_Wa (n := n) ℓ
              (fun q => W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2)) x₁ ℓ k *
            linearPreact n (W5_DeepLearningTheory_Wa (n := n) ℓ
              (fun q => W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2)) x₂ ℓ k') := by
      intro ω
      rw [W5_DeepLearningTheory_rep W x₁ ℓ ω ℓ le_rfl k hkl,
        W5_DeepLearningTheory_rep W x₂ ℓ ω ℓ le_rfl k' hkl']
      ring
    simp_rw [e]
    rw [key, W5_DeepLearningTheory_WW hW hi₁ hkl hi₂ hkl']
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    try simp only
    rw [← W5_DeepLearningTheory_rep W x₁ ℓ ω ℓ le_rfl k hkl,
      ← W5_DeepLearningTheory_rep W x₂ ℓ ω ℓ le_rfl k' hkl']
  rw [Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun k' hk' => hterm k hk k' hk']
  unfold kron
  by_cases h : i₁ = i₂
  · simp only [h, true_and, if_true, one_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.sum_eq_single k]
    · simp
    · intro k' _ hne
      simp [Ne.symm hne]
    · intro hk'
      exact absurd hk hk'
  · simp [h]

theorem W5_DeepLearningTheory_two_point_all (hW : IsLinearNetInit P n CW W) (hn : ∀ ℓ, 0 < n ℓ)
    (x₁ x₂ : ℕ → ℝ) : ∀ ℓ, 1 ≤ ℓ → ∀ i₁ i₂, i₁ < n ℓ → i₂ < n ℓ →
    ∫ ω, linearPreact n (W ω) x₁ ℓ i₁ * linearPreact n (W ω) x₂ ℓ i₂ ∂P
      = kron i₁ i₂ * (CW : ℝ) ^ ℓ * inputKernel (n 0) x₁ x₂ := by
  intro ℓ hℓ
  induction ℓ with
  | zero => omega
  | succ ℓ ih =>
    intro i₁ i₂ hi₁ hi₂
    rw [W5_DeepLearningTheory_R2 hW x₁ x₂ ℓ i₁ i₂ hi₁ hi₂]
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · subst h0
      simp only [linearPreact, integral_const, probReal_univ, one_smul]
      unfold inputKernel
      rw [NNReal.coe_div, NNReal.coe_natCast, Finset.mul_sum, Finset.mul_sum]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
    · rw [Finset.sum_congr rfl fun k hk =>
        ih hpos k k (Finset.mem_range.mp hk) (Finset.mem_range.mp hk)]
      simp only [kron, if_true, one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [NNReal.coe_div, NNReal.coe_natCast]
      have hnl : (n ℓ : ℝ) ≠ 0 := by exact_mod_cast (hn ℓ).ne'
      field_simp
      ring

end Init

theorem W5_DeepLearningTheory_linearNet_two_point {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (hn : ∀ ℓ, 0 < n ℓ) (CW : ℝ≥0)
    (W : Ω → ℕ → ℕ → ℕ → ℝ) (hW : IsLinearNetInit P n CW W) (x₁ x₂ : ℕ → ℝ)
    (ℓ i₁ i₂ : ℕ) (hℓ : 1 ≤ ℓ) (hi₁ : i₁ < n ℓ) (hi₂ : i₂ < n ℓ) :
    ∫ ω, linearPreact n (W ω) x₁ ℓ i₁ * linearPreact n (W ω) x₂ ℓ i₂ ∂P
      = kron i₁ i₂ * (CW : ℝ) ^ ℓ * inputKernel (n 0) x₁ x₂ :=
  W5_DeepLearningTheory_two_point_all hW hn x₁ x₂ ℓ hℓ i₁ i₂ hi₁ hi₂

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

/-! ### Joint law of the next-layer weights -/

section Init2
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n : ℕ → ℕ} {CW : ℝ≥0} {W : Ω → ℕ → ℕ → ℕ → ℝ}

theorem W5_DeepLearningTheory_Tlayer (ℓ : ℕ) (q : W5_DeepLearningTheory_Tset n ℓ) :
    q.1.1.1 = ℓ + 1 := by
  have h := q.2
  unfold W5_DeepLearningTheory_Tset at h
  have h' := Finset.mem_subtype.mp h
  simp only [Finset.mem_product, Finset.mem_singleton] at h'
  exact h'.1

theorem W5_DeepLearningTheory_Tjoint (hW : IsLinearNetInit P n CW W) (ℓ : ℕ) :
    P.map (fun ω (q : W5_DeepLearningTheory_Tset n ℓ) => W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2) =
      Measure.pi (fun _ : W5_DeepLearningTheory_Tset n ℓ => gaussianReal 0 (CW / (n ℓ : ℝ≥0))) := by
  have hind := hW.1.precomp (Subtype.val_injective (p := fun x => x ∈ W5_DeepLearningTheory_Tset n ℓ))
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map
    (fun q : W5_DeepLearningTheory_Tset n ℓ => W5_DeepLearningTheory_waem hW q.1)).1 hind
  refine hmap.trans ?_
  congr 1
  funext q
  rw [hW.2 _ _ _ q.1.2.1 q.1.2.2.1 q.1.2.2.2, W5_DeepLearningTheory_Tlayer ℓ q]
  rfl

theorem W5_DeepLearningTheory_W4 (hW : IsLinearNetInit P n CW W) {ℓ i₁ i₂ i₃ i₄ k₁ k₂ k₃ k₄ : ℕ}
    (hi₁ : i₁ < n (ℓ + 1)) (hi₂ : i₂ < n (ℓ + 1)) (hi₃ : i₃ < n (ℓ + 1)) (hi₄ : i₄ < n (ℓ + 1))
    (hk₁ : k₁ < n ℓ) (hk₂ : k₂ < n ℓ) (hk₃ : k₃ < n ℓ) (hk₄ : k₄ < n ℓ) :
    ∫ ω, W ω (ℓ + 1) i₁ k₁ * W ω (ℓ + 1) i₂ k₂ * W ω (ℓ + 1) i₃ k₃ * W ω (ℓ + 1) i₄ k₄ ∂P =
      ((CW / (n ℓ : ℝ≥0) : ℝ≥0) : ℝ) ^ 2 *
        ((if i₁ = i₂ ∧ k₁ = k₂ then 1 else 0) * (if i₃ = i₄ ∧ k₃ = k₄ then 1 else 0) +
          (if i₁ = i₃ ∧ k₁ = k₃ then 1 else 0) * (if i₂ = i₄ ∧ k₂ = k₄ then 1 else 0) +
          (if i₁ = i₄ ∧ k₁ = k₄ then 1 else 0) * (if i₂ = i₃ ∧ k₂ = k₃ then 1 else 0)) := by
  classical
  let t : ∀ i k, i < n (ℓ + 1) → k < n ℓ → W5_DeepLearningTheory_Tset n ℓ := fun i k hi hk =>
    ⟨Subtype.mk (ℓ + 1, i, k) ⟨by omega, hi, by simpa using hk⟩,
      W5_DeepLearningTheory_memT ⟨by omega, hi, by simpa using hk⟩⟩
  have ht : ∀ i k i' k' hi hk hi' hk', (t i k hi hk = t i' k' hi' hk') ↔ (i = i' ∧ k = k') := by
    intro i k i' k' hi hk hi' hk'
    constructor
    · intro h
      have h2 := congrArg (fun q : W5_DeepLearningTheory_Tset n ℓ => q.1.1) h
      simp only [t, Prod.mk.injEq, true_and] at h2
      exact h2
    · rintro ⟨rfl, rfl⟩; rfl
  have hB := W5_DeepLearningTheory_Baem hW ℓ
  have hΦ : Measurable (fun y : W5_DeepLearningTheory_Tset n ℓ → ℝ =>
      y (t i₁ k₁ hi₁ hk₁) * y (t i₂ k₂ hi₂ hk₂) * y (t i₃ k₃ hi₃ hk₃) * y (t i₄ k₄ hi₄ hk₄)) := by
    fun_prop
  calc ∫ ω, W ω (ℓ + 1) i₁ k₁ * W ω (ℓ + 1) i₂ k₂ * W ω (ℓ + 1) i₃ k₃ * W ω (ℓ + 1) i₄ k₄ ∂P
      = ∫ ω, (fun y : W5_DeepLearningTheory_Tset n ℓ → ℝ =>
          y (t i₁ k₁ hi₁ hk₁) * y (t i₂ k₂ hi₂ hk₂) * y (t i₃ k₃ hi₃ hk₃) *
            y (t i₄ k₄ hi₄ hk₄))
          ((fun ω (q : W5_DeepLearningTheory_Tset n ℓ) => W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2) ω) ∂P :=
        rfl
    _ = ∫ y, y (t i₁ k₁ hi₁ hk₁) * y (t i₂ k₂ hi₂ hk₂) * y (t i₃ k₃ hi₃ hk₃) *
            y (t i₄ k₄ hi₄ hk₄)
          ∂(P.map (fun ω (q : W5_DeepLearningTheory_Tset n ℓ) =>
            W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2)) :=
        (integral_map hB hΦ.aestronglyMeasurable).symm
    _ = _ := by
        rw [W5_DeepLearningTheory_Tjoint hW ℓ, W5_DeepLearningTheory_pi4]
        simp only [ht]

end Init2

/-! ### Four-point recursion -/

theorem W5_DeepLearningTheory_s2mul (s : Finset ℕ) (F : ℕ → ℕ → ℝ) (h : ℕ → ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, F a b) * (∑ c ∈ s, h c) = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, F a b * h c := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]

theorem W5_DeepLearningTheory_s3mul (s : Finset ℕ) (F : ℕ → ℕ → ℕ → ℝ) (h : ℕ → ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, F a b c) * (∑ d ∈ s, h d) =
      ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, F a b c * h d := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]

theorem W5_DeepLearningTheory_T1s (s : Finset ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℝ) :
    ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
      F a b c d * ((if a = b then (1 : ℝ) else 0) * (if c = d then 1 else 0))
      = ∑ a ∈ s, ∑ c ∈ s, F a a c c := by
  refine Finset.sum_congr rfl fun a ha => ?_
  have h : ∀ b, ∑ c ∈ s, ∑ d ∈ s,
      F a b c d * ((if a = b then (1 : ℝ) else 0) * (if c = d then 1 else 0))
      = (∑ c ∈ s, F a b c c) * (if a = b then 1 else 0) := by
    intro b
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c hc => ?_
    simp_rw [← mul_assoc]
    rw [Finset.sum_mul_boole]
    simp [hc]
  rw [Finset.sum_congr rfl fun b _ => h b, Finset.sum_mul_boole]
  simp [ha]

theorem W5_DeepLearningTheory_T2s (s : Finset ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℝ) :
    ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
      F a b c d * ((if a = c then (1 : ℝ) else 0) * (if b = d then 1 else 0))
      = ∑ a ∈ s, ∑ b ∈ s, F a b a b := by
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  have h : ∀ c, ∑ d ∈ s, F a b c d * ((if a = c then (1 : ℝ) else 0) * (if b = d then 1 else 0))
      = F a b c b * (if a = c then 1 else 0) := by
    intro c
    simp_rw [← mul_assoc]
    rw [Finset.sum_mul_boole]
    simp [hb]
  rw [Finset.sum_congr rfl fun c _ => h c, Finset.sum_mul_boole]
  simp [ha]

theorem W5_DeepLearningTheory_T3s (s : Finset ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℝ) :
    ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
      F a b c d * ((if a = d then (1 : ℝ) else 0) * (if b = c then 1 else 0))
      = ∑ a ∈ s, ∑ b ∈ s, F a b b a := by
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  have h : ∀ c, ∑ d ∈ s, F a b c d * ((if a = d then (1 : ℝ) else 0) * (if b = c then 1 else 0))
      = F a b c a * (if b = c then 1 else 0) := by
    intro c
    simp_rw [mul_comm (if a = _ then (1 : ℝ) else 0), ← mul_assoc]
    rw [Finset.sum_mul_boole]
    simp [ha]
  rw [Finset.sum_congr rfl fun c _ => h c, Finset.sum_mul_boole]
  simp [hb]

theorem W5_DeepLearningTheory_ite_and (p q : Prop) [Decidable p] [Decidable q] :
    (if p ∧ q then (1 : ℝ) else 0) = (if p then 1 else 0) * (if q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

section Four
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n : ℕ → ℕ} {CW : ℝ≥0} {W : Ω → ℕ → ℕ → ℕ → ℝ}

theorem W5_DeepLearningTheory_int4s (s : Finset ℕ) (F : ℕ → ℕ → ℕ → ℕ → Ω → ℝ)
    (hF : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s, Integrable (F a b c d) P) :
    ∫ ω, ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, F a b c d ω ∂P =
      ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, ∫ ω, F a b c d ω ∂P := by
  rw [integral_finsetSum _ (fun a ha => integrable_finsetSum _ fun b hb =>
    integrable_finsetSum _ fun c hc => integrable_finsetSum _ fun d hd => hF a ha b hb c hc d hd)]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [integral_finsetSum _ (fun b hb => integrable_finsetSum _ fun c hc =>
    integrable_finsetSum _ fun d hd => hF a ha b hb c hc d hd)]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [integral_finsetSum _ (fun c hc => integrable_finsetSum _ fun d hd => hF a ha b hb c hc d hd)]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [integral_finsetSum _ (fun d hd => hF a ha b hb c hc d hd)]

end Four

theorem W5_DeepLearningTheory_linearNet_four_point_recursion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (CW : ℝ≥0) (W : Ω → ℕ → ℕ → ℕ → ℝ)
    (hW : IsLinearNetInit P n CW W) (x : ℕ → ℝ) (ℓ i₁ i₂ i₃ i₄ : ℕ)
    (hi₁ : i₁ < n (ℓ + 1)) (hi₂ : i₂ < n (ℓ + 1)) (hi₃ : i₃ < n (ℓ + 1))
    (hi₄ : i₄ < n (ℓ + 1)) :
    ∫ ω, linearPreact n (W ω) x (ℓ + 1) i₁ * linearPreact n (W ω) x (ℓ + 1) i₂ *
        linearPreact n (W ω) x (ℓ + 1) i₃ * linearPreact n (W ω) x (ℓ + 1) i₄ ∂P
      = (CW : ℝ) ^ 2 * wickDelta4 i₁ i₂ i₃ i₄ * (1 / (n ℓ : ℝ) ^ 2) *
          ∑ j ∈ Finset.range (n ℓ), ∑ k ∈ Finset.range (n ℓ),
            ∫ ω, linearPreact n (W ω) x ℓ j * linearPreact n (W ω) x ℓ j *
              linearPreact n (W ω) x ℓ k * linearPreact n (W ω) x ℓ k ∂P := by
  set s := Finset.range (n ℓ) with hs
  set v : ℝ := ((CW / (n ℓ : ℝ≥0) : ℝ≥0) : ℝ) with hv
  set E4 : ℕ → ℕ → ℕ → ℕ → ℝ := fun a b c d => ∫ ω, linearPreact n (W ω) x ℓ a *
    linearPreact n (W ω) x ℓ b * linearPreact n (W ω) x ℓ c * linearPreact n (W ω) x ℓ d ∂P
    with hE4
  have hz : ∀ i ω, linearPreact n (W ω) x (ℓ + 1) i =
      ∑ k ∈ s, W ω (ℓ + 1) i k * linearPreact n (W ω) x ℓ k := fun i ω => rfl
  simp_rw [hz]
  have hexp : ∀ ω, (∑ a ∈ s, W ω (ℓ + 1) i₁ a * linearPreact n (W ω) x ℓ a) *
      (∑ b ∈ s, W ω (ℓ + 1) i₂ b * linearPreact n (W ω) x ℓ b) *
      (∑ c ∈ s, W ω (ℓ + 1) i₃ c * linearPreact n (W ω) x ℓ c) *
      (∑ d ∈ s, W ω (ℓ + 1) i₄ d * linearPreact n (W ω) x ℓ d) =
      ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, W ω (ℓ + 1) i₁ a * linearPreact n (W ω) x ℓ a *
        (W ω (ℓ + 1) i₂ b * linearPreact n (W ω) x ℓ b) *
        (W ω (ℓ + 1) i₃ c * linearPreact n (W ω) x ℓ c) *
        (W ω (ℓ + 1) i₄ d * linearPreact n (W ω) x ℓ d) := by
    intro ω
    rw [Finset.sum_mul_sum, W5_DeepLearningTheory_s2mul, W5_DeepLearningTheory_s3mul]
  simp_rw [hexp]
  have hAMW : ∀ i k, i < n (ℓ + 1) → k ∈ s →
      W5_DeepLearningTheory_AM P (fun ω => W ω (ℓ + 1) i k * linearPreact n (W ω) x ℓ k) :=
    fun i k hi hk => W5_DeepLearningTheory_AM_mul
      (W5_DeepLearningTheory_AM_gauss (hW.2 (ℓ + 1) i k (by omega) hi
        (by simpa using Finset.mem_range.mp hk)))
      (W5_DeepLearningTheory_AMz hW x ℓ k (Finset.mem_range.mp hk))
  rw [W5_DeepLearningTheory_int4s s _ (fun a ha b hb c hc d hd => W5_DeepLearningTheory_AM_int
    (W5_DeepLearningTheory_AM_mul (W5_DeepLearningTheory_AM_mul (W5_DeepLearningTheory_AM_mul
      (hAMW i₁ a hi₁ ha) (hAMW i₂ b hi₂ hb)) (hAMW i₃ c hi₃ hc)) (hAMW i₄ d hi₄ hd)))]
  have hterm : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      ∫ ω, W ω (ℓ + 1) i₁ a * linearPreact n (W ω) x ℓ a *
        (W ω (ℓ + 1) i₂ b * linearPreact n (W ω) x ℓ b) *
        (W ω (ℓ + 1) i₃ c * linearPreact n (W ω) x ℓ c) *
        (W ω (ℓ + 1) i₄ d * linearPreact n (W ω) x ℓ d) ∂P =
      v ^ 2 * ((if i₁ = i₂ ∧ a = b then 1 else 0) * (if i₃ = i₄ ∧ c = d then 1 else 0) +
          (if i₁ = i₃ ∧ a = c then 1 else 0) * (if i₂ = i₄ ∧ b = d then 1 else 0) +
          (if i₁ = i₄ ∧ a = d then 1 else 0) * (if i₂ = i₃ ∧ b = c then 1 else 0)) *
        E4 a b c d := by
    intro a ha b hb c hc d hd
    have ha' := Finset.mem_range.mp ha
    have hb' := Finset.mem_range.mp hb
    have hc' := Finset.mem_range.mp hc
    have hd' := Finset.mem_range.mp hd
    have key := W5_DeepLearningTheory_factor hW ℓ
      (fun y : W5_DeepLearningTheory_Tset n ℓ → ℝ =>
          y ⟨Subtype.mk (ℓ + 1, i₁, a) ⟨by omega, hi₁, by simpa using ha'⟩,
            W5_DeepLearningTheory_memT ⟨by omega, hi₁, by simpa using ha'⟩⟩ *
          y ⟨Subtype.mk (ℓ + 1, i₂, b) ⟨by omega, hi₂, by simpa using hb'⟩,
            W5_DeepLearningTheory_memT ⟨by omega, hi₂, by simpa using hb'⟩⟩ *
          y ⟨Subtype.mk (ℓ + 1, i₃, c) ⟨by omega, hi₃, by simpa using hc'⟩,
            W5_DeepLearningTheory_memT ⟨by omega, hi₃, by simpa using hc'⟩⟩ *
          y ⟨Subtype.mk (ℓ + 1, i₄, d) ⟨by omega, hi₄, by simpa using hd'⟩,
            W5_DeepLearningTheory_memT ⟨by omega, hi₄, by simpa using hd'⟩⟩)
      (fun y : W5_DeepLearningTheory_Sset n ℓ → ℝ =>
          linearPreact n (W5_DeepLearningTheory_Wa ℓ y) x ℓ a *
          linearPreact n (W5_DeepLearningTheory_Wa ℓ y) x ℓ b *
          linearPreact n (W5_DeepLearningTheory_Wa ℓ y) x ℓ c *
          linearPreact n (W5_DeepLearningTheory_Wa ℓ y) x ℓ d)
      (by fun_prop)
      (by
        have h1 := W5_DeepLearningTheory_Gmeas (n := n) x ℓ ℓ a
        have h2 := W5_DeepLearningTheory_Gmeas (n := n) x ℓ ℓ b
        have h3 := W5_DeepLearningTheory_Gmeas (n := n) x ℓ ℓ c
        have h4 := W5_DeepLearningTheory_Gmeas (n := n) x ℓ ℓ d
        fun_prop)
    simp only at key
    have e : ∀ ω, W ω (ℓ + 1) i₁ a * linearPreact n (W ω) x ℓ a *
        (W ω (ℓ + 1) i₂ b * linearPreact n (W ω) x ℓ b) *
        (W ω (ℓ + 1) i₃ c * linearPreact n (W ω) x ℓ c) *
        (W ω (ℓ + 1) i₄ d * linearPreact n (W ω) x ℓ d) =
        W ω (ℓ + 1) i₁ a * W ω (ℓ + 1) i₂ b * W ω (ℓ + 1) i₃ c * W ω (ℓ + 1) i₄ d *
          (linearPreact n (W5_DeepLearningTheory_Wa (n := n) ℓ
              (fun q => W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2)) x ℓ a *
            linearPreact n (W5_DeepLearningTheory_Wa (n := n) ℓ
              (fun q => W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2)) x ℓ b *
            linearPreact n (W5_DeepLearningTheory_Wa (n := n) ℓ
              (fun q => W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2)) x ℓ c *
            linearPreact n (W5_DeepLearningTheory_Wa (n := n) ℓ
              (fun q => W ω q.1.1.1 q.1.1.2.1 q.1.1.2.2)) x ℓ d) := by
      intro ω
      rw [W5_DeepLearningTheory_rep W x ℓ ω ℓ le_rfl a ha',
        W5_DeepLearningTheory_rep W x ℓ ω ℓ le_rfl b hb',
        W5_DeepLearningTheory_rep W x ℓ ω ℓ le_rfl c hc',
        W5_DeepLearningTheory_rep W x ℓ ω ℓ le_rfl d hd']
      ring
    simp_rw [e]
    rw [key]
    rw [W5_DeepLearningTheory_W4 hW hi₁ hi₂ hi₃ hi₄ ha' hb' hc' hd']
    congr 1
    simp only [hE4]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    try simp only
    rw [← W5_DeepLearningTheory_rep W x ℓ ω ℓ le_rfl a ha',
      ← W5_DeepLearningTheory_rep W x ℓ ω ℓ le_rfl b hb',
      ← W5_DeepLearningTheory_rep W x ℓ ω ℓ le_rfl c hc',
      ← W5_DeepLearningTheory_rep W x ℓ ω ℓ le_rfl d hd']
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb =>
    Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd => hterm a ha b hb c hc d hd]
  have hsplit : ∀ a b c d : ℕ,
      v ^ 2 * ((if i₁ = i₂ ∧ a = b then 1 else 0) * (if i₃ = i₄ ∧ c = d then 1 else 0) +
          (if i₁ = i₃ ∧ a = c then 1 else 0) * (if i₂ = i₄ ∧ b = d then 1 else 0) +
          (if i₁ = i₄ ∧ a = d then 1 else 0) * (if i₂ = i₃ ∧ b = c then 1 else 0)) *
        E4 a b c d =
      (v ^ 2 * (kron i₁ i₂ * kron i₃ i₄)) *
          (E4 a b c d * ((if a = b then (1 : ℝ) else 0) * (if c = d then 1 else 0))) +
        (v ^ 2 * (kron i₁ i₃ * kron i₂ i₄)) *
          (E4 a b c d * ((if a = c then (1 : ℝ) else 0) * (if b = d then 1 else 0))) +
        (v ^ 2 * (kron i₁ i₄ * kron i₂ i₃)) *
          (E4 a b c d * ((if a = d then (1 : ℝ) else 0) * (if b = c then 1 else 0))) := by
    intro a b c d
    simp only [W5_DeepLearningTheory_ite_and, kron]
    ring
  simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [W5_DeepLearningTheory_T1s, W5_DeepLearningTheory_T2s, W5_DeepLearningTheory_T3s]
  have h2 : ∑ a ∈ s, ∑ b ∈ s, E4 a b a b = ∑ a ∈ s, ∑ b ∈ s, E4 a a b b := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hE4]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  have h3 : ∑ a ∈ s, ∑ b ∈ s, E4 a b b a = ∑ a ∈ s, ∑ b ∈ s, E4 a a b b := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hE4]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  rw [h2, h3]
  simp only [hE4, hv, wickDelta4, NNReal.coe_div, NNReal.coe_natCast]
  ring

theorem W5_DeepLearningTheory_linearNet_four_point_first_layer {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (CW : ℝ≥0) (W : Ω → ℕ → ℕ → ℕ → ℝ)
    (hW : IsLinearNetInit P n CW W) (x : ℕ → ℝ) (i₁ i₂ i₃ i₄ : ℕ)
    (hi₁ : i₁ < n 1) (hi₂ : i₂ < n 1) (hi₃ : i₃ < n 1) (hi₄ : i₄ < n 1) :
    ∫ ω, linearPreact n (W ω) x 1 i₁ * linearPreact n (W ω) x 1 i₂ *
        linearPreact n (W ω) x 1 i₃ * linearPreact n (W ω) x 1 i₄ ∂P
      = (CW : ℝ) ^ 2 * wickDelta4 i₁ i₂ i₃ i₄ * inputKernel (n 0) x x ^ 2 := by
  refine (W5_DeepLearningTheory_linearNet_four_point_recursion P n CW W hW x 0 i₁ i₂ i₃ i₄
    hi₁ hi₂ hi₃ hi₄).trans ?_
  simp only [linearPreact, integral_const, probReal_univ, one_smul]
  have h : ∑ j ∈ Finset.range (n 0), ∑ k ∈ Finset.range (n 0), x j * x j * x k * x k =
      (∑ j ∈ Finset.range (n 0), x j * x j) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [h]
  unfold inputKernel
  ring

theorem W5_DeepLearningTheory_linearNet_G4_recursion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (hn : ∀ ℓ, 0 < n ℓ) (CW : ℝ≥0)
    (W : Ω → ℕ → ℕ → ℕ → ℝ) (hW : IsLinearNetInit P n CW W) (x : ℕ → ℝ) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (G4 : ℝ)
    (hG4 : ∀ i₁ i₂ i₃ i₄, i₁ < n ℓ → i₂ < n ℓ → i₃ < n ℓ → i₄ < n ℓ →
      ∫ ω, linearPreact n (W ω) x ℓ i₁ * linearPreact n (W ω) x ℓ i₂ *
        linearPreact n (W ω) x ℓ i₃ * linearPreact n (W ω) x ℓ i₄ ∂P
        = wickDelta4 i₁ i₂ i₃ i₄ * G4)
    (i₁ i₂ i₃ i₄ : ℕ) (hi₁ : i₁ < n (ℓ + 1)) (hi₂ : i₂ < n (ℓ + 1))
    (hi₃ : i₃ < n (ℓ + 1)) (hi₄ : i₄ < n (ℓ + 1)) :
    ∫ ω, linearPreact n (W ω) x (ℓ + 1) i₁ * linearPreact n (W ω) x (ℓ + 1) i₂ *
        linearPreact n (W ω) x (ℓ + 1) i₃ * linearPreact n (W ω) x (ℓ + 1) i₄ ∂P
      = wickDelta4 i₁ i₂ i₃ i₄ * ((CW : ℝ) ^ 2 * (1 + 2 / (n ℓ : ℝ)) * G4) := by
  rw [W5_DeepLearningTheory_linearNet_four_point_recursion P n CW W hW x ℓ i₁ i₂ i₃ i₄
    hi₁ hi₂ hi₃ hi₄]
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk =>
    hG4 j j k k (Finset.mem_range.mp hj) (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)
      (Finset.mem_range.mp hk)]
  have hw : ∀ j ∈ Finset.range (n ℓ),
      ∑ k ∈ Finset.range (n ℓ), wickDelta4 j j k k * G4 = ((n ℓ : ℝ) + 2) * G4 := by
    intro j hj
    rw [← Finset.sum_mul]
    congr 1
    unfold wickDelta4 kron
    simp only [if_true, mul_one, one_mul]
    have hsq : ∀ k, (if j = k then (1 : ℝ) else 0) * (if j = k then 1 else 0) =
        if j = k then 1 else 0 := by
      intro k; split_ifs <;> simp
    simp only [hsq, Finset.sum_add_distrib, Finset.sum_ite_eq, hj, if_true, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    ring
  rw [Finset.sum_congr rfl hw, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hnl : (n ℓ : ℝ) ≠ 0 := by exact_mod_cast (hn ℓ).ne'
  field_simp
  try ring

theorem W5_DeepLearningTheory_linearNet_four_point {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (hn : ∀ ℓ, 0 < n ℓ) (CW : ℝ≥0)
    (W : Ω → ℕ → ℕ → ℕ → ℝ) (hW : IsLinearNetInit P n CW W) (x : ℕ → ℝ)
    (ℓ i₁ i₂ i₃ i₄ : ℕ) (hℓ : 1 ≤ ℓ)
    (hi₁ : i₁ < n ℓ) (hi₂ : i₂ < n ℓ) (hi₃ : i₃ < n ℓ) (hi₄ : i₄ < n ℓ) :
    ∫ ω, linearPreact n (W ω) x ℓ i₁ * linearPreact n (W ω) x ℓ i₂ *
        linearPreact n (W ω) x ℓ i₃ * linearPreact n (W ω) x ℓ i₄ ∂P
      = wickDelta4 i₁ i₂ i₃ i₄ *
          ((CW : ℝ) ^ (2 * ℓ) * (∏ ℓ' ∈ Finset.Ico 1 ℓ, (1 + 2 / (n ℓ' : ℝ))) *
            inputKernel (n 0) x x ^ 2) := by
  have main : ∀ ℓ, 1 ≤ ℓ → ∀ i₁ i₂ i₃ i₄, i₁ < n ℓ → i₂ < n ℓ → i₃ < n ℓ → i₄ < n ℓ →
      ∫ ω, linearPreact n (W ω) x ℓ i₁ * linearPreact n (W ω) x ℓ i₂ *
        linearPreact n (W ω) x ℓ i₃ * linearPreact n (W ω) x ℓ i₄ ∂P
      = wickDelta4 i₁ i₂ i₃ i₄ *
          ((CW : ℝ) ^ (2 * ℓ) * (∏ ℓ' ∈ Finset.Ico 1 ℓ, (1 + 2 / (n ℓ' : ℝ))) *
            inputKernel (n 0) x x ^ 2) := by
    intro ℓ hℓ
    induction ℓ with
    | zero => omega
    | succ ℓ ih =>
      intro i₁ i₂ i₃ i₄ h1 h2 h3 h4
      rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
      · subst h0
        refine (W5_DeepLearningTheory_linearNet_four_point_first_layer P n CW W hW x
          i₁ i₂ i₃ i₄ h1 h2 h3 h4).trans ?_
        simp
        ring
      · rw [W5_DeepLearningTheory_linearNet_G4_recursion P n hn CW W hW x ℓ hpos _ (ih hpos)
          i₁ i₂ i₃ i₄ h1 h2 h3 h4, Finset.prod_Ico_succ_top hpos]
        ring
  exact main ℓ hℓ i₁ i₂ i₃ i₄ hi₁ hi₂ hi₃ hi₄

theorem W5_DeepLearningTheory_linearNet_connected_four_point {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (hn : ∀ ℓ, 0 < n ℓ) (CW : ℝ≥0)
    (W : Ω → ℕ → ℕ → ℕ → ℝ) (hW : IsLinearNetInit P n CW W) (x : ℕ → ℝ)
    (ℓ j k : ℕ) (hℓ : 1 ≤ ℓ) (hj : j < n ℓ) (hk : k < n ℓ) (hjk : j ≠ k) :
    ∫ ω, (linearPreact n (W ω) x ℓ j ^ 2 - (CW : ℝ) ^ ℓ * inputKernel (n 0) x x) *
        (linearPreact n (W ω) x ℓ k ^ 2 - (CW : ℝ) ^ ℓ * inputKernel (n 0) x x) ∂P
      = (CW : ℝ) ^ (2 * ℓ) * (∏ ℓ' ∈ Finset.Ico 1 ℓ, (1 + 2 / (n ℓ' : ℝ))) *
            inputKernel (n 0) x x ^ 2
          - ((CW : ℝ) ^ ℓ * inputKernel (n 0) x x) ^ 2 := by
  set c := (CW : ℝ) ^ ℓ * inputKernel (n 0) x x with hc
  have hAj := W5_DeepLearningTheory_AMz hW x ℓ j hj
  have hAk := W5_DeepLearningTheory_AMz hW x ℓ k hk
  have e : ∀ ω, (linearPreact n (W ω) x ℓ j ^ 2 - c) * (linearPreact n (W ω) x ℓ k ^ 2 - c) =
      linearPreact n (W ω) x ℓ j * linearPreact n (W ω) x ℓ j * linearPreact n (W ω) x ℓ k *
        linearPreact n (W ω) x ℓ k - c * (linearPreact n (W ω) x ℓ j * linearPreact n (W ω) x ℓ j)
        - c * (linearPreact n (W ω) x ℓ k * linearPreact n (W ω) x ℓ k) + c ^ 2 := by
    intro ω; ring
  simp_rw [e]
  have i1 := W5_DeepLearningTheory_AM_int (W5_DeepLearningTheory_AM_mul
    (W5_DeepLearningTheory_AM_mul (W5_DeepLearningTheory_AM_mul hAj hAj) hAk) hAk)
  have i2 := (W5_DeepLearningTheory_AM_int (W5_DeepLearningTheory_AM_mul hAj hAj)).const_mul c
  have i3 := (W5_DeepLearningTheory_AM_int (W5_DeepLearningTheory_AM_mul hAk hAk)).const_mul c
  have i12 : Integrable (fun ω => linearPreact n (W ω) x ℓ j * linearPreact n (W ω) x ℓ j *
      linearPreact n (W ω) x ℓ k * linearPreact n (W ω) x ℓ k -
      c * (linearPreact n (W ω) x ℓ j * linearPreact n (W ω) x ℓ j)) P := i1.sub i2
  have i123 : Integrable (fun ω => linearPreact n (W ω) x ℓ j * linearPreact n (W ω) x ℓ j *
      linearPreact n (W ω) x ℓ k * linearPreact n (W ω) x ℓ k -
      c * (linearPreact n (W ω) x ℓ j * linearPreact n (W ω) x ℓ j) -
      c * (linearPreact n (W ω) x ℓ k * linearPreact n (W ω) x ℓ k)) P := i12.sub i3
  rw [integral_add i123 (integrable_const _), integral_sub i12 i3,
    integral_sub i1 i2, integral_const_mul, integral_const_mul, integral_const]
  rw [W5_DeepLearningTheory_linearNet_four_point P n hn CW W hW x ℓ j j k k hℓ hj hj hk hk,
    W5_DeepLearningTheory_two_point_all hW hn x x ℓ hℓ j j hj hj,
    W5_DeepLearningTheory_two_point_all hW hn x x ℓ hℓ k k hk hk]
  have hw : wickDelta4 j j k k = 1 := by
    unfold wickDelta4 kron
    simp [hjk]
  rw [hw]
  simp only [kron, if_true, probReal_univ, one_smul, one_mul]
  ring
