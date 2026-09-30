-- Prove2me | solution 1 for ComputationalLearning.weak_strong_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T01:33:18.859774+00:00
-- url     : https://prove2.me/submissions/60e4cad0-2dfe-457e-af0b-dee92c62a842

import Mathlib
import Definitions.Def_ComputationalLearning_Boosting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ComputationalLearning in
def p426_tree {X : Type*} {m : ℕ} (L : (Fin m → X × Bool) → X → Bool) :
    (k : ℕ) → ((Fin k → Fin 3) → Fin m → X × Bool) → X → Bool
  | 0, T => L (T (fun i => i.elim0))
  | k + 1, T => majority3 (p426_tree L k (fun p => T (Fin.cons (0 : Fin 3) p)))
      (p426_tree L k (fun p => T (Fin.cons (1 : Fin 3) p)))
      (p426_tree L k (fun p => T (Fin.cons (2 : Fin 3) p)))

open MeasureTheory ProbabilityTheory ComputationalLearning in
noncomputable def p426_ind {X : Type*} {N : ℕ} (S : Fin N → X × Bool) (h : X → Bool)
    (j : Fin N) : ℝ :=
  if h (S j).1 = (S j).2 then 0 else 1

open MeasureTheory ProbabilityTheory ComputationalLearning in
noncomputable def p426_werr {X : Type*} {N : ℕ} (S : Fin N → X × Bool) (w : Fin N → ℝ)
    (h : X → Bool) : ℝ :=
  ∑ j, w j * p426_ind S h j

open MeasureTheory ProbabilityTheory ComputationalLearning in
noncomputable def p426_w2 {X : Type*} {N : ℕ} (S : Fin N → X × Bool) (w : Fin N → ℝ)
    (h₁ : X → Bool) : Fin N → ℝ :=
  fun j => w j * (p426_ind S h₁ j / (2 * p426_werr S w h₁) +
    (1 - p426_ind S h₁ j) / (2 * (1 - p426_werr S w h₁)))

open MeasureTheory ProbabilityTheory ComputationalLearning in
noncomputable def p426_Z {X : Type*} {N : ℕ} (S : Fin N → X × Bool) (w : Fin N → ℝ)
    (h₁ h₂ : X → Bool) : ℝ :=
  ∑ j, w j * (p426_ind S h₁ j + p426_ind S h₂ j - 2 * p426_ind S h₁ j * p426_ind S h₂ j)

open MeasureTheory ProbabilityTheory ComputationalLearning in
noncomputable def p426_w3 {X : Type*} {N : ℕ} (S : Fin N → X × Bool) (w : Fin N → ℝ)
    (h₁ h₂ : X → Bool) : Fin N → ℝ :=
  fun j => w j * (p426_ind S h₁ j + p426_ind S h₂ j - 2 * p426_ind S h₁ j * p426_ind S h₂ j) /
    p426_Z S w h₁ h₂

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_ind_cases {X : Type*} {N : ℕ} (S : Fin N → X × Bool) (h : X → Bool) (j : Fin N) :
    p426_ind S h j = 0 ∨ p426_ind S h j = 1 := by
  unfold p426_ind
  by_cases h' : h (S j).1 = (S j).2 <;> simp [h']

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_ind_nonneg {X : Type*} {N : ℕ} (S : Fin N → X × Bool) (h : X → Bool) (j : Fin N) :
    0 ≤ p426_ind S h j := by
  rcases p426_ind_cases S h j with h' | h' <;> simp [h']

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_ind_maj {X : Type*} {N : ℕ} (S : Fin N → X × Bool) (h₁ h₂ h₃ : X → Bool)
    (j : Fin N) :
    p426_ind S (majority3 h₁ h₂ h₃) j = p426_ind S h₁ j * p426_ind S h₂ j +
      (p426_ind S h₁ j + p426_ind S h₂ j - 2 * p426_ind S h₁ j * p426_ind S h₂ j) *
        p426_ind S h₃ j := by
  simp only [p426_ind, majority3]
  rcases Bool.eq_false_or_eq_true (h₁ (S j).1) with ha | ha <;>
  rcases Bool.eq_false_or_eq_true (h₂ (S j).1) with hb | hb <;>
  rcases Bool.eq_false_or_eq_true (h₃ (S j).1) with hc | hc <;>
  rcases Bool.eq_false_or_eq_true (S j).2 with hy | hy <;>
  (simp [ha, hb, hc, hy]; try norm_num)

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_maj_self {X : Type*} (h : X → Bool) : majority3 h h h = h := by
  funext x
  simp only [majority3]
  cases h x <;> rfl

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_poly (β e u v : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 1 / 2) (he0 : 0 < e) (heβ : e ≤ β)
    (hu : 0 ≤ u) (_hv : 0 ≤ v) (huv : u + v ≤ 2 * β) :
    (1 - β) * e * u + β * e + β * (1 - e) * v ≤ 3 * β ^ 2 - 2 * β ^ 3 := by
  have h1 : 0 ≤ β * (1 - e) := mul_nonneg hβ0 (by linarith)
  have h2 := mul_le_mul_of_nonneg_left huv h1
  have h3 := mul_nonneg (sub_nonneg.2 heβ) hu
  have h4 := mul_nonneg (sub_nonneg.2 heβ) (mul_nonneg hβ0 (by linarith : (0:ℝ) ≤ 1 - 2 * β))
  nlinarith

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_core {N : ℕ} (w a b c : Fin N → ℝ) (hw0 : ∀ j, 0 ≤ w j)
    (ha : ∀ j, a j = 0 ∨ a j = 1) (hb : ∀ j, b j = 0 ∨ b j = 1) (hc : ∀ j, c j = 0 ∨ c j = 1)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 1 / 2)
    (he0 : 0 < ∑ j, w j * a j) (he : ∑ j, w j * a j ≤ β)
    (h2 : ∑ j, w j * (a j / (2 * ∑ i, w i * a i) + (1 - a j) / (2 * (1 - ∑ i, w i * a i))) *
      b j ≤ β)
    (h3 : ∑ j, w j * (a j + b j - 2 * a j * b j) = 0 ∨
      ∑ j, w j * (a j + b j - 2 * a j * b j) / (∑ i, w i * (a i + b i - 2 * a i * b i)) * c j
        ≤ β) :
    ∑ j, w j * (a j * b j + (a j + b j - 2 * a j * b j) * c j) ≤ 3 * β ^ 2 - 2 * β ^ 3 := by
  set e := ∑ j, w j * a j with he_def
  set Z := ∑ j, w j * (a j + b j - 2 * a j * b j) with hZ_def
  set p := ∑ j, w j * (a j * b j) with hp
  set q := ∑ j, w j * (a j * (1 - b j)) with hq
  set r := ∑ j, w j * ((1 - a j) * b j) with hr
  have hne : e ≠ 0 := he0.ne'
  have hne1 : (1 : ℝ) - e ≠ 0 := by intro h; linarith
  have hp0 : 0 ≤ p := Finset.sum_nonneg (fun j _ => mul_nonneg (hw0 j) (by
    rcases ha j with h | h <;> rcases hb j with h' | h' <;> rw [h, h'] <;> norm_num))
  have hr0 : 0 ≤ r := Finset.sum_nonneg (fun j _ => mul_nonneg (hw0 j) (by
    rcases ha j with h | h <;> rcases hb j with h' | h' <;> rw [h, h'] <;> norm_num))
  have hdis : ∀ j, 0 ≤ w j * (a j + b j - 2 * a j * b j) := fun j => mul_nonneg (hw0 j) (by
    rcases ha j with h | h <;> rcases hb j with h' | h' <;> rw [h, h'] <;> norm_num)
  have hF1 : e = p + q := by
    rw [he_def, hp, hq, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hF3 : Z = q + r := by
    rw [hZ_def, hq, hr, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hF2 : ∑ j, w j * (a j / (2 * e) + (1 - a j) / (2 * (1 - e))) * b j =
      p / e / 2 + r / (1 - e) / 2 := by
    rw [hp, hr]
    simp only [Finset.sum_div]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by field_simp)
  have hF4 : ∑ j, w j * (a j * b j + (a j + b j - 2 * a j * b j) * c j) =
      p + ∑ j, w j * (a j + b j - 2 * a j * b j) * c j := by
    rw [hp, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hF5 : ∑ j, w j * (a j + b j - 2 * a j * b j) * c j ≤ β * (q + r) := by
    rw [← hF3]
    by_cases hZ0 : Z = 0
    · have hle : ∑ j, w j * (a j + b j - 2 * a j * b j) * c j ≤ Z := by
        rw [hZ_def]
        refine Finset.sum_le_sum (fun j _ => ?_)
        have := hdis j
        rcases hc j with h | h <;> rw [h] <;> linarith
      rw [hZ0] at hle ⊢
      linarith
    · have hZpos : 0 < Z := lt_of_le_of_ne (Finset.sum_nonneg (fun j _ => hdis j)) (Ne.symm hZ0)
      rcases h3 with h3 | h3
      · exact absurd h3 hZ0
      · have hq3 : ∑ j, w j * (a j + b j - 2 * a j * b j) / Z * c j =
            (∑ j, w j * (a j + b j - 2 * a j * b j) * c j) / Z := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [hq3, div_le_iff₀ hZpos] at h3
        linarith
  have hu0 : 0 ≤ p / e := div_nonneg hp0 he0.le
  have hv0 : 0 ≤ r / (1 - e) := div_nonneg hr0 (by linarith)
  have huv : p / e + r / (1 - e) ≤ 2 * β := by rw [hF2] at h2; linarith
  have key := p426_poly β e (p / e) (r / (1 - e)) hβ0 hβ he0 he hu0 hv0 huv
  have hpe : e * (p / e) = p := by field_simp
  have hre : (1 - e) * (r / (1 - e)) = r := by field_simp
  have hq' : q = e - p := by linarith [hF1]
  have hkey : p + β * (q + r) =
      (1 - β) * e * (p / e) + β * e + β * (1 - e) * (r / (1 - e)) := by
    rw [hq']
    calc p + β * (e - p + r) = (1 - β) * p + β * e + β * r := by ring
      _ = (1 - β) * (e * (p / e)) + β * e + β * ((1 - e) * (r / (1 - e))) := by rw [hpe, hre]
      _ = _ := by ring
  rw [hF4]
  linarith [hF5, hkey, key]

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_w2_prob {N : ℕ} (w a : Fin N → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (ha : ∀ j, a j = 0 ∨ a j = 1) (he0 : 0 < ∑ j, w j * a j) (he1 : ∑ j, w j * a j < 1) :
    (∀ j, 0 ≤ w j * (a j / (2 * ∑ i, w i * a i) + (1 - a j) / (2 * (1 - ∑ i, w i * a i)))) ∧
    ∑ j, w j * (a j / (2 * ∑ i, w i * a i) + (1 - a j) / (2 * (1 - ∑ i, w i * a i))) = 1 := by
  set e := ∑ j, w j * a j with he_def
  have h1e : 0 < 1 - e := by linarith
  refine ⟨fun j => mul_nonneg (hw0 j) ?_, ?_⟩
  · have ha0 : 0 ≤ a j := by rcases ha j with h | h <;> simp [h]
    have ha1 : 0 ≤ 1 - a j := by rcases ha j with h | h <;> simp [h]
    exact add_nonneg (div_nonneg ha0 (by linarith)) (div_nonneg ha1 (by linarith))
  · have hsum : ∑ j, w j * (a j / (2 * e) + (1 - a j) / (2 * (1 - e))) =
        (∑ j, w j * a j) * (1 / (2 * e) - 1 / (2 * (1 - e))) +
          (∑ j, w j) * (1 / (2 * (1 - e))) := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsum, hw1, ← he_def]
    field_simp
    ring

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_w3_prob {N : ℕ} (w a b : Fin N → ℝ) (hw0 : ∀ j, 0 ≤ w j)
    (ha : ∀ j, a j = 0 ∨ a j = 1) (hb : ∀ j, b j = 0 ∨ b j = 1)
    (hZ : ∑ j, w j * (a j + b j - 2 * a j * b j) ≠ 0) :
    (∀ j, 0 ≤ w j * (a j + b j - 2 * a j * b j) / ∑ i, w i * (a i + b i - 2 * a i * b i)) ∧
    ∑ j, w j * (a j + b j - 2 * a j * b j) / (∑ i, w i * (a i + b i - 2 * a i * b i)) = 1 := by
  have hdis : ∀ j, 0 ≤ w j * (a j + b j - 2 * a j * b j) := fun j => mul_nonneg (hw0 j) (by
    rcases ha j with h | h <;> rcases hb j with h' | h' <;> rw [h, h'] <;> norm_num)
  have hZ0 : 0 ≤ ∑ j, w j * (a j + b j - 2 * a j * b j) := Finset.sum_nonneg (fun j _ => hdis j)
  refine ⟨fun j => div_nonneg (hdis j) hZ0, ?_⟩
  rw [← Finset.sum_div]
  exact div_self hZ

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_iter_bounds (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 1 / 2) :
    ∀ k : ℕ, 0 ≤ boostFun^[k] β ∧ boostFun^[k] β ≤ β := by
  intro k
  induction k with
  | zero => exact ⟨hβ0, le_rfl⟩
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    rw [Function.iterate_succ_apply']
    set x := boostFun^[k] β
    unfold boostFun
    have hx2 : x < 1 / 2 := lt_of_le_of_lt h1 hβ
    constructor
    · have := mul_nonneg (sq_nonneg x) (show (0:ℝ) ≤ 3 - 2 * x by linarith)
      nlinarith
    · have := mul_nonneg (mul_nonneg h0 (show (0:ℝ) ≤ 1 - x by linarith))
        (show (0:ℝ) ≤ 1 - 2 * x by linarith)
      nlinarith

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_tree_mem {X : Type*} {m : ℕ} (H : Set (X → Bool))
    (L : (Fin m → X × Bool) → X → Bool) (hLH : ∀ S, L S ∈ H) (k : ℕ) :
    ∀ T, p426_tree L k T ∈ majorityTrees H := by
  induction k with
  | zero => intro T; exact MajorityTree.leaf (hLH _)
  | succ k ih => intro T; exact MajorityTree.node (ih _) (ih _) (ih _)

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_tree_meas {X : Type*} [MeasurableSpace X] {m : ℕ}
    (L : (Fin m → X × Bool) → X → Bool)
    (hL : Measurable (fun p : (Fin m → X × Bool) × X ↦ L p.1 p.2)) (k : ℕ) :
    Measurable (fun z : ((Fin k → Fin 3) → Fin m → X × Bool) × X ↦ p426_tree L k z.1 z.2) := by
  induction k with
  | zero =>
    have h1 : Measurable (fun z : ((Fin 0 → Fin 3) → Fin m → X × Bool) × X =>
        (z.1 (fun i => i.elim0), z.2)) :=
      ((measurable_pi_apply _).comp measurable_fst).prodMk measurable_snd
    exact hL.comp h1
  | succ k ih =>
    have hsub : ∀ a : Fin 3, Measurable (fun z : ((Fin (k + 1) → Fin 3) → Fin m → X × Bool) × X ↦
        p426_tree L k (fun p => z.1 (Fin.cons a p)) z.2) := by
      intro a
      have h1 : Measurable (fun z : ((Fin (k + 1) → Fin 3) → Fin m → X × Bool) × X =>
          ((fun p => z.1 (Fin.cons a p)), z.2)) :=
        (measurable_pi_lambda _
          (fun p => (measurable_pi_apply _).comp measurable_fst)).prodMk measurable_snd
      exact ih.comp h1
    have hf : Measurable (fun t : Bool × Bool × Bool =>
        (t.1 && t.2.1) || (t.1 && t.2.2) || (t.2.1 && t.2.2)) := measurable_of_finite _
    exact hf.comp ((hsub 0).prodMk ((hsub 1).prodMk (hsub 2)))

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_tree_comb {X : Type*} {m N k : ℕ} (L : (Fin m → X × Bool) → X → Bool)
    (S : Fin N → X × Bool) (ι₁ ι₂ ι₃ : (Fin k → Fin 3) → Fin m → Fin N) :
    p426_tree L (k + 1) (fun p i => S (![ι₁, ι₂, ι₃] (p 0) (Fin.tail p) i)) =
      majority3 (p426_tree L k (fun p i => S (ι₁ p i))) (p426_tree L k (fun p i => S (ι₂ p i)))
        (p426_tree L k (fun p i => S (ι₃ p i))) := by
  rfl

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_exists {X : Type*} {m N : ℕ} (L : (Fin m → X × Bool) → X → Bool)
    (S : Fin N → X × Bool) (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 1 / 2)
    (hbase : ∀ w : Fin N → ℝ, (∀ j, 0 ≤ w j) → ∑ j, w j = 1 →
      ∃ τ : Fin m → Fin N, p426_werr S w (L (fun i => S (τ i))) ≤ β) :
    ∀ (k : ℕ) (w : Fin N → ℝ), (∀ j, 0 ≤ w j) → ∑ j, w j = 1 →
      ∃ ι : (Fin k → Fin 3) → Fin m → Fin N,
        p426_werr S w (p426_tree L k (fun p i => S (ι p i))) ≤ boostFun^[k] β := by
  intro k
  induction k with
  | zero =>
    intro w hw0 hw1
    obtain ⟨τ, hτ⟩ := hbase w hw0 hw1
    exact ⟨fun _ => τ, hτ⟩
  | succ k ih =>
    intro w hw0 hw1
    obtain ⟨hb0, hb1⟩ := p426_iter_bounds β hβ0 hβ k
    have hβ'2 : boostFun^[k] β < 1 / 2 := lt_of_le_of_lt hb1 hβ
    obtain ⟨hg0, -⟩ := p426_iter_bounds β hβ0 hβ (k + 1)
    rw [Function.iterate_succ_apply'] at hg0 ⊢
    obtain ⟨ι₁, hι₁⟩ := ih w hw0 hw1
    have hcases := fun h j => p426_ind_cases S h j
    by_cases he0 : p426_werr S w (p426_tree L k (fun p i => S (ι₁ p i))) = 0
    · refine ⟨fun p => ![ι₁, ι₁, ι₁] (p 0) (Fin.tail p), ?_⟩
      rw [p426_tree_comb, p426_maj_self, he0]
      exact hg0
    · have he1 : 0 < p426_werr S w (p426_tree L k (fun p i => S (ι₁ p i))) :=
        lt_of_le_of_ne (Finset.sum_nonneg (fun j _ => mul_nonneg (hw0 j)
          (p426_ind_nonneg S _ j))) (Ne.symm he0)
      have hw2 := p426_w2_prob w (p426_ind S (p426_tree L k (fun p i => S (ι₁ p i))))
        hw0 hw1 (hcases _) he1 (lt_of_le_of_lt hι₁ (by linarith))
      obtain ⟨ι₂, hι₂⟩ := ih (p426_w2 S w (p426_tree L k (fun p i => S (ι₁ p i)))) hw2.1 hw2.2
      by_cases hZ : p426_Z S w (p426_tree L k (fun p i => S (ι₁ p i)))
          (p426_tree L k (fun p i => S (ι₂ p i))) = 0
      · refine ⟨fun p => ![ι₁, ι₂, ι₁] (p 0) (Fin.tail p), ?_⟩
        rw [p426_tree_comb]
        unfold p426_werr
        simp only [p426_ind_maj]
        exact p426_core w _ _ _ hw0 (hcases _) (hcases _) (hcases _) _ hb0 hβ'2 he1 hι₁ hι₂
          (Or.inl hZ)
      · have hw3 := p426_w3_prob w (p426_ind S (p426_tree L k (fun p i => S (ι₁ p i))))
          (p426_ind S (p426_tree L k (fun p i => S (ι₂ p i)))) hw0 (hcases _) (hcases _) hZ
        obtain ⟨ι₃, hι₃⟩ := ih (p426_w3 S w (p426_tree L k (fun p i => S (ι₁ p i)))
          (p426_tree L k (fun p i => S (ι₂ p i)))) hw3.1 hw3.2
        refine ⟨fun p => ![ι₁, ι₂, ι₃] (p 0) (Fin.tail p), ?_⟩
        rw [p426_tree_comb]
        unfold p426_werr
        simp only [p426_ind_maj]
        exact p426_core w _ _ _ hw0 (hcases _) (hcases _) (hcases _) _ hb0 hβ'2 he1 hι₁ hι₂
          (Or.inr hι₃)

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_base {X : Type*} [MeasurableSpace X] {m N : ℕ}
    (L : (Fin m → X × Bool) → X → Bool)
    (hL : Measurable (fun p : (Fin m → X × Bool) × X ↦ L p.1 p.2)) (c : X → Bool)
    (hc : Measurable c) (γ δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hwk : ∀ D : Measure X, IsProbabilityMeasure D →
      sampleLaw D c m {S | 1 / 2 - γ < errorOf D c (L S)} ≤ ENNReal.ofReal (1 - δ₀))
    (S : Fin N → X × Bool) (hS : ∀ j, (S j).2 = c (S j).1)
    (w : Fin N → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) :
    ∃ τ : Fin m → Fin N, p426_werr S w (L (fun i => S (τ i))) ≤ 1 / 2 - γ := by
  classical
  by_contra hcon
  push Not at hcon
  have hLx : ∀ S', Measurable (L S') := fun S' => Measurable.of_uncurry_left (f := L) hL
  set ν : Measure (Fin N) := ∑ j, ENNReal.ofReal (w j) • Measure.dirac j with hν
  have hνapp : ∀ s : Set (Fin N), ν s = ENNReal.ofReal (∑ j, if j ∈ s then w j else 0) := by
    intro s
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by split_ifs <;> linarith [hw0 j])]
    rw [hν, Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
    by_cases hj : j ∈ s <;> simp [hj]
  have hνP : IsProbabilityMeasure ν := ⟨by rw [hνapp]; simp [hw1]⟩
  have hxs : Measurable (fun j : Fin N => (S j).1) := measurable_of_finite _
  have hpair : Measurable (fun x : X => (x, c x)) := measurable_id.prodMk hc
  set P : Measure X := ν.map (fun j => (S j).1) with hP
  have : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map hxs.aemeasurable
  have herr : ∀ h : X → Bool, Measurable h → errorOf P c h = p426_werr S w h := by
    intro h hh
    have hmeas : MeasurableSet {x | h x ≠ c x} := (measurableSet_eq_fun hh hc).compl
    unfold errorOf
    rw [hP, Measure.map_apply hxs hmeas, hνapp, ENNReal.toReal_ofReal
      (Finset.sum_nonneg (fun j _ => by split_ifs <;> linarith [hw0 j]))]
    unfold p426_werr p426_ind
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hS j]
    by_cases hh' : h (S j).1 = c (S j).1 <;> simp [hh']
  have hmapS : Measurable S := measurable_of_finite _
  have hsl : sampleLaw P c m = (Measure.pi (fun _ : Fin m => ν)).map (fun τ i => S (τ i)) := by
    have h1 : exampleLaw P c = ν.map S := by
      unfold exampleLaw
      rw [hP, Measure.map_map hpair hxs]
      congr 1
      funext j
      exact Prod.ext rfl (hS j).symm
    unfold sampleLaw
    rw [h1]
    exact (Measure.pi_map_pi (μ := fun _ : Fin m => ν) (f := fun _ => S)
      (fun _ => hmapS.aemeasurable)).symm
  have hB := hwk P inferInstance
  have hpre : (fun τ : Fin m → Fin N => fun i => S (τ i)) ⁻¹'
      {S' | 1 / 2 - γ < errorOf P c (L S')} = Set.univ := by
    ext τ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    rw [herr _ (hLx _)]
    exact hcon τ
  have hle := Measure.le_map_apply (μ := Measure.pi (fun _ : Fin m => ν))
    (measurable_of_finite (fun τ : Fin m → Fin N => fun i => S (τ i))).aemeasurable
    {S' | 1 / 2 - γ < errorOf P c (L S')}
  rw [hpre, measure_univ, ← hsl] at hle
  have hlt : ENNReal.ofReal (1 - δ₀) < 1 := by
    rw [ENNReal.ofReal_lt_one]; linarith
  exact absurd (hle.trans hB) (not_le.2 hlt)

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_gen {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (c : X → Bool) (hc : Measurable c) {N : ℕ} (p : Fin N → Prop) [DecidablePred p]
    (φ : (Subtype p → X × Bool) → X → Bool)
    (hφ : Measurable (fun z : (Subtype p → X × Bool) × X ↦ φ z.1 z.2)) (ε : ℝ) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (n : ℕ) (hn : n ≤ Fintype.card {j // ¬ p j}) :
    sampleLaw D c N {S | ε < errorOf D c (φ (fun j => S j)) ∧
        ∀ j, ¬ p j → φ (fun j => S j) (S j).1 = (S j).2}
      ≤ ENNReal.ofReal ((1 - ε) ^ n) := by
  have hpair : Measurable (fun x : X => (x, c x)) := measurable_id.prodMk hc
  have hEx : IsProbabilityMeasure (exampleLaw D c) :=
    Measure.isProbabilityMeasure_map hpair.aemeasurable
  have hφu : ∀ u, Measurable (φ u) := fun u => Measurable.of_uncurry_left (f := φ) hφ
  set G : Set (Subtype p → X × Bool) := {u | ε < errorOf D c (φ u)} with hG
  have hGm : MeasurableSet G := by
    have hW : MeasurableSet {z : (Subtype p → X × Bool) × X | φ z.1 z.2 ≠ c z.2} :=
      (measurableSet_eq_fun hφ (hc.comp measurable_snd)).compl
    have hf : Measurable (fun u : Subtype p → X × Bool =>
        D (Prod.mk u ⁻¹' {z : (Subtype p → X × Bool) × X | φ z.1 z.2 ≠ c z.2})) :=
      measurable_measure_prodMk_left hW
    exact measurableSet_lt measurable_const (ENNReal.measurable_toReal.comp hf)
  set E : Set ((Subtype p → X × Bool) × ({j // ¬ p j} → X × Bool)) :=
    Prod.fst ⁻¹' G ∩ {z | ∀ j, φ z.1 (z.2 j).1 = (z.2 j).2} with hE
  have hEm : MeasurableSet E := by
    refine (measurable_fst hGm).inter ?_
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter (fun j => measurableSet_eq_fun ?_ ?_)
    · exact hφ.comp (measurable_fst.prodMk
        (measurable_fst.comp ((measurable_pi_apply j).comp measurable_snd)))
    · exact measurable_snd.comp ((measurable_pi_apply j).comp measurable_snd)
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin N => exampleLaw D c) p
  have hsub : {S : Fin N → X × Bool | ε < errorOf D c (φ (fun j => S j)) ∧
        ∀ j, ¬ p j → φ (fun j => S j) (S j).1 = (S j).2} ⊆
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => X × Bool) p) ⁻¹' E := by
    rintro S ⟨h1, h2⟩
    exact ⟨h1, fun j => h2 j j.2⟩
  unfold sampleLaw
  refine (measure_mono hsub).trans ?_
  rw [hmp.measure_preimage_equiv, Measure.prod_apply hEm]
  have hsec : ∀ u : Subtype p → X × Bool,
      Measure.pi (fun _ : {j // ¬ p j} => exampleLaw D c) (Prod.mk u ⁻¹' E) ≤
        ENNReal.ofReal ((1 - ε) ^ n) := by
    intro u
    by_cases hu : u ∈ G
    · have hset : Prod.mk u ⁻¹' E = Set.univ.pi (fun _ => {y : X × Bool | φ u y.1 = y.2}) := by
        ext v
        simp [hE, hu, Set.mem_pi]
      rw [hset, Measure.pi_pi]
      have hy : exampleLaw D c {y : X × Bool | φ u y.1 = y.2} ≤ ENNReal.ofReal (1 - ε) := by
        have hm1 : MeasurableSet {y : X × Bool | φ u y.1 = y.2} :=
          measurableSet_eq_fun ((hφu u).comp measurable_fst) measurable_snd
        unfold exampleLaw
        rw [Measure.map_apply hpair hm1]
        have hpre : (fun x : X => (x, c x)) ⁻¹' {y : X × Bool | φ u y.1 = y.2} =
            {x | φ u x ≠ c x}ᶜ := by
          ext x; simp
        have hne : MeasurableSet {x | φ u x ≠ c x} := (measurableSet_eq_fun (hφu u) hc).compl
        rw [hpre, prob_compl_eq_one_sub hne]
        have h1 : ENNReal.ofReal ε ≤ D {x | φ u x ≠ c x} := by
          have hu' : ε < (D {x | φ u x ≠ c x}).toReal := hu
          rw [← ENNReal.ofReal_toReal (measure_ne_top D {x | φ u x ≠ c x})]
          exact ENNReal.ofReal_le_ofReal hu'.le
        calc 1 - D {x | φ u x ≠ c x} ≤ 1 - ENNReal.ofReal ε := tsub_le_tsub_left h1 _
          _ = ENNReal.ofReal (1 - ε) := by rw [ENNReal.ofReal_sub 1 hε, ENNReal.ofReal_one]
      calc ∏ i : {j // ¬ p j}, exampleLaw D c {y : X × Bool | φ u y.1 = y.2}
          ≤ ENNReal.ofReal (1 - ε) ^ (Finset.univ : Finset {j // ¬ p j}).card :=
            Finset.prod_le_pow_card _ _ _ (fun i _ => hy)
        _ = ENNReal.ofReal ((1 - ε) ^ Fintype.card {j // ¬ p j}) := by
            rw [Finset.card_univ, ENNReal.ofReal_pow (by linarith)]
        _ ≤ ENNReal.ofReal ((1 - ε) ^ n) :=
            ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one (by linarith) (by linarith) hn)
    · have hset : Prod.mk u ⁻¹' E = ∅ := by
        ext v
        simp [hE, hu]
      rw [hset, measure_empty]
      exact zero_le
  calc ∫⁻ u, Measure.pi (fun _ : {j // ¬ p j} => exampleLaw D c) (Prod.mk u ⁻¹' E)
        ∂(Measure.pi fun _ : Subtype p => exampleLaw D c)
      ≤ ∫⁻ _u, ENNReal.ofReal ((1 - ε) ^ n)
        ∂(Measure.pi fun _ : Subtype p => exampleLaw D c) := lintegral_mono hsec
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_consistent {X : Type*} {N : ℕ} (S : Fin N → X × Bool) (h : X → Bool) (x : ℝ)
    (hN : 0 < N) (hw : p426_werr S (fun _ => 1 / (N : ℝ)) h ≤ x) (hx : (N : ℝ) * x < 1) :
    ∀ j, h (S j).1 = (S j).2 := by
  intro j
  by_contra hj
  have hind : p426_ind S h j = 1 := by simp [p426_ind, hj]
  have hsum : 1 ≤ ∑ i, p426_ind S h i := by
    calc (1 : ℝ) = p426_ind S h j := hind.symm
      _ ≤ ∑ i, p426_ind S h i :=
        Finset.single_le_sum (fun i _ => p426_ind_nonneg S h i) (Finset.mem_univ j)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : p426_werr S (fun _ => 1 / (N : ℝ)) h = (∑ i, p426_ind S h i) / N := by
    unfold p426_werr
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [heq, div_le_iff₀ hNr] at hw
  nlinarith

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_k0 (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 1 / 2) :
    ∃ k₀ : ℕ, boostFun^[k₀] β ≤ 1 / 6 := by
  set η : ℝ := (1 - 2 * β) / 12 with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  have claim : ∀ k : ℕ, boostFun^[k] β ≤ 1 / 6 ∨ boostFun^[k] β ≤ β - k * η := by
    intro k
    induction k with
    | zero => right; simp
    | succ k ih =>
      obtain ⟨h0, h1⟩ := p426_iter_bounds β hβ0 hβ k
      rw [Function.iterate_succ_apply']
      set x := boostFun^[k] β with hx
      have hg : boostFun x = x - x * (1 - x) * (1 - 2 * x) := by unfold boostFun; ring
      have hx2 : x < 1 / 2 := lt_of_le_of_lt h1 hβ
      have hnn : 0 ≤ x * (1 - x) * (1 - 2 * x) :=
        mul_nonneg (mul_nonneg h0 (by linarith)) (by linarith)
      by_cases hx6 : x ≤ 1 / 6
      · left; rw [hg]; linarith
      · right
        push Not at hx6
        rcases ih with ih | ih
        · exact absurd ih (not_le.2 hx6)
        · have ha : 1 / 12 ≤ x * (1 - x) := by nlinarith
          have hb : 1 - 2 * β ≤ 1 - 2 * x := by linarith
          have hc : 1 / 12 * (1 - 2 * β) ≤ x * (1 - x) * (1 - 2 * x) :=
            mul_le_mul ha hb (by linarith) (mul_nonneg h0 (by linarith))
          rw [hg]
          push_cast
          have : η = 1 / 12 * (1 - 2 * β) := by rw [hη]; ring
          nlinarith
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (β / η)
  refine ⟨k₀, ?_⟩
  rcases claim k₀ with h | h
  · exact h
  · exfalso
    have h0 := (p426_iter_bounds β hβ0 hβ k₀).1
    have : β < k₀ * η := by rwa [div_lt_iff₀ hηpos] at hk₀
    linarith

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_double (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 1 / 2) (k₀ : ℕ)
    (hk₀ : boostFun^[k₀] β ≤ 1 / 6) :
    ∀ j : ℕ, 3 * boostFun^[k₀ + j] β ≤ (1 / 2) ^ (2 ^ j) := by
  intro j
  induction j with
  | zero => simp; linarith
  | succ j ih =>
    rw [← add_assoc, Function.iterate_succ_apply']
    have h0 := (p426_iter_bounds β hβ0 hβ (k₀ + j)).1
    set x := boostFun^[k₀ + j] β
    have hg : 3 * boostFun x ≤ (3 * x) ^ 2 := by
      unfold boostFun; nlinarith [pow_nonneg h0 3]
    calc 3 * boostFun x ≤ (3 * x) ^ 2 := hg
      _ ≤ ((1 / 2) ^ (2 ^ j)) ^ 2 := pow_le_pow_left₀ (by linarith) ih 2
      _ = (1 / 2) ^ (2 ^ (j + 1)) := by rw [← pow_mul, pow_succ]

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_growth (C : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) :
    ∃ j : ℕ, ((2 : ℝ) ^ (2 ^ j)) ^ (C * 3 ^ j) * (1 - ε) ^ (2 ^ (2 ^ j) - C * 3 ^ j) ≤ δ := by
  set K : ℝ := 2 * ((C : ℝ) + 1) with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  have h1 : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ 3 / 2 ^ n < ε / (2 * K) :=
    (tendsto_pow_const_div_const_pow_of_one_lt 3 one_lt_two).eventually
      (Iio_mem_nhds (by positivity))
  have h2 : ∀ᶠ n : ℕ in Filter.atTop, 2 * |Real.log δ| / ε ≤ (2 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).eventually_ge_atTop _
  have h3 : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ n := Filter.eventually_ge_atTop 1
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨n₀, ?_⟩
  have hnn : n₀ ≤ 2 ^ n₀ := Nat.lt_two_pow_self.le
  obtain ⟨hA, hB, hC⟩ := hn₀ (2 ^ n₀) hnn
  set n : ℕ := 2 ^ n₀ with hn
  set a : ℕ := C * 3 ^ n₀ with ha
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hC
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hA' : K * (n : ℝ) ^ 3 < ε / 2 * 2 ^ n := by
    rw [div_lt_iff₀ hpow] at hA
    have := mul_lt_mul_of_pos_left hA hKpos
    calc K * (n : ℝ) ^ 3 < K * (ε / (2 * K) * 2 ^ n) := this
      _ = ε / 2 * 2 ^ n := by field_simp
  have hB' : |Real.log δ| ≤ ε / 2 * 2 ^ n := by
    rw [div_le_iff₀ hε] at hB; linarith
  have h3n : (3 : ℝ) ^ n₀ ≤ (n : ℝ) ^ 2 := by
    have : ((n : ℕ) : ℝ) ^ 2 = 4 ^ n₀ := by
      rw [hn]; push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) n₀
  have har : (a : ℝ) ≤ C * (n : ℝ) ^ 2 := by
    rw [ha]; push_cast
    exact mul_le_mul_of_nonneg_left h3n (by positivity)
  have hn23 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := pow_le_pow_right₀ hnr (by norm_num)
  have hCK : 2 * (C : ℝ) * (n : ℝ) ^ 3 ≤ K * (n : ℝ) ^ 3 := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [hK]; linarith
  have hCn : (C : ℝ) * (n : ℝ) ^ 2 ≤ C * (n : ℝ) ^ 3 :=
    mul_le_mul_of_nonneg_left hn23 (by positivity)
  have hε2n : ε / 2 * (2 : ℝ) ^ n ≤ 2 ^ n := by nlinarith
  have hn3 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  have hale : a ≤ 2 ^ n := by
    have : (a : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast this
  have hexp1 : ((2 : ℝ) ^ n) ^ a ≤ Real.exp ((n : ℝ) * a) := by
    rw [← pow_mul]
    calc (2 : ℝ) ^ (n * a) ≤ (Real.exp 1) ^ (n * a) :=
          pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp 1]) _
      _ = Real.exp ((n : ℝ) * a) := by
          rw [← Real.exp_nat_mul, mul_one, Nat.cast_mul]
  have hexp2 : (1 - ε) ^ (2 ^ n - a) ≤ Real.exp (((2 : ℝ) ^ n - a) * (-ε)) := by
    have hc : (((2 ^ n - a : ℕ)) : ℝ) = (2 : ℝ) ^ n - a := by
      rw [Nat.cast_sub hale]; norm_num
    rw [← hc, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-ε)]) _
  calc ((2 : ℝ) ^ n) ^ a * (1 - ε) ^ (2 ^ n - a)
      ≤ Real.exp ((n : ℝ) * a) * Real.exp (((2 : ℝ) ^ n - a) * (-ε)) :=
        mul_le_mul hexp1 hexp2 (pow_nonneg (by linarith) _) (Real.exp_pos _).le
    _ = Real.exp ((n : ℝ) * a + ((2 : ℝ) ^ n - a) * (-ε)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (Real.log δ) := by
        apply Real.exp_le_exp.2
        have ha0 : (0 : ℝ) ≤ a := by positivity
        have hna : (n : ℝ) * a ≤ C * (n : ℝ) ^ 3 := by
          calc (n : ℝ) * a ≤ n * (C * n ^ 2) := mul_le_mul_of_nonneg_left har (by positivity)
            _ = C * n ^ 3 := by ring
        have hea0 : ε * a ≤ a := by nlinarith
        have hexpand : (n : ℝ) * a + ((2 : ℝ) ^ n - a) * (-ε) =
            n * a + ε * a - ε * 2 ^ n := by ring
        rw [hexpand]
        have := neg_abs_le (Real.log δ)
        linarith
    _ = δ := Real.exp_log hδ

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem p426_numeric (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 1 / 2) (m : ℕ) (ε δ : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hδ : 0 < δ) :
    ∃ k N : ℕ, 0 < N ∧ (N : ℝ) * boostFun^[k] β < 1 ∧
      ((N : ℝ) ^ m) ^ (3 ^ k) * (1 - ε) ^ (N - 3 ^ k * m) ≤ δ := by
  obtain ⟨k₀, hk₀⟩ := p426_k0 β hβ0 hβ
  obtain ⟨j, hj⟩ := p426_growth (3 ^ k₀ * m) ε δ hε hε1 hδ
  refine ⟨k₀ + j, 2 ^ (2 ^ j), by positivity, ?_, ?_⟩
  · have hd := p426_double β hβ0 hβ k₀ hk₀ j
    push_cast
    have h1 : (2 : ℝ) ^ (2 ^ j) * (1 / 2) ^ (2 ^ j) = 1 := by rw [← mul_pow]; norm_num
    have hpos : (0 : ℝ) < 2 ^ (2 ^ j) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hd hpos.le]
  · have e1 : 3 ^ (k₀ + j) * m = 3 ^ k₀ * m * 3 ^ j := by ring
    have e2 : m * 3 ^ (k₀ + j) = 3 ^ k₀ * m * 3 ^ j := by ring
    push_cast
    rw [← pow_mul, e2, e1]
    exact hj

open MeasureTheory ProbabilityTheory ComputationalLearning in
theorem solution {X : Type*} [MeasurableSpace X] (C H : Set (X → Bool))
    (hH : ∀ h ∈ H, Measurable h) (hweak : WeaklyLearnable C H) :
    PACLearnable C (majorityTrees H) := by
  classical
  have _hHm := hH
  obtain ⟨γ, δ₀, m, L, hγ, hδ₀, hLH, hLm, hwk⟩ := hweak
  intro ε δ hε hε2 hδ _hδ2
  have hβ0 : (0 : ℝ) ≤ max (1 / 2 - γ) 0 := le_max_right _ _
  have hβ : max (1 / 2 - γ) 0 < 1 / 2 := max_lt (by linarith) (by norm_num)
  obtain ⟨k, N, hN, hkN, hnum⟩ := p426_numeric _ hβ0 hβ m ε δ hε (by linarith) hδ
  have : Nonempty ((Fin k → Fin 3) → Fin m → Fin N) := ⟨fun _ _ => ⟨0, hN⟩⟩
  refine ⟨N, fun S => p426_tree L k (fun q i => S (Classical.epsilon
      (fun ι : (Fin k → Fin 3) → Fin m → Fin N =>
        ∀ j, p426_tree L k (fun q i => S (ι q i)) (S j).1 = (S j).2) q i)),
    fun S => p426_tree_mem H L hLH k _, ?_⟩
  intro c hcC hc D hD
  have hpair : Measurable (fun x : X => (x, c x)) := measurable_id.prodMk hc
  have hEx : IsProbabilityMeasure (exampleLaw D c) :=
    Measure.isProbabilityMeasure_map hpair.aemeasurable
  have hcons : ∀ S : Fin N → X × Bool, (∀ j, (S j).2 = c (S j).1) →
      ∃ ι : (Fin k → Fin 3) → Fin m → Fin N,
        ∀ j, p426_tree L k (fun q i => S (ι q i)) (S j).1 = (S j).2 := by
    intro S hS
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    obtain ⟨ι, hι⟩ := p426_exists L S _ hβ0 hβ
      (fun w hw0 hw1 => (p426_base L hLm c hc γ δ₀ hδ₀ (fun D' hD' => hwk c hcC hc D' hD')
        S hS w hw0 hw1).imp fun τ hτ => hτ.trans (le_max_left _ _))
      k (fun _ => 1 / (N : ℝ)) (fun _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp)
    exact ⟨ι, p426_consistent S _ _ hN hι hkN⟩
  set A : ((Fin k → Fin 3) → Fin m → Fin N) → Set (Fin N → X × Bool) := fun ι =>
    {S | ε < errorOf D c (p426_tree L k (fun q i => S (ι q i))) ∧
      ∀ j, p426_tree L k (fun q i => S (ι q i)) (S j).1 = (S j).2} with hA_def
  have hsub : {S : Fin N → X × Bool | ε < errorOf D c (p426_tree L k (fun q i => S
      (Classical.epsilon (fun ι : (Fin k → Fin 3) → Fin m → Fin N =>
        ∀ j, p426_tree L k (fun q i => S (ι q i)) (S j).1 = (S j).2) q i)))} ⊆
      {S | ∃ j, (S j).2 ≠ c (S j).1} ∪ ⋃ ι, A ι := by
    intro S hS
    by_cases hlab : ∀ j, (S j).2 = c (S j).1
    · right
      exact Set.mem_iUnion.2 ⟨_, hS, Classical.epsilon_spec (hcons S hlab)⟩
    · left
      push Not at hlab
      exact hlab
  have hA : ∀ ι, sampleLaw D c N (A ι) ≤ ENNReal.ofReal ((1 - ε) ^ (N - 3 ^ k * m)) := by
    intro ι
    have ht := p426_tree_meas L hLm k
    have h1 : Measurable (fun z : ({j // ∃ q i, ι q i = j} → X × Bool) × X =>
        ((fun q i => z.1 ⟨ι q i, q, i, rfl⟩ : (Fin k → Fin 3) → Fin m → X × Bool), z.2)) :=
      (measurable_pi_lambda _ (fun q => measurable_pi_lambda _
        (fun i => (measurable_pi_apply _).comp measurable_fst))).prodMk measurable_snd
    have hgen := p426_gen D c hc (fun j => ∃ q i, ι q i = j)
      (fun u => p426_tree L k (fun q i => u ⟨ι q i, q, i, rfl⟩)) (ht.comp h1) ε hε.le
      (by linarith) (N - 3 ^ k * m) (by
        rw [Fintype.card_subtype_compl, Fintype.card_fin]
        have key : Fintype.card {j // ∃ q i, ι q i = j} ≤ 3 ^ k * m := by
          have hs := Fintype.card_le_of_surjective
            (fun qi : (Fin k → Fin 3) × Fin m =>
              (⟨ι qi.1 qi.2, qi.1, qi.2, rfl⟩ : {j // ∃ q i, ι q i = j}))
            (by rintro ⟨j, q, i, rfl⟩; exact ⟨(q, i), rfl⟩)
          simpa [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] using hs
        convert Nat.sub_le_sub_left key N using 2)
    refine (measure_mono ?_).trans hgen
    rintro S ⟨h1, h2⟩
    exact ⟨h1, fun j _ => h2 j⟩
  have hbad0 : sampleLaw D c N {S : Fin N → X × Bool | ∃ j, (S j).2 ≠ c (S j).1} = 0 := by
    have hset : {S : Fin N → X × Bool | ∃ j, (S j).2 ≠ c (S j).1} =
        ⋃ j, (fun S : Fin N → X × Bool => S j) ⁻¹' {y : X × Bool | y.2 ≠ c y.1} := by
      ext S; simp
    rw [hset]
    refine measure_iUnion_null (fun j => ?_)
    unfold sampleLaw
    apply Measure.pi_eval_preimage_null
    have hm : MeasurableSet {y : X × Bool | y.2 ≠ c y.1} :=
      (measurableSet_eq_fun measurable_snd (hc.comp measurable_fst)).compl
    unfold exampleLaw
    rw [Measure.map_apply hpair hm]
    simp
  refine (measure_mono hsub).trans ?_
  calc sampleLaw D c N ({S | ∃ j, (S j).2 ≠ c (S j).1} ∪ ⋃ ι, A ι)
      ≤ sampleLaw D c N {S | ∃ j, (S j).2 ≠ c (S j).1} + sampleLaw D c N (⋃ ι, A ι) :=
        measure_union_le _ _
    _ ≤ 0 + ∑ ι : (Fin k → Fin 3) → Fin m → Fin N,
          ENNReal.ofReal ((1 - ε) ^ (N - 3 ^ k * m)) := by
        rw [hbad0]
        exact add_le_add le_rfl ((measure_iUnion_fintype_le _ _).trans
          (Finset.sum_le_sum fun ι _ => hA ι))
    _ = ENNReal.ofReal (((N : ℝ) ^ m) ^ (3 ^ k) * (1 - ε) ^ (N - 3 ^ k * m)) := by
        rw [zero_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [Fintype.card_fun, Fintype.card_fin]
        rw [← ENNReal.ofReal_natCast]
        congr 1
        push_cast
        ring
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hnum
