-- Prove2me | solution 1 for BalancedPrices.WeakExtension.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T22:48:06.844337+00:00
-- url     : https://prove2.me/submissions/30cda6dc-5a04-4354-b577-cdf871a8ea2e

import Mathlib
import Definitions.Def_BalancedPrices_WeakExtension_Model
import Definitions.Def_BalancedPrices_Extension_Mechanism

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace BP435

open BalancedPrices.Extension

lemma run_eq {n : ℕ} {X V : Fin n → Type*} (nul : Outcome X)
    (choice : ∀ i, V i → Outcome X → X i) (v : ∀ i, V i) (i : Fin n) :
    run nul choice v i = choice i (v i) (pre nul (run nul choice v) i) := by
  rw [run]
  congr 1
  funext j
  simp [pre, restrictTo]

lemma run_congr {n : ℕ} {X V : Fin n → Type*} (nul : Outcome X)
    (choice : ∀ i, V i → Outcome X → X i) (v v' : ∀ i, V i) :
    ∀ (m : ℕ) (i : Fin n), i.val = m → (∀ k : Fin n, k ≤ i → v k = v' k) →
      run nul choice v i = run nul choice v' i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i hi h
    rw [run_eq, run_eq, h i le_rfl]
    congr 1
    funext j
    simp only [pre, restrictTo, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with hj
    · exact ih j.val (by have := Fin.lt_def.mp hj; omega) j rfl
        (fun k hk => h k (le_trans hk hj.le))
    · rfl

lemma pre_run_update {n : ℕ} {X V : Fin n → Type*} (nul : Outcome X)
    (choice : ∀ i, V i → Outcome X → X i) (v : ∀ i, V i) (i : Fin n) (a : V i) :
    pre nul (run nul choice (Function.update v i a)) i = pre nul (run nul choice v) i := by
  funext j
  simp only [pre, restrictTo, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with hj
  · exact run_congr nul choice _ _ j.val j rfl (fun k hk => by
      rw [Function.update_of_ne (ne_of_lt (lt_of_le_of_lt hk hj))])
  · rfl

lemma welfare_bd {n : ℕ} {X V : Fin n → Type*} (val : ∀ i, V i → X i → ℝ)
    (hval : ∀ i w xi, 0 ≤ val i w xi ∧ val i w xi ≤ 1) (w : ∀ i, V i) (y : Outcome X) :
    0 ≤ welfare (prof val w) y ∧ welfare (prof val w) y ≤ n := by
  unfold welfare prof
  constructor
  · exact Finset.sum_nonneg fun i _ => (hval i (w i) (y i)).1
  · calc ∑ i, val i (w i) (y i) ≤ ∑ _i : Fin n, (1:ℝ) :=
          Finset.sum_le_sum fun i _ => (hval i (w i) (y i)).2
      _ = n := by simp

lemma opt_bd {n : ℕ} {X V : Fin n → Type*} (val : ∀ i, V i → X i → ℝ)
    (hval : ∀ i w xi, 0 ≤ val i w xi ∧ val i w xi ≤ 1) (w : ∀ i, V i) (S : Set (Outcome X)) :
    0 ≤ optVal (prof val w) S ∧ optVal (prof val w) S ≤ n := by
  unfold optVal
  constructor
  · apply Real.sSup_nonneg
    rintro _ ⟨y, -, rfl⟩
    exact (welfare_bd val hval w y).1
  · apply Real.sSup_le
    · rintro _ ⟨y, -, rfl⟩
      exact (welfare_bd val hval w y).2
    · exact Nat.cast_nonneg n

lemma intB {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Countable Ω]
    (m : Measure Ω) [IsFiniteMeasure m] (f : Ω → ℝ) (lo hi : ℝ)
    (h : ∀ x, lo ≤ f x ∧ f x ≤ hi) : Integrable f m := by
  refine Integrable.of_bound StronglyMeasurable.of_discrete.aestronglyMeasurable (|lo| + |hi|)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have := h x
  constructor <;> linarith [neg_abs_le lo, le_abs_self hi, abs_nonneg lo, abs_nonneg hi]

lemma int_le_lint {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Countable Ω]
    (m : Measure Ω) (g : Ω → ℝ) (hg : Integrable g m) :
    ∫ x, g x ∂m ≤ (∫⁻ x, ENNReal.ofReal (g x) ∂m).toReal := by
  have h1 : ∫ x, g x ∂m ≤ ∫ x, max (g x) 0 ∂m :=
    integral_mono hg hg.pos_part (fun x => le_max_left _ _)
  have h2 : ∫ x, max (g x) 0 ∂m = (∫⁻ x, ENNReal.ofReal (max (g x) 0) ∂m).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => le_max_right _ _)
      StronglyMeasurable.of_discrete.aestronglyMeasurable
  have h3 : (fun x => ENNReal.ofReal (max (g x) 0)) = fun x => ENNReal.ofReal (g x) := by
    funext x
    rcases le_total (g x) 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
    · rw [max_eq_left h]
  rw [h2, h3] at h1
  exact h1

lemma int_fst {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Countable Ω]
    (m m' : Measure Ω) [IsProbabilityMeasure m] [IsProbabilityMeasure m'] (f : Ω → ℝ)
    (lo hi : ℝ) (h : ∀ x, lo ≤ f x ∧ f x ≤ hi) :
    ∫ p, f p.1 ∂(m.prod m') = ∫ x, f x ∂m := by
  rw [integral_prod _ (intB _ _ lo hi (fun p => h p.1))]
  simp

def sw {n : ℕ} {V : Fin n → Type*} (i : Fin n) (p : (∀ j, V j) × (∀ j, V j)) :
    (∀ j, V j) × (∀ j, V j) :=
  (Function.update p.1 i (p.2 i), Function.update p.2 i (p.1 i))

lemma sw_sw {n : ℕ} {V : Fin n → Type*} (i : Fin n) (p : (∀ j, V j) × (∀ j, V j)) :
    sw i (sw i p) = p := by
  obtain ⟨a, b⟩ := p
  simp [sw]

def swapE {n : ℕ} {V : Fin n → Type*} [∀ i, MeasurableSpace (V i)]
    [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)] (i : Fin n) :
    ((∀ j, V j) × (∀ j, V j)) ≃ᵐ ((∀ j, V j) × (∀ j, V j)) where
  toFun := sw i
  invFun := sw i
  left_inv := sw_sw i
  right_inv := sw_sw i
  measurable_toFun := Measurable.of_discrete
  measurable_invFun := Measurable.of_discrete

lemma swapE_apply {n : ℕ} {V : Fin n → Type*} [∀ i, MeasurableSpace (V i)]
    [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)] (i : Fin n)
    (p : (∀ j, V j) × (∀ j, V j)) : swapE i p = sw i p := rfl

lemma map_sw {n : ℕ} {V : Fin n → Type*} [∀ i, MeasurableSpace (V i)]
    [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)]
    (μ : ∀ i, Measure (V i)) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n) :
    ((Measure.pi μ).prod (Measure.pi μ)).map (swapE i) = (Measure.pi μ).prod (Measure.pi μ) := by
  rw [Measure.ext_iff_singleton]
  rintro ⟨a, b⟩
  rw [Measure.map_apply (swapE i).measurable (measurableSet_singleton _)]
  have hpre : (swapE i) ⁻¹' {(a, b)} = {sw i (a, b)} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, swapE_apply]
    constructor
    · intro h
      rw [← h, sw_sw]
    · rintro rfl
      exact sw_sw i (a, b)
  rw [hpre]
  simp only [sw]
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, ← Set.singleton_prod_singleton,
    Measure.prod_prod, Measure.pi_singleton, Measure.pi_singleton, Measure.pi_singleton,
    Measure.pi_singleton, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  by_cases h : j = i
  · subst h
    simp [mul_comm]
  · simp [Function.update_of_ne h]

lemma int_sw {n : ℕ} {V : Fin n → Type*} [∀ i, MeasurableSpace (V i)]
    [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)]
    (μ : ∀ i, Measure (V i)) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n)
    (f : (∀ j, V j) × (∀ j, V j) → ℝ) :
    ∫ p, f p ∂((Measure.pi μ).prod (Measure.pi μ)) =
      ∫ p, f (sw i p) ∂((Measure.pi μ).prod (Measure.pi μ)) := by
  have := integral_map_equiv (μ := (Measure.pi μ).prod (Measure.pi μ)) (swapE i) f
  rw [map_sw] at this
  exact this

lemma arith (α β₁ β₂ A H U R : ℝ) (hα : 0 < α) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (hsum : 1 / α ≤ β₁ + β₂) (hA : 0 ≤ A) (hU0 : 0 ≤ U)
    (hU : H - 1 / (β₁ + max (2 * β₂) (1 / α)) * (β₁ * H + β₂ * A) ≤ U)
    (hR : 1 / (β₁ + max (2 * β₂) (1 / α)) / α * (A - H) ≤ R) :
    1 / (α * (2 * β₁ + 4 * β₂)) * A ≤ U + R := by
  have hia : 0 < 1 / α := by positivity
  have hsum' : 1 ≤ α * β₁ + α * β₂ := by
    rw [div_le_iff₀ hα] at hsum; nlinarith
  rcases le_total (1 / α) (2 * β₂) with h | h
  · rw [max_eq_left h] at hU hR
    have h' : 1 ≤ 2 * α * β₂ := by rw [div_le_iff₀ hα] at h; nlinarith
    have hb : 0 < β₂ := by linarith
    have hD : 0 < β₁ + 2 * β₂ := by linarith
    have hD' : β₁ + 2 * β₂ ≠ 0 := hD.ne'
    have hab : 0 < α * β₂ := mul_pos hα hb
    have hp : 0 < 2 * β₁ + 4 * β₂ := by linarith
    have hp' : 2 * β₁ + 4 * β₂ ≠ 0 := hp.ne'
    set l := 1 / (2 * α * β₂) with hl
    have hl0 : 0 ≤ l := by positivity
    have hl1 : l ≤ 1 := by
      rw [hl, div_le_one (by positivity)]
      exact h'
    have hU' : l * (H - 1 / (β₁ + 2 * β₂) * (β₁ * H + β₂ * A)) ≤ U := by
      calc _ ≤ l * U := mul_le_mul_of_nonneg_left hU hl0
        _ ≤ 1 * U := mul_le_mul_of_nonneg_right hl1 hU0
        _ = U := one_mul U
    have key : l * (H - 1 / (β₁ + 2 * β₂) * (β₁ * H + β₂ * A)) +
        1 / (β₁ + 2 * β₂) / α * (A - H) = 1 / (α * (2 * β₁ + 4 * β₂)) * A := by
      rw [hl]
      have ha : α ≠ 0 := hα.ne'
      have hb' : β₂ ≠ 0 := hb.ne'
      field_simp
      ring
    linarith
  · rw [max_eq_right h] at hU hR
    have h2 : 2 * (α * β₂) ≤ 1 := by rw [le_div_iff₀ hα] at h; nlinarith
    have hq : 0 < α * β₁ + 1 := by nlinarith
    have ha : α ≠ 0 := hα.ne'
    have hq' : α * β₁ + 1 ≠ 0 := hq.ne'
    have hδe : 1 / (β₁ + 1 / α) = α / (α * β₁ + 1) := by
      field_simp
    rw [hδe] at hU hR
    have key : (H - α / (α * β₁ + 1) * (β₁ * H + β₂ * A)) + α / (α * β₁ + 1) / α * (A - H)
        = (1 - α * β₂) / (α * β₁ + 1) * A := by
      field_simp
      ring
    have hc : 1 / (α * (2 * β₁ + 4 * β₂)) ≤ (1 - α * β₂) / (α * β₁ + 1) := by
      have hp : 0 < α * (2 * β₁ + 4 * β₂) := by nlinarith
      have hb0 : 0 ≤ α * β₂ := mul_nonneg hα.le hβ₂
      rw [div_le_div_iff₀ hp hq]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - 2 * (α * β₂))
        (by linarith : (0:ℝ) ≤ α * β₁ - 1 + 2 * (α * β₂))]
    have := mul_le_mul_of_nonneg_right hc hA
    linarith

open BalancedPrices.WeakExtension

noncomputable def pp {n : ℕ} {X V : Fin n → Type*} [∀ i, MeasurableSpace (V i)] (δ : ℝ)
    (μ : ∀ i, Measure (V i)) (pv : (∀ i, V i) → PriceRule X) : PriceRule X :=
  fun i xi y => ENNReal.ofReal δ * expPrice μ pv i xi y

set_option maxHeartbeats 1000000 in
lemma main {n : ℕ} {X V : Fin n → Type*}
    [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)]
    (μ : ∀ i, Measure (V i)) [∀ i, IsProbabilityMeasure (μ i)]
    (nul : Outcome X) (F : Set (Outcome X)) (hF : DownClosed nul F)
    (val : ∀ i, V i → X i → ℝ) (hval : ∀ i w xi, 0 ≤ val i w xi ∧ val i w xi ≤ 1)
    (α β₁ β₂ : ℝ) (hα : 0 < α) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (ALG : (∀ i, V i) → Outcome X) (hALG : ∀ v, ALG v ∈ F)
    (pv : (∀ i, V i) → PriceRule X)
    (hrule : ∀ w, IsPricingRule F (pv w))
    (hnull : ∀ w i y, y ∈ F → pv w i (nul i) y = 0)
    (Fam : Outcome X → Set (Outcome X))
    (hB : ∀ w, WeakBalanced nul α β₁ β₂ F Fam (prof val w) (ALG w) (pv w))
    (δ : ℝ) (hδ : 0 < δ)
    (choice : ∀ i, V i → Outcome X → X i)
    (hchoice : IsUtilMax F val (pp δ μ pv) choice) :
    ∃ U R H : ℝ, ∫ v, welfare (prof val v) (run nul choice v) ∂(Measure.pi μ) = U + R ∧ 0 ≤ U ∧
      H - δ * (β₁ * H + β₂ * ∫ w, welfare (prof val w) (ALG w) ∂(Measure.pi μ)) ≤ U ∧
      δ / α * ((∫ w, welfare (prof val w) (ALG w) ∂(Measure.pi μ)) - H) ≤ R := by
  classical
  have hδT : ENNReal.ofReal δ ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]; linarith
  have hne : ∀ i, Nonempty (V i) := fun i => by
    by_contra h
    rw [not_nonempty_iff] at h
    have := measure_univ (μ := μ i)
    rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at this
    exact zero_ne_one this
  have hnulF : nul ∈ F := by
    have := hF (ALG fun i => Classical.choice (hne i)) (hALG _) ∅
    convert this using 1
    funext j
    simp [restrictTo]
  have htop : ∀ i xi y, y ∈ F → Function.update y i xi ∉ F →
      pp δ μ pv i xi y = ⊤ := by
    intro i xi y hy hn
    simp only [pp, expPrice]
    have : ∀ w, pv w i xi y = ⊤ := fun w => hrule w i xi y hy hn
    simp only [this, lintegral_const, measure_univ, mul_one]
    exact ENNReal.mul_top hδT
  have hq0 : ∀ i y, y ∈ F → pp δ μ pv i (nul i) y = 0 := by
    intro i y hy
    simp [pp, expPrice, hnull _ i y hy]
  have hLfin : ∀ i a y, pp δ μ pv i a y ≠ ⊤ →
      ∫⁻ w, pv w i a y ∂(Measure.pi μ) ≠ ⊤ := by
    intro i a y h hT
    apply h
    simp only [pp, expPrice, hT]
    exact ENNReal.mul_top hδT
  have hfeas : ∀ v, ∀ m : ℕ, m ≤ n → restrictTo nul (run nul choice v)
      (Finset.univ.filter fun j : Fin n => j.val < m) ∈ F := by
    intro v m
    induction m with
    | zero =>
      intro _
      convert hnulF using 1
      funext j
      simp [restrictTo]
    | succ m ih =>
      intro hm
      have hmn : m < n := hm
      have hy := ih hmn.le
      have hpre : pre nul (run nul choice v) ⟨m, hmn⟩ = restrictTo nul (run nul choice v)
          (Finset.univ.filter fun j : Fin n => j.val < m) := by
        unfold pre
        congr 1
      have hy' : pre nul (run nul choice v) ⟨m, hmn⟩ ∈ F := by rw [hpre]; exact hy
      have key : restrictTo nul (run nul choice v)
          (Finset.univ.filter fun j : Fin n => j.val < m + 1) =
          Function.update (pre nul (run nul choice v) ⟨m, hmn⟩) ⟨m, hmn⟩
            (choice ⟨m, hmn⟩ (v ⟨m, hmn⟩) (pre nul (run nul choice v) ⟨m, hmn⟩)) := by
        rw [← BP435.run_eq nul choice v ⟨m, hmn⟩]
        funext j
        by_cases hj : j = ⟨m, hmn⟩
        · subst hj
          simp [restrictTo]
        · rw [Function.update_of_ne hj, hpre]
          have : j.val ≠ m := fun h => hj (Fin.ext h)
          simp only [restrictTo, Finset.mem_filter, Finset.mem_univ, true_and]
          split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
      rw [key]
      by_contra hcon
      exact (hchoice _ _ _ hy').1 (htop _ _ _ hy' hcon)
  have hpreF : ∀ v i, pre nul (run nul choice v) i ∈ F := by
    intro v i
    have := hfeas v i.val i.isLt.le
    convert this using 1
    unfold pre
    congr 1
  have hxF : ∀ v, run nul choice v ∈ F := by
    intro v
    have := hfeas v n le_rfl
    convert this using 1
    funext j
    simp [restrictTo, j.isLt]
  have hU : ∀ v i (xi : X i),
      pp δ μ pv i xi (pre nul (run nul choice v) i) ≠ ⊤ →
      val i (v i) xi - (pp δ μ pv i xi (pre nul (run nul choice v) i)).toReal ≤
        utility nul val (pp δ μ pv) choice v i := by
    intro v i xi hxi
    unfold utility
    rw [BP435.run_eq nul choice v i]
    exact (hchoice i (v i) _ (hpreF v i)).2 xi hxi
  have hUb : ∀ v i, 0 ≤ utility nul val (pp δ μ pv) choice v i ∧
      utility nul val (pp δ μ pv) choice v i ≤ 1 := by
    intro v i
    constructor
    · have := hU v i (nul i) (by rw [hq0 _ _ (hpreF v i)]; exact ENNReal.zero_ne_top)
      rw [hq0 _ _ (hpreF v i), ENNReal.toReal_zero, sub_zero] at this
      linarith [(hval i (v i) (nul i)).1]
    · unfold utility
      linarith [(hval i (v i) (run nul choice v i)).2, ENNReal.toReal_nonneg (a :=
        pp δ μ pv i (run nul choice v i) (pre nul (run nul choice v) i))]
  have hRb : ∀ v i, 0 ≤ (pp δ μ pv i (run nul choice v i)
      (pre nul (run nul choice v) i)).toReal ∧ (pp δ μ pv i (run nul choice v i)
      (pre nul (run nul choice v) i)).toReal ≤ 1 := by
    intro v i
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have := (hUb v i).1
    unfold utility at this
    linarith [(hval i (v i) (run nul choice v i)).1, (hval i (v i) (run nul choice v i)).2]
  have hW : ∀ v, welfare (prof val v) (run nul choice v) =
      ∑ i, utility nul val (pp δ μ pv) choice v i +
      ∑ i, (pp δ μ pv i (run nul choice v i) (pre nul (run nul choice v) i)).toReal := by
    intro v
    simp only [welfare, prof, utility]
    rw [← Finset.sum_add_distrib]
    simp
  have hsumq : ∀ (a x : Outcome X), (∀ i, pp δ μ pv i (a i) (pre nul x i) ≠ ⊤) →
      ∑ i, (pp δ μ pv i (a i) (pre nul x i)).toReal =
        δ * (∫⁻ w, ∑ i, pv w i (a i) (pre nul x i) ∂(Measure.pi μ)).toReal := by
    intro a x hfin
    have hfin' := fun i => hLfin i _ _ (hfin i)
    simp only [pp, expPrice, ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le]
    rw [← Finset.mul_sum, lintegral_finset_sum _ (fun i _ => Measurable.of_discrete),
      ENNReal.toReal_sum (fun i _ => hfin' i)]
  have hsumfin : ∀ (a x : Outcome X), (∀ i, pp δ μ pv i (a i) (pre nul x i) ≠ ⊤) →
      ∫⁻ w, ∑ i, pv w i (a i) (pre nul x i) ∂(Measure.pi μ) ≠ ⊤ := by
    intro a x hfin
    rw [lintegral_finset_sum _ (fun i _ => Measurable.of_discrete)]
    exact ENNReal.sum_ne_top.mpr (fun i _ => hLfin i _ _ (hfin i))
  obtain ⟨h, hh⟩ : ∃ h : (∀ i, V i) → ℝ, ∀ v,
      h v = ∫ w, optVal (prof val w) (Fam (run nul choice v)) ∂(Measure.pi μ) := ⟨_, fun _ => rfl⟩
  have hoptI : ∀ v, Integrable (fun w => optVal (prof val w) (Fam (run nul choice v)))
      (Measure.pi μ) := fun v => BP435.intB _ _ 0 n (fun w => BP435.opt_bd val hval w _)
  have hhb : ∀ v, 0 ≤ h v ∧ h v ≤ n := by
    intro v
    rw [hh]
    constructor
    · exact integral_nonneg fun w => (BP435.opt_bd val hval w _).1
    · calc ∫ w, optVal (prof val w) (Fam (run nul choice v)) ∂(Measure.pi μ)
          ≤ ∫ _w, (n : ℝ) ∂(Measure.pi μ) :=
            integral_mono (hoptI v) (integrable_const _) (fun w => (BP435.opt_bd val hval w _).2)
        _ = n := by simp
  obtain ⟨WA, hWA⟩ : ∃ WA : ℝ, WA = ∫ w, welfare (prof val w) (ALG w) ∂(Measure.pi μ) :=
    ⟨_, rfl⟩
  have hWAI : Integrable (fun w => welfare (prof val w) (ALG w)) (Measure.pi μ) :=
    BP435.intB _ _ 0 n (fun w => BP435.welfare_bd val hval w _)
  have hWAb : 0 ≤ WA ∧ WA ≤ n := by
    rw [hWA]
    constructor
    · exact integral_nonneg fun w => (BP435.welfare_bd val hval w _).1
    · calc ∫ w, welfare (prof val w) (ALG w) ∂(Measure.pi μ)
          ≤ ∫ _w, (n : ℝ) ∂(Measure.pi μ) :=
            integral_mono hWAI (integrable_const _) (fun w => (BP435.welfare_bd val hval w _).2)
        _ = n := by simp
  rw [← hWA]
  -- revenue bound
  have hrev : ∀ v, δ / α * (WA - h v) ≤
      ∑ i, (pp δ μ pv i (run nul choice v i) (pre nul (run nul choice v) i)).toReal := by
    intro v
    have hfin : ∀ i, pp δ μ pv i (run nul choice v i)
        (pre nul (run nul choice v) i) ≠ ⊤ := by
      intro i
      rw [BP435.run_eq nul choice v i]
      exact (hchoice i (v i) _ (hpreF v i)).1
    rw [hsumq _ _ hfin]
    have hlow : ∫⁻ w, ENNReal.ofReal ((1 / α) * (welfare (prof val w) (ALG w) -
        optVal (prof val w) (Fam (run nul choice v)))) ∂(Measure.pi μ) ≤
        ∫⁻ w, ∑ i, pv w i (run nul choice v i) (pre nul (run nul choice v) i) ∂(Measure.pi μ) :=
      lintegral_mono fun w => (hB w (run nul choice v) (hxF v)).1
    have hgI : Integrable (fun w => (1 / α) * (welfare (prof val w) (ALG w) -
        optVal (prof val w) (Fam (run nul choice v)))) (Measure.pi μ) :=
      (hWAI.sub (hoptI v)).const_mul _
    have hint : ∫ w, (1 / α) * (welfare (prof val w) (ALG w) -
        optVal (prof val w) (Fam (run nul choice v))) ∂(Measure.pi μ) = (1 / α) * (WA - h v) := by
      rw [integral_const_mul, integral_sub hWAI (hoptI v), hWA, hh]
    calc δ / α * (WA - h v)
        = δ * ((1 / α) * (WA - h v)) := by ring
      _ ≤ δ * (∫⁻ w, ENNReal.ofReal ((1 / α) * (welfare (prof val w) (ALG w) -
          optVal (prof val w) (Fam (run nul choice v)))) ∂(Measure.pi μ)).toReal := by
          rw [← hint]
          exact mul_le_mul_of_nonneg_left (BP435.int_le_lint _ _ hgI) hδ.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (hsumfin _ _ hfin) hlow) hδ.le
  have hUI : ∀ i, Integrable (fun v => utility nul val (pp δ μ pv) choice v i)
      (Measure.pi μ) := fun i => BP435.intB _ _ 0 1 (fun v => hUb v i)
  have hRI : ∀ i, Integrable (fun v => (pp δ μ pv i (run nul choice v i)
      (pre nul (run nul choice v) i)).toReal) (Measure.pi μ) := fun i =>
    BP435.intB _ _ 0 1 (fun v => hRb v i)
  have hhI : Integrable h (Measure.pi μ) := BP435.intB _ _ 0 n hhb
  have hT : ∀ v, 0 ≤ β₁ * h v + β₂ * WA ∧ β₁ * h v + β₂ * WA ≤ β₁ * n + β₂ * n := by
    intro v
    have a1 := mul_le_mul_of_nonneg_left (hhb v).2 hβ₁
    have a2 := mul_le_mul_of_nonneg_left hWAb.2 hβ₂
    have a3 := mul_nonneg hβ₁ (hhb v).1
    have a4 := mul_nonneg hβ₂ hWAb.1
    constructor <;> linarith
  -- main estimate with slack ε
  have hmain : ∀ ε : ℝ, 0 < ε → (∫ v, h v ∂(Measure.pi μ)) -
      δ * (β₁ * (∫ v, h v ∂(Measure.pi μ)) + β₂ * WA) ≤
      ∫ v, ∑ i, utility nul val (pp δ μ pv) choice v i ∂(Measure.pi μ) + ε := by
    intro ε hε
    have hdev : ∀ v w : (∀ i, V i), ∃ D : Outcome X,
        optVal (prof val w) (Fam (run nul choice v)) - ε ≤ welfare (prof val w) D ∧
        ∀ w', ∑ j, pv w' j (D j) (pre nul (run nul choice v) j) ≤
          ENNReal.ofReal (β₁ * optVal (prof val w') (Fam (run nul choice v)) +
            β₂ * welfare (prof val w') (ALG w')) := by
      intro v w
      by_cases hS : (Fam (run nul choice v)).Nonempty
      · have hlt : optVal (prof val w) (Fam (run nul choice v)) - ε <
            sSup (welfare (prof val w) '' Fam (run nul choice v)) := by
          unfold optVal; linarith
        obtain ⟨_, ⟨y, hyS, rfl⟩, hy⟩ := exists_lt_of_lt_csSup (hS.image _) hlt
        exact ⟨y, hy.le, fun w' => (hB w' (run nul choice v) (hxF v)).2 y hyS⟩
      · rw [Set.not_nonempty_iff_eq_empty] at hS
        refine ⟨nul, ?_, fun w' => ?_⟩
        · rw [hS]
          unfold optVal
          rw [Set.image_empty, Real.sSup_empty]
          linarith [(BP435.welfare_bd val hval w nul).1]
        · rw [Finset.sum_eq_zero (fun j _ => hnull w' j _ (hpreF v j))]
          exact zero_le
    choose D hD1 hD2 using hdev
    have hbw : ∀ (a : ∀ i, V i) w, β₁ * optVal (prof val w) (Fam (run nul choice a)) +
        β₂ * welfare (prof val w) (ALG w) ≤ β₁ * n + β₂ * n := by
      intro a w
      have a1 := mul_le_mul_of_nonneg_left (BP435.opt_bd val hval w (Fam (run nul choice a))).2 hβ₁
      have a2 := mul_le_mul_of_nonneg_left (BP435.welfare_bd val hval w (ALG w)).2 hβ₂
      linarith
    have hbw0 : ∀ (a : ∀ i, V i) w, 0 ≤ β₁ * optVal (prof val w) (Fam (run nul choice a)) +
        β₂ * welfare (prof val w) (ALG w) := by
      intro a w
      have a3 := mul_nonneg hβ₁ (BP435.opt_bd val hval w (Fam (run nul choice a))).1
      have a4 := mul_nonneg hβ₂ (BP435.welfare_bd val hval w (ALG w)).1
      linarith
    have hDq : ∀ v' w' i, pp δ μ pv i (D v' w' i) (pre nul (run nul choice v') i) ≤
        ENNReal.ofReal δ * ENNReal.ofReal (β₁ * n + β₂ * n) := by
      intro v' w' i
      simp only [pp, expPrice]
      refine mul_le_mul' le_rfl ?_
      calc ∫⁻ w, pv w i (D v' w' i) (pre nul (run nul choice v') i) ∂(Measure.pi μ)
          ≤ ∫⁻ _w, ENNReal.ofReal (β₁ * n + β₂ * n) ∂(Measure.pi μ) := by
            refine lintegral_mono fun w => ?_
            refine le_trans (Finset.single_le_sum
              (f := fun j => pv w j (D v' w' j) (pre nul (run nul choice v') j))
              (fun _ _ => zero_le) (Finset.mem_univ i)) (le_trans (hD2 v' w' w) ?_)
            exact ENNReal.ofReal_le_ofReal (hbw v' w)
        _ = ENNReal.ofReal (β₁ * n + β₂ * n) := by simp
    have hDfin : ∀ v' w' i, pp δ μ pv i (D v' w' i)
        (pre nul (run nul choice v') i) ≠ ⊤ := fun v' w' i =>
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (hDq v' w' i)
    obtain ⟨g, hg⟩ : ∃ g : Fin n → (∀ i, V i) × (∀ i, V i) → ℝ, ∀ i p, g i p =
        val i (p.1 i) (D (BP435.sw i p).1 (BP435.sw i p).2 i) -
          (pp δ μ pv i (D (BP435.sw i p).1 (BP435.sw i p).2 i)
            (pre nul (run nul choice p.1) i)).toReal := ⟨_, fun _ _ => rfl⟩
    have hg_le : ∀ i p, g i p ≤ utility nul val (pp δ μ pv) choice p.1 i := by
      intro i p
      rw [hg]
      apply hU
      have := hDfin (BP435.sw i p).1 (BP435.sw i p).2 i
      simp only [BP435.sw] at this ⊢
      rw [BP435.pre_run_update] at this
      exact this
    have hn0 : 0 ≤ β₁ * (n : ℝ) + β₂ * n := by
      have := Nat.cast_nonneg (α := ℝ) n
      positivity
    have hg_bd : ∀ i p, -(δ * (β₁ * n + β₂ * n)) ≤ g i p ∧ g i p ≤ 1 := by
      intro i p
      rw [hg]
      have hq := hDq (BP435.sw i p).1 (BP435.sw i p).2 i
      simp only [BP435.sw] at hq ⊢
      rw [BP435.pre_run_update] at hq
      have hq' := ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hq
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le,
        ENNReal.toReal_ofReal hn0] at hq'
      constructor
      · linarith [(hval i (p.1 i) (D (Function.update p.1 i (p.2 i))
          (Function.update p.2 i (p.1 i)) i)).1]
      · linarith [(hval i (p.1 i) (D (Function.update p.1 i (p.2 i))
          (Function.update p.2 i (p.1 i)) i)).2, ENNReal.toReal_nonneg (a :=
          pp δ μ pv i (D (Function.update p.1 i (p.2 i))
          (Function.update p.2 i (p.1 i)) i) (pre nul (run nul choice p.1) i))]
    have hg_sw : ∀ i a b, g i (BP435.sw i (a, b)) = val i (b i) (D a b i) -
        (pp δ μ pv i (D a b i) (pre nul (run nul choice a) i)).toReal := by
      intro i a b
      rw [hg, BP435.sw_sw]
      simp only [BP435.sw, Function.update_self]
      rw [BP435.pre_run_update]
    have hlowsum : ∀ a b, optVal (prof val b) (Fam (run nul choice a)) -
        (ε + δ * (β₁ * h a + β₂ * WA)) ≤ ∑ i, g i (BP435.sw i (a, b)) := by
      intro a b
      simp only [hg_sw]
      rw [Finset.sum_sub_distrib, hsumq _ _ (fun i => hDfin a b i)]
      have h1 := hD1 a b
      have hB2 : (∫⁻ w, ∑ i, pv w i (D a b i) (pre nul (run nul choice a) i) ∂(Measure.pi μ)).toReal
          ≤ β₁ * h a + β₂ * WA := by
        have hbI : Integrable (fun w => β₁ * optVal (prof val w) (Fam (run nul choice a)) +
            β₂ * welfare (prof val w) (ALG w)) (Measure.pi μ) :=
          ((hoptI a).const_mul _).add (hWAI.const_mul _)
        have hEq : β₁ * h a + β₂ * WA = (∫⁻ w, ENNReal.ofReal (β₁ * optVal (prof val w)
            (Fam (run nul choice a)) + β₂ * welfare (prof val w) (ALG w)) ∂(Measure.pi μ)).toReal := by
          rw [← integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => hbw0 a w)
            StronglyMeasurable.of_discrete.aestronglyMeasurable,
            integral_add ((hoptI a).const_mul _) (hWAI.const_mul _), integral_const_mul,
            integral_const_mul, hh, hWA]
        rw [hEq]
        refine ENNReal.toReal_mono ?_ (lintegral_mono fun w => hD2 a b w)
        refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := β₁ * n + β₂ * n)) ?_
        calc ∫⁻ w, ENNReal.ofReal (β₁ * optVal (prof val w) (Fam (run nul choice a)) +
                β₂ * welfare (prof val w) (ALG w)) ∂(Measure.pi μ)
              ≤ ∫⁻ _w, ENNReal.ofReal (β₁ * n + β₂ * n) ∂(Measure.pi μ) :=
              lintegral_mono fun w => ENNReal.ofReal_le_ofReal (hbw a w)
          _ = ENNReal.ofReal (β₁ * n + β₂ * n) := by simp
      have hwel : welfare (prof val b) (D a b) = ∑ i, val i (b i) (D a b i) := rfl
      rw [← hwel]
      nlinarith [mul_le_mul_of_nonneg_left hB2 hδ.le]
    set Q := (Measure.pi μ).prod (Measure.pi μ) with hQ
    have hgI : ∀ i, Integrable (g i) Q := fun i =>
      BP435.intB _ _ _ _ (fun p => hg_bd i p)
    have hgsI : ∀ i, Integrable (fun p => g i (BP435.sw i p)) Q := fun i =>
      BP435.intB _ _ _ _ (fun p => hg_bd i (BP435.sw i p))
    have e1 : ∫ v, ∑ i, utility nul val (pp δ μ pv) choice v i ∂(Measure.pi μ) =
        ∫ p, ∑ i, utility nul val (pp δ μ pv) choice p.1 i ∂Q := by
      rw [hQ, BP435.int_fst _ _ (fun v => ∑ i, utility nul val (pp δ μ pv) choice v i)
        0 n]
      intro v
      constructor
      · exact Finset.sum_nonneg fun i _ => (hUb v i).1
      · calc ∑ i, utility nul val (pp δ μ pv) choice v i ≤ ∑ _i : Fin n, (1:ℝ) :=
            Finset.sum_le_sum fun i _ => (hUb v i).2
          _ = n := by simp
    have e2 : ∫ p, ∑ i, g i p ∂Q ≤
        ∫ p, ∑ i, utility nul val (pp δ μ pv) choice p.1 i ∂Q :=
      integral_mono (integrable_finsetSum _ fun i _ => hgI i)
        (integrable_finsetSum _ fun i _ => BP435.intB _ _ 0 1 (fun p => hUb p.1 i))
        (fun p => Finset.sum_le_sum fun i _ => hg_le i p)
    have e3 : ∫ p, ∑ i, g i p ∂Q = ∫ p, ∑ i, g i (BP435.sw i p) ∂Q := by
      rw [integral_finset_sum _ (fun i _ => hgI i),
        integral_finset_sum _ (fun i _ => hgsI i)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hQ]
      exact BP435.int_sw μ i (g i)
    have hkI : Integrable (fun p : (∀ i, V i) × (∀ i, V i) =>
        optVal (prof val p.2) (Fam (run nul choice p.1)) -
          (ε + δ * (β₁ * h p.1 + β₂ * WA))) Q := by
      refine BP435.intB _ _ (0 - (ε + δ * (β₁ * n + β₂ * n))) (n - ε) (fun p => ?_)
      have := BP435.opt_bd val hval p.2 (Fam (run nul choice p.1))
      have : 0 ≤ δ * (β₁ * h p.1 + β₂ * WA) := mul_nonneg hδ.le (hT p.1).1
      have : δ * (β₁ * h p.1 + β₂ * WA) ≤ δ * (β₁ * n + β₂ * n) :=
        mul_le_mul_of_nonneg_left (hT p.1).2 hδ.le
      constructor <;> linarith
    have e4 : ∫ p, (optVal (prof val p.2) (Fam (run nul choice p.1)) -
          (ε + δ * (β₁ * h p.1 + β₂ * WA))) ∂Q ≤ ∫ p, ∑ i, g i (BP435.sw i p) ∂Q :=
      integral_mono hkI (integrable_finsetSum _ fun i _ => hgsI i)
        (fun p => hlowsum p.1 p.2)
    have e5 : ∫ p, (optVal (prof val p.2) (Fam (run nul choice p.1)) -
          (ε + δ * (β₁ * h p.1 + β₂ * WA))) ∂Q =
        (∫ v, h v ∂(Measure.pi μ)) - δ * (β₁ * (∫ v, h v ∂(Measure.pi μ)) + β₂ * WA) - ε := by
      rw [hQ, integral_prod _ hkI]
      have inner : ∀ v, ∫ w, (optVal (prof val w) (Fam (run nul choice v)) -
          (ε + δ * (β₁ * h v + β₂ * WA))) ∂(Measure.pi μ) =
          (1 - δ * β₁) * h v - (ε + δ * β₂ * WA) := by
        intro v
        rw [integral_sub (hoptI v) (integrable_const _), integral_const, ← hh]
        simp only [probReal_univ, smul_eq_mul, one_mul]
        ring
      simp only [inner]
      rw [integral_sub (hhI.const_mul _) (integrable_const _), integral_const_mul,
        integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      ring
    linarith
  refine ⟨∫ v, ∑ i, utility nul val (pp δ μ pv) choice v i ∂(Measure.pi μ),
    ∫ v, ∑ i, (pp δ μ pv i (run nul choice v i) (pre nul (run nul choice v) i)).toReal
      ∂(Measure.pi μ), ∫ v, h v ∂(Measure.pi μ), ?_, ?_, ?_, ?_⟩
  · simp_rw [hW]
    exact integral_add (integrable_finsetSum _ fun i _ => hUI i)
      (integrable_finsetSum _ fun i _ => hRI i)
  · exact integral_nonneg fun v => Finset.sum_nonneg fun i _ => (hUb v i).1
  · exact le_of_forall_pos_le_add hmain
  · have hfI : Integrable (fun v => δ / α * (WA - h v)) (Measure.pi μ) :=
      ((integrable_const WA).sub hhI).const_mul _
    have := integral_mono hfI (integrable_finsetSum _ fun i _ => hRI i) hrev
    rw [integral_const_mul, integral_sub (integrable_const WA) hhI, integral_const] at this
    simpa using this

end BP435

open BalancedPrices.Extension MeasureTheory in
theorem solution
    {n : ℕ} {X V : Fin n → Type*}
    [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)]
    (μ : ∀ i, Measure (V i)) [∀ i, IsProbabilityMeasure (μ i)]
    (nul : BalancedPrices.Extension.Outcome X) (F : Set (BalancedPrices.Extension.Outcome X)) (hF : BalancedPrices.Extension.DownClosed nul F)
    (val : ∀ i, V i → X i → ℝ) (hval : ∀ i w xi, 0 ≤ val i w xi ∧ val i w xi ≤ 1)
    (α β₁ β₂ : ℝ) (hα : 0 < α) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hsum : 1 / α ≤ β₁ + β₂)
    (ALG : (∀ i, V i) → BalancedPrices.Extension.Outcome X) (hALG : ∀ v, ALG v ∈ F)
    (pv : (∀ i, V i) → BalancedPrices.Extension.PriceRule X)
    (hrule : ∀ w, BalancedPrices.Extension.IsPricingRule F (pv w))
    (hnull : ∀ w i y, y ∈ F → pv w i (nul i) y = 0)
    (hwb : ∃ Fam : BalancedPrices.Extension.Outcome X → Set (BalancedPrices.Extension.Outcome X), BalancedPrices.Extension.ExchFamily F Fam ∧
      ∀ w, BalancedPrices.WeakExtension.WeakBalanced nul α β₁ β₂ F Fam (BalancedPrices.Extension.prof val w) (ALG w) (pv w))
    (choice : ∀ i, V i → BalancedPrices.Extension.Outcome X → X i)
    (hchoice : BalancedPrices.Extension.IsUtilMax F val
      (fun i xi y => ENNReal.ofReal (1 / (β₁ + max (2 * β₂) (1 / α))) * BalancedPrices.Extension.expPrice μ pv i xi y) choice) :
    1 / (α * (2 * β₁ + 4 * β₂)) * ∫ v, BalancedPrices.Extension.welfare (BalancedPrices.Extension.prof val v) (ALG v) ∂(Measure.pi μ) ≤
      ∫ v, BalancedPrices.Extension.welfare (BalancedPrices.Extension.prof val v) (BalancedPrices.Extension.run nul choice v) ∂(Measure.pi μ) := by
  obtain ⟨Fam, -, hB⟩ := hwb
  have hpos : 0 < β₁ + max (2 * β₂) (1 / α) := by
    have := le_max_right (2 * β₂) (1 / α)
    have : 0 < 1 / α := by positivity
    linarith
  obtain ⟨U, R, H, hE, hU0, hU, hR⟩ := BP435.main μ nul F hF val hval α β₁ β₂ hα hβ₁ hβ₂ ALG hALG
    pv hrule hnull Fam hB (1 / (β₁ + max (2 * β₂) (1 / α))) (by positivity) choice hchoice
  rw [hE]
  exact BP435.arith α β₁ β₂ _ H U R hα hβ₁ hβ₂ hsum
    (integral_nonneg fun w => (BP435.welfare_bd val hval w _).1) hU0 hU hR
