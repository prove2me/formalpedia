-- Prove2me | solution 1 for BalancedPrices.Extension.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T07:16:25.336304+00:00
-- url     : https://prove2.me/submissions/a6966675-078f-41ef-897b-6c455a701cff

import Mathlib
import Definitions.Def_BalancedPrices_Extension_Model
import Definitions.Def_BalancedPrices_Extension_Mechanism

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace BP42

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

end BP42

set_option maxHeartbeats 1000000 in
open BalancedPrices.Extension MeasureTheory in
theorem solution {n : ℕ} {X V : Fin n → Type*}
    [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)]
    (nul : Outcome X) (F : Set (Outcome X)) (hF : DownClosed nul F)
    (val : ∀ i, V i → X i → ℝ) (hval : ∀ i w xi, 0 ≤ val i w xi ∧ val i w xi ≤ 1)
    (μ : ∀ i, Measure (V i)) [∀ i, IsProbabilityMeasure (μ i)]
    (α β : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (ALG : (∀ i, V i) → Outcome X) (hALG : ∀ v, ALG v ∈ F)
    (pv : (∀ i, V i) → PriceRule X) (hrule : ∀ w, IsPricingRule F (pv w))
    (hnull : ∀ w i y, y ∈ F → pv w i (nul i) y = 0)
    (hbal : ∃ Fam : Outcome X → Set (Outcome X), ExchFamily F Fam ∧
      ∀ w, Balanced nul α β F Fam (prof val w) (ALG w) (pv w))
    (choice : ∀ i, V i → Outcome X → X i)
    (hchoice : IsUtilMax F val (postedPrice α β μ pv) choice) :
    1 / (1 + α * β) * ∫ v, welfare (prof val v) (ALG v) ∂(Measure.pi μ) ≤
      ∫ v, welfare (prof val v) (run nul choice v) ∂(Measure.pi μ) := by
  classical
  obtain ⟨Fam, -, hB⟩ := hbal
  have h1ab : 0 < 1 + α * β := by nlinarith
  have hδ : 0 < α / (1 + α * β) := div_pos hα h1ab
  have hδT : ENNReal.ofReal (α / (1 + α * β)) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]; linarith
  -- nonempty types, nul ∈ F
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
  -- infinite price outside F, zero price for nul
  have htop : ∀ i xi y, y ∈ F → Function.update y i xi ∉ F →
      postedPrice α β μ pv i xi y = ⊤ := by
    intro i xi y hy hn
    simp only [postedPrice, expPrice]
    have : ∀ w, pv w i xi y = ⊤ := fun w => hrule w i xi y hy hn
    simp only [this, lintegral_const, measure_univ, mul_one]
    exact ENNReal.mul_top hδT
  have hq0 : ∀ i y, y ∈ F → postedPrice α β μ pv i (nul i) y = 0 := by
    intro i y hy
    simp [postedPrice, expPrice, hnull _ i y hy]
  have hLfin : ∀ i a y, postedPrice α β μ pv i a y ≠ ⊤ →
      ∫⁻ w, pv w i a y ∂(Measure.pi μ) ≠ ⊤ := by
    intro i a y h hT
    apply h
    simp only [postedPrice, expPrice, hT]
    exact ENNReal.mul_top hδT
  -- feasibility of the run
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
        rw [← BP42.run_eq nul choice v ⟨m, hmn⟩]
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
  -- utility facts
  have hU : ∀ v i (xi : X i),
      postedPrice α β μ pv i xi (pre nul (run nul choice v) i) ≠ ⊤ →
      val i (v i) xi - (postedPrice α β μ pv i xi (pre nul (run nul choice v) i)).toReal ≤
        utility nul val (postedPrice α β μ pv) choice v i := by
    intro v i xi hxi
    unfold utility
    rw [BP42.run_eq nul choice v i]
    exact (hchoice i (v i) _ (hpreF v i)).2 xi hxi
  have hUb : ∀ v i, 0 ≤ utility nul val (postedPrice α β μ pv) choice v i ∧
      utility nul val (postedPrice α β μ pv) choice v i ≤ 1 := by
    intro v i
    constructor
    · have := hU v i (nul i) (by rw [hq0 _ _ (hpreF v i)]; exact ENNReal.zero_ne_top)
      rw [hq0 _ _ (hpreF v i), ENNReal.toReal_zero, sub_zero] at this
      linarith [(hval i (v i) (nul i)).1]
    · unfold utility
      linarith [(hval i (v i) (run nul choice v i)).2, ENNReal.toReal_nonneg (a :=
        postedPrice α β μ pv i (run nul choice v i) (pre nul (run nul choice v) i))]
  have hRb : ∀ v i, 0 ≤ (postedPrice α β μ pv i (run nul choice v i)
      (pre nul (run nul choice v) i)).toReal ∧ (postedPrice α β μ pv i (run nul choice v i)
      (pre nul (run nul choice v) i)).toReal ≤ 1 := by
    intro v i
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have := (hUb v i).1
    unfold utility at this
    linarith [(hval i (v i) (run nul choice v i)).1, (hval i (v i) (run nul choice v i)).2]
  have hW : ∀ v, welfare (prof val v) (run nul choice v) =
      ∑ i, utility nul val (postedPrice α β μ pv) choice v i +
      ∑ i, (postedPrice α β μ pv i (run nul choice v i) (pre nul (run nul choice v) i)).toReal := by
    intro v
    simp only [welfare, prof, utility]
    rw [← Finset.sum_add_distrib]
    simp
  -- sums of posted prices
  have hsumq : ∀ (a x : Outcome X), (∀ i, postedPrice α β μ pv i (a i) (pre nul x i) ≠ ⊤) →
      ∑ i, (postedPrice α β μ pv i (a i) (pre nul x i)).toReal =
        α / (1 + α * β) * (∫⁻ w, ∑ i, pv w i (a i) (pre nul x i) ∂(Measure.pi μ)).toReal := by
    intro a x hfin
    have hfin' := fun i => hLfin i _ _ (hfin i)
    simp only [postedPrice, expPrice, ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le]
    rw [← Finset.mul_sum, lintegral_finset_sum _ (fun i _ => Measurable.of_discrete),
      ENNReal.toReal_sum (fun i _ => hfin' i)]
  have hsumfin : ∀ (a x : Outcome X), (∀ i, postedPrice α β μ pv i (a i) (pre nul x i) ≠ ⊤) →
      ∫⁻ w, ∑ i, pv w i (a i) (pre nul x i) ∂(Measure.pi μ) ≠ ⊤ := by
    intro a x hfin
    rw [lintegral_finset_sum _ (fun i _ => Measurable.of_discrete)]
    exact ENNReal.sum_ne_top.mpr (fun i _ => hLfin i _ _ (hfin i))
  -- the expected optimum h
  obtain ⟨h, hh⟩ : ∃ h : (∀ i, V i) → ℝ, ∀ v,
      h v = ∫ w, optVal (prof val w) (Fam (run nul choice v)) ∂(Measure.pi μ) := ⟨_, fun _ => rfl⟩
  have hoptI : ∀ v, Integrable (fun w => optVal (prof val w) (Fam (run nul choice v)))
      (Measure.pi μ) := fun v => BP42.intB _ _ 0 n (fun w => BP42.opt_bd val hval w _)
  have hhb : ∀ v, 0 ≤ h v ∧ h v ≤ n := by
    intro v
    rw [hh]
    constructor
    · exact integral_nonneg fun w => (BP42.opt_bd val hval w _).1
    · calc ∫ w, optVal (prof val w) (Fam (run nul choice v)) ∂(Measure.pi μ)
          ≤ ∫ _w, (n : ℝ) ∂(Measure.pi μ) :=
            integral_mono (hoptI v) (integrable_const _) (fun w => (BP42.opt_bd val hval w _).2)
        _ = n := by simp
  obtain ⟨WA, hWA⟩ : ∃ WA : ℝ, WA = ∫ w, welfare (prof val w) (ALG w) ∂(Measure.pi μ) :=
    ⟨_, rfl⟩
  have hWAI : Integrable (fun w => welfare (prof val w) (ALG w)) (Measure.pi μ) :=
    BP42.intB _ _ 0 n (fun w => BP42.welfare_bd val hval w _)
  -- revenue bound
  have hrev : ∀ v, 1 / (1 + α * β) * (WA - h v) ≤
      ∑ i, (postedPrice α β μ pv i (run nul choice v i) (pre nul (run nul choice v) i)).toReal := by
    intro v
    have hfin : ∀ i, postedPrice α β μ pv i (run nul choice v i)
        (pre nul (run nul choice v) i) ≠ ⊤ := by
      intro i
      rw [BP42.run_eq nul choice v i]
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
    calc 1 / (1 + α * β) * (WA - h v)
        = α / (1 + α * β) * ((1 / α) * (WA - h v)) := by field_simp
      _ ≤ α / (1 + α * β) * (∫⁻ w, ENNReal.ofReal ((1 / α) * (welfare (prof val w) (ALG w) -
          optVal (prof val w) (Fam (run nul choice v)))) ∂(Measure.pi μ)).toReal := by
          rw [← hint]
          exact mul_le_mul_of_nonneg_left (BP42.int_le_lint _ _ hgI) hδ.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (hsumfin _ _ hfin) hlow) hδ.le
  -- main estimate with slack ε
  have hmain : ∀ ε : ℝ, 0 < ε → 1 / (1 + α * β) * WA ≤
      ∫ v, welfare (prof val v) (run nul choice v) ∂(Measure.pi μ) + ε := by
    intro ε hε
    have hdev : ∀ v w : (∀ i, V i), ∃ D : Outcome X,
        optVal (prof val w) (Fam (run nul choice v)) - ε ≤ welfare (prof val w) D ∧
        ∀ w', ∑ j, pv w' j (D j) (pre nul (run nul choice v) j) ≤
          ENNReal.ofReal (β * optVal (prof val w') (Fam (run nul choice v))) := by
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
          linarith [(BP42.welfare_bd val hval w nul).1]
        · rw [Finset.sum_eq_zero (fun j _ => hnull w' j _ (hpreF v j))]
          exact zero_le
    choose D hD1 hD2 using hdev
    have hDq : ∀ v' w' i, postedPrice α β μ pv i (D v' w' i) (pre nul (run nul choice v') i) ≤
        ENNReal.ofReal (α / (1 + α * β)) * ENNReal.ofReal (β * n) := by
      intro v' w' i
      simp only [postedPrice, expPrice]
      refine mul_le_mul' le_rfl ?_
      calc ∫⁻ w, pv w i (D v' w' i) (pre nul (run nul choice v') i) ∂(Measure.pi μ)
          ≤ ∫⁻ _w, ENNReal.ofReal (β * n) ∂(Measure.pi μ) := by
            refine lintegral_mono fun w => ?_
            refine le_trans (Finset.single_le_sum
              (f := fun j => pv w j (D v' w' j) (pre nul (run nul choice v') j))
              (fun _ _ => zero_le) (Finset.mem_univ i)) (le_trans (hD2 v' w' w) ?_)
            exact ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_left (BP42.opt_bd val hval w _).2 hβ)
        _ = ENNReal.ofReal (β * n) := by simp
    have hDfin : ∀ v' w' i, postedPrice α β μ pv i (D v' w' i)
        (pre nul (run nul choice v') i) ≠ ⊤ := fun v' w' i =>
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (hDq v' w' i)
    -- the deviation utility bound
    obtain ⟨g, hg⟩ : ∃ g : Fin n → (∀ i, V i) × (∀ i, V i) → ℝ, ∀ i p, g i p =
        val i (p.1 i) (D (BP42.sw i p).1 (BP42.sw i p).2 i) -
          (postedPrice α β μ pv i (D (BP42.sw i p).1 (BP42.sw i p).2 i)
            (pre nul (run nul choice p.1) i)).toReal := ⟨_, fun _ _ => rfl⟩
    have hg_le : ∀ i p, g i p ≤ utility nul val (postedPrice α β μ pv) choice p.1 i := by
      intro i p
      rw [hg]
      apply hU
      have := hDfin (BP42.sw i p).1 (BP42.sw i p).2 i
      simp only [BP42.sw] at this ⊢
      rw [BP42.pre_run_update] at this
      exact this
    have hg_bd : ∀ i p, -(α / (1 + α * β) * (β * n)) ≤ g i p ∧ g i p ≤ 1 := by
      intro i p
      rw [hg]
      have hq := hDq (BP42.sw i p).1 (BP42.sw i p).2 i
      simp only [BP42.sw] at hq ⊢
      rw [BP42.pre_run_update] at hq
      have hq' := ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hq
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le,
        ENNReal.toReal_ofReal (mul_nonneg hβ (Nat.cast_nonneg n))] at hq'
      constructor
      · linarith [(hval i (p.1 i) (D (Function.update p.1 i (p.2 i))
          (Function.update p.2 i (p.1 i)) i)).1]
      · linarith [(hval i (p.1 i) (D (Function.update p.1 i (p.2 i))
          (Function.update p.2 i (p.1 i)) i)).2, ENNReal.toReal_nonneg (a :=
          postedPrice α β μ pv i (D (Function.update p.1 i (p.2 i))
          (Function.update p.2 i (p.1 i)) i) (pre nul (run nul choice p.1) i))]
    have hg_sw : ∀ i a b, g i (BP42.sw i (a, b)) = val i (b i) (D a b i) -
        (postedPrice α β μ pv i (D a b i) (pre nul (run nul choice a) i)).toReal := by
      intro i a b
      rw [hg, BP42.sw_sw]
      simp only [BP42.sw, Function.update_self]
      rw [BP42.pre_run_update]
    have hlowsum : ∀ a b, optVal (prof val b) (Fam (run nul choice a)) -
        (ε + α / (1 + α * β) * (β * h a)) ≤ ∑ i, g i (BP42.sw i (a, b)) := by
      intro a b
      simp only [hg_sw]
      rw [Finset.sum_sub_distrib, hsumq _ _ (fun i => hDfin a b i)]
      have h1 := hD1 a b
      have hB2 : (∫⁻ w, ∑ i, pv w i (D a b i) (pre nul (run nul choice a) i) ∂(Measure.pi μ)).toReal
          ≤ β * h a := by
        have hbI : Integrable (fun w => β * optVal (prof val w) (Fam (run nul choice a)))
            (Measure.pi μ) := (hoptI a).const_mul _
        have hEq : β * h a = (∫⁻ w, ENNReal.ofReal (β * optVal (prof val w)
            (Fam (run nul choice a))) ∂(Measure.pi μ)).toReal := by
          rw [hh, ← integral_const_mul]
          exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w =>
            mul_nonneg hβ (BP42.opt_bd val hval w _).1)
            StronglyMeasurable.of_discrete.aestronglyMeasurable
        rw [hEq]
        refine ENNReal.toReal_mono ?_ (lintegral_mono fun w => hD2 a b w)
        refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := β * n)) ?_
        calc ∫⁻ w, ENNReal.ofReal (β * optVal (prof val w) (Fam (run nul choice a)))
              ∂(Measure.pi μ) ≤ ∫⁻ _w, ENNReal.ofReal (β * n) ∂(Measure.pi μ) :=
              lintegral_mono fun w => ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_left (BP42.opt_bd val hval w _).2 hβ)
          _ = ENNReal.ofReal (β * n) := by simp
      have hwel : welfare (prof val b) (D a b) = ∑ i, val i (b i) (D a b i) := rfl
      rw [← hwel]
      nlinarith [mul_le_mul_of_nonneg_left hB2 hδ.le]
    -- integrals
    set Q := (Measure.pi μ).prod (Measure.pi μ) with hQ
    have hgI : ∀ i, Integrable (g i) Q := fun i =>
      BP42.intB _ _ _ _ (fun p => hg_bd i p)
    have hgsI : ∀ i, Integrable (fun p => g i (BP42.sw i p)) Q := fun i =>
      BP42.intB _ _ _ _ (fun p => hg_bd i (BP42.sw i p))
    have hUI : ∀ i, Integrable (fun v => utility nul val (postedPrice α β μ pv) choice v i)
        (Measure.pi μ) := fun i => BP42.intB _ _ 0 1 (fun v => hUb v i)
    have hRI : ∀ i, Integrable (fun v => (postedPrice α β μ pv i (run nul choice v i)
        (pre nul (run nul choice v) i)).toReal) (Measure.pi μ) := fun i =>
      BP42.intB _ _ 0 1 (fun v => hRb v i)
    have hhI : Integrable h (Measure.pi μ) := BP42.intB _ _ 0 n hhb
    -- utility part
    have hSU : ∫ v, ∑ i, utility nul val (postedPrice α β μ pv) choice v i ∂(Measure.pi μ) ≥
        (∫ v, h v ∂(Measure.pi μ)) - (ε + α / (1 + α * β) * (β * ∫ v, h v ∂(Measure.pi μ))) := by
      have e1 : ∫ v, ∑ i, utility nul val (postedPrice α β μ pv) choice v i ∂(Measure.pi μ) =
          ∫ p, ∑ i, utility nul val (postedPrice α β μ pv) choice p.1 i ∂Q := by
        rw [hQ, BP42.int_fst _ _ (fun v => ∑ i, utility nul val (postedPrice α β μ pv) choice v i)
          0 n]
        intro v
        constructor
        · exact Finset.sum_nonneg fun i _ => (hUb v i).1
        · calc ∑ i, utility nul val (postedPrice α β μ pv) choice v i ≤ ∑ _i : Fin n, (1:ℝ) :=
              Finset.sum_le_sum fun i _ => (hUb v i).2
            _ = n := by simp
      have e2 : ∫ p, ∑ i, g i p ∂Q ≤
          ∫ p, ∑ i, utility nul val (postedPrice α β μ pv) choice p.1 i ∂Q :=
        integral_mono (integrable_finsetSum _ fun i _ => hgI i)
          (integrable_finsetSum _ fun i _ => BP42.intB _ _ 0 1 (fun p => hUb p.1 i))
          (fun p => Finset.sum_le_sum fun i _ => hg_le i p)
      have e3 : ∫ p, ∑ i, g i p ∂Q = ∫ p, ∑ i, g i (BP42.sw i p) ∂Q := by
        rw [integral_finset_sum _ (fun i _ => hgI i),
          integral_finset_sum _ (fun i _ => hgsI i)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hQ]
        exact BP42.int_sw μ i (g i)
      have hkI : Integrable (fun p : (∀ i, V i) × (∀ i, V i) =>
          optVal (prof val p.2) (Fam (run nul choice p.1)) -
            (ε + α / (1 + α * β) * (β * h p.1))) Q := by
        refine BP42.intB _ _ (0 - (ε + α / (1 + α * β) * (β * n))) (n - ε) (fun p => ?_)
        have := BP42.opt_bd val hval p.2 (Fam (run nul choice p.1))
        have := hhb p.1
        have : 0 ≤ α / (1 + α * β) * (β * h p.1) := mul_nonneg hδ.le (mul_nonneg hβ (hhb p.1).1)
        have : α / (1 + α * β) * (β * h p.1) ≤ α / (1 + α * β) * (β * n) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hhb p.1).2 hβ) hδ.le
        constructor <;> linarith
      have e4 : ∫ p, (optVal (prof val p.2) (Fam (run nul choice p.1)) -
            (ε + α / (1 + α * β) * (β * h p.1))) ∂Q ≤ ∫ p, ∑ i, g i (BP42.sw i p) ∂Q :=
        integral_mono hkI (integrable_finsetSum _ fun i _ => hgsI i)
          (fun p => hlowsum p.1 p.2)
      have e5 : ∫ p, (optVal (prof val p.2) (Fam (run nul choice p.1)) -
            (ε + α / (1 + α * β) * (β * h p.1))) ∂Q =
          (∫ v, h v ∂(Measure.pi μ)) - (ε + α / (1 + α * β) * (β * ∫ v, h v ∂(Measure.pi μ))) := by
        rw [hQ, integral_prod _ hkI]
        have inner : ∀ v, ∫ w, (optVal (prof val w) (Fam (run nul choice v)) -
            (ε + α / (1 + α * β) * (β * h v))) ∂(Measure.pi μ) =
            h v - (ε + α / (1 + α * β) * (β * h v)) := by
          intro v
          rw [integral_sub (hoptI v) (integrable_const _), integral_const, hh]
          simp
        simp only [inner]
        rw [integral_sub hhI (by fun_prop), integral_add (integrable_const _)
          ((hhI.const_mul β).const_mul _), integral_const, integral_const_mul,
          integral_const_mul]
        simp
      linarith
    -- revenue part
    have hSR : ∫ v, ∑ i, (postedPrice α β μ pv i (run nul choice v i)
        (pre nul (run nul choice v) i)).toReal ∂(Measure.pi μ) ≥
        1 / (1 + α * β) * (WA - ∫ v, h v ∂(Measure.pi μ)) := by
      have hfI : Integrable (fun v => 1 / (1 + α * β) * (WA - h v)) (Measure.pi μ) :=
        ((integrable_const WA).sub hhI).const_mul _
      have := integral_mono hfI (integrable_finsetSum _ fun i _ => hRI i) hrev
      rw [integral_const_mul, integral_sub (integrable_const WA) hhI, integral_const] at this
      simpa using this
    have hE : ∫ v, welfare (prof val v) (run nul choice v) ∂(Measure.pi μ) =
        ∫ v, ∑ i, utility nul val (postedPrice α β μ pv) choice v i ∂(Measure.pi μ) +
        ∫ v, ∑ i, (postedPrice α β μ pv i (run nul choice v i)
          (pre nul (run nul choice v) i)).toReal ∂(Measure.pi μ) := by
      simp_rw [hW]
      exact integral_add (integrable_finsetSum _ fun i _ => hUI i)
        (integrable_finsetSum _ fun i _ => hRI i)
    have hcd : 1 / (1 + α * β) + α / (1 + α * β) * β = 1 := by
      field_simp
    have hH := congrArg (fun t => t * ∫ v, h v ∂(Measure.pi μ)) hcd
    rw [hE]
    nlinarith [hSU, hSR, hH]
  rw [← hWA]
  exact le_of_forall_pos_le_add hmain
