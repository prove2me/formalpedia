-- Prove2me | solution 3 for BartlettNN.Sigmoid.theorem28_part1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T02:43:03.640845+00:00
-- url     : https://prove2.me/submissions/ee1c8cdd-bd45-4a60-86ff-efbd627c83f1

import Mathlib
import Definitions.Def_BartlettNN_Sigmoid_Classification
import Definitions.Def_BartlettNN_Sigmoid_Networks
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction
import Definitions.Def_VapnikChervonenkis_Shared_deviation
import Theorems.Thm_Measurable_fin_append
import Theorems.Thm_Hoeffding_card_filter_sign_sum_le

-- carved verbatim out of submission 0f39c22d-cf6c-4cef-9f8e-35718ff87eba, lines 1342-1460

section
set_option autoImplicit false

open Classical in
noncomputable def b28HS {n K : ℕ} (x : Fin K → Fin n → ℝ) : Finset (Finset (Fin K)) :=
  Finset.univ.filter fun T => ∃ (a : Fin n → ℝ) (c : ℝ), ∀ k, k ∈ T ↔ c < ∑ i, a i * x k i

noncomputable def b28b {n : ℕ} (q : (Fin n → ℚ) × ℚ) (x : Fin n → ℝ) : ℝ :=
  if (q.2 : ℝ) < ∑ i, (q.1 i : ℝ) * x i then 1 else -1

noncomputable def b28g {n N : ℕ} (A : ℝ) (θ : Fin N → Bool × ((Fin n → ℚ) × ℚ))
    (x : Fin n → ℝ) : ℝ :=
  A / N * ∑ r, BartlettNN.Margin.pm (θ r).1 * b28b (θ r).2 x

def b28S (n N : ℕ) (A γ : ℝ) : Set (Set ((Fin n → ℝ) × Bool)) :=
  Set.range fun θ : Fin N → Bool × ((Fin n → ℚ) × ℚ) =>
    {p | BartlettNN.Margin.pm p.2 * b28g A θ p.1 < γ / 2}

def b28S0 : Set (Set ((Fin 0 → ℝ) × Bool)) := {{p | p.2 = false}, {p | p.2 = true}}

lemma b28S0_countable : b28S0.Countable :=
  (Set.countable_singleton _).insert _

lemma b28S0_growth (K : ℕ) : (VapnikChervonenkis.Shared.growthFunction b28S0 K : ℝ) ≤ 2 := by
  classical
  have hle : ∀ x : Fin K → (Fin 0 → ℝ) × Bool, VapnikChervonenkis.Shared.index b28S0 x ≤ 2 := by
    intro x
    unfold VapnikChervonenkis.Shared.index
    refine le_trans (Finset.card_le_card (t := {Finset.univ.filter fun i => (x i).2 = false,
      Finset.univ.filter fun i => (x i).2 = true}) ?_) Finset.card_le_two
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    obtain ⟨C, hC, hCt⟩ := ht
    rcases hC with rfl | rfl
    · refine Finset.mem_insert.2 (Or.inl ?_)
      ext i; rw [hCt i]; simp
    · refine Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 ?_))
      ext i; rw [hCt i]; simp
  have h2 : VapnikChervonenkis.Shared.growthFunction b28S0 K ≤ 2 := by
    unfold VapnikChervonenkis.Shared.growthFunction
    exact ciSup_le hle
  exact_mod_cast h2

lemma b28S0_meas : ∀ C ∈ b28S0, MeasurableSet C := by
  intro C hC
  rcases hC with rfl | rfl
  · exact measurable_snd (measurableSet_singleton false)
  · exact measurable_snd (measurableSet_singleton true)

lemma b28S_countable (n N : ℕ) (A γ : ℝ) : (b28S n N A γ).Countable := Set.countable_range _

lemma b28_isLinear {n : ℕ} (a : Fin n → ℝ) : IsLinearMap ℝ (fun v : Fin n → ℝ => ∑ i, a i * v i) := by
  constructor
  · intro u v; simp [mul_add, Finset.sum_add_distrib]
  · intro r v; simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

lemma b28_hs_shatter_le {n K : ℕ} (x : Fin K → Fin n → ℝ) (t : Finset (Fin K))
    (ht : (b28HS x).Shatters t) : t.card ≤ n + 1 := by
  classical
  by_contra hlt
  push_neg at hlt
  set f : t → (Fin n → ℝ) := fun k => x k with hf
  have hnot : ¬ AffineIndependent ℝ f := by
    intro hai
    have h1 := hai.card_le_finrank_succ
    rw [Fintype.card_coe] at h1
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range f))
    rw [Module.finrank_fin_fun] at h2
    omega
  obtain ⟨I, p, hp1, hp2⟩ := Convex.radon_partition hnot
  set t' : Finset (Fin K) := (t.attach.filter fun k => k ∈ I).map (Function.Embedding.subtype _)
    with ht'
  have hsub : t' ⊆ t := by
    intro k hk
    simp only [ht', Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
      Function.Embedding.coe_subtype] at hk
    obtain ⟨j, _, rfl⟩ := hk
    exact j.2
  obtain ⟨u, hu, htu⟩ := ht hsub
  simp only [b28HS, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  obtain ⟨a, c, hac⟩ := hu
  set φ : (Fin n → ℝ) → ℝ := fun v => ∑ i, a i * v i with hφ
  have hin : f '' I ⊆ {v | c < φ v} := by
    rintro _ ⟨j, hj, rfl⟩
    have hj' : (j : Fin K) ∈ t' := by
      simp only [ht', Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
        Function.Embedding.coe_subtype]
      exact ⟨j, hj, rfl⟩
    rw [← htu] at hj'
    exact (hac j).1 (Finset.mem_inter.1 hj').2
  have hout : f '' Iᶜ ⊆ {v | φ v ≤ c} := by
    rintro _ ⟨j, hj, rfl⟩
    show φ (x j) ≤ c
    by_contra hcon
    push_neg at hcon
    have hju : (j : Fin K) ∈ u := (hac j).2 hcon
    have hjt : (j : Fin K) ∈ t ∩ u := Finset.mem_inter.2 ⟨j.2, hju⟩
    rw [htu] at hjt
    simp only [ht', Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
      Function.Embedding.coe_subtype] at hjt
    obtain ⟨j', hj'I, hj'eq⟩ := hjt
    have : j' = j := Subtype.ext hj'eq
    subst this
    exact hj hj'I
  have h1 := convexHull_min hin (convex_halfSpace_gt (b28_isLinear a) c) hp1
  have h2 := convexHull_min hout (convex_halfSpace_le (b28_isLinear a) c) hp2
  simp only [Set.mem_setOf_eq] at h1 h2
  linarith

lemma b28_hs_card {n K : ℕ} (x : Fin K → Fin n → ℝ) : (b28HS x).card ≤ (K + 1) ^ (n + 1) := by
  classical
  have hvc : (b28HS x).vcDim ≤ n + 1 := by
    unfold Finset.vcDim
    refine Finset.sup_le fun s hs => ?_
    exact b28_hs_shatter_le x s (Finset.mem_shatterer.1 hs)
  calc (b28HS x).card ≤ (b28HS x).shatterer.card := Finset.card_le_card_shatterer _
    _ ≤ ∑ k ∈ Finset.Iic (b28HS x).vcDim, (Fintype.card (Fin K)).choose k :=
        Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ Finset.Iic (n + 1), K.choose k := by
        rw [Fintype.card_fin]
        exact Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.2 hvc)
    _ ≤ ∑ k ∈ Finset.range (n + 1 + 1), K ^ k * 1 ^ (n + 1 - k) * (n + 1).choose k := by
        have hI : Finset.Iic (n + 1) = Finset.range (n + 1 + 1) := by
          ext k; simp [Nat.lt_succ_iff]
        rw [hI]
        refine Finset.sum_le_sum fun k hk => ?_
        have h1 := Nat.choose_le_pow K k
        have h2 : 1 ≤ (n + 1).choose k :=
          Nat.choose_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
        calc K.choose k ≤ K ^ k := h1
          _ = K ^ k * 1 ^ (n + 1 - k) * 1 := by simp
          _ ≤ K ^ k * 1 ^ (n + 1 - k) * (n + 1).choose k := Nat.mul_le_mul_left _ h2
    _ = (K + 1) ^ (n + 1) := (add_pow K 1 (n + 1)).symm

lemma b28S_growth (n N : ℕ) (A γ : ℝ) (K : ℕ) :
    (VapnikChervonenkis.Shared.growthFunction (b28S n N A γ) K : ℝ)
      ≤ 2 ^ N * (((K : ℝ) + 1) ^ (n + 1)) ^ N := by
  classical
  have hle : ∀ x : Fin K → (Fin n → ℝ) × Bool,
      VapnikChervonenkis.Shared.index (b28S n N A γ) x ≤ 2 ^ N * ((K + 1) ^ (n + 1)) ^ N := by
    intro x
    set xs : Fin K → Fin n → ℝ := fun i => (x i).1 with hxs
    set F : (Fin N → Bool) × (Fin N → Finset (Fin K)) → Finset (Fin K) := fun ετ =>
      Finset.univ.filter fun i => BartlettNN.Margin.pm (x i).2 *
        (A / N * ∑ r, BartlettNN.Margin.pm (ετ.1 r) * (if i ∈ ετ.2 r then (1 : ℝ) else -1)) < γ / 2
      with hF
    have hsub : (Finset.univ.filter fun t : Finset (Fin K) =>
        ∃ C ∈ b28S n N A γ, ∀ i, i ∈ t ↔ x i ∈ C) ⊆
        ((Finset.univ : Finset (Fin N → Bool)) ×ˢ
          Fintype.piFinset (fun _ : Fin N => b28HS xs)).image F := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      obtain ⟨C, ⟨θ, rfl⟩, hC⟩ := ht
      refine Finset.mem_image.2 ⟨(fun r => (θ r).1, fun r => Finset.univ.filter fun i =>
        ((θ r).2.2 : ℝ) < ∑ j, ((θ r).2.1 j : ℝ) * xs i j), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_univ, true_and, Fintype.mem_piFinset]
        intro r
        simp only [b28HS, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun j => ((θ r).2.1 j : ℝ), ((θ r).2.2 : ℝ), fun i => Iff.rfl⟩
      · ext i
        rw [hC i]
        simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, b28g,
          b28b, hxs]
    calc VapnikChervonenkis.Shared.index (b28S n N A γ) x
        ≤ (((Finset.univ : Finset (Fin N → Bool)) ×ˢ
          Fintype.piFinset (fun _ : Fin N => b28HS xs)).image F).card := Finset.card_le_card hsub
      _ ≤ ((Finset.univ : Finset (Fin N → Bool)) ×ˢ
          Fintype.piFinset (fun _ : Fin N => b28HS xs)).card := Finset.card_image_le
      _ = 2 ^ N * (b28HS xs).card ^ N := by
          rw [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]
      _ ≤ 2 ^ N * ((K + 1) ^ (n + 1)) ^ N :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (b28_hs_card xs) N)
  have h2 : VapnikChervonenkis.Shared.growthFunction (b28S n N A γ) K
      ≤ 2 ^ N * ((K + 1) ^ (n + 1)) ^ N := by
    unfold VapnikChervonenkis.Shared.growthFunction
    exact ciSup_le hle
  exact_mod_cast h2

lemma b28_pm_meas {X : Type*} [MeasurableSpace X] :
    Measurable (fun p : X × Bool => BartlettNN.Margin.pm p.2) :=
  (Measurable.of_discrete (f := BartlettNN.Margin.pm)).comp measurable_snd

lemma b28b_meas {n : ℕ} (q : (Fin n → ℚ) × ℚ) : Measurable (b28b q) := by
  unfold b28b
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt measurable_const
    (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _)

lemma b28g_meas {n N : ℕ} (A : ℝ) (θ : Fin N → Bool × ((Fin n → ℚ) × ℚ)) :
    Measurable (b28g A θ) := by
  unfold b28g
  exact (Finset.measurable_sum _ fun r _ => (b28b_meas _).const_mul _).const_mul _

lemma b28S_meas (n N : ℕ) (A γ : ℝ) : ∀ C ∈ b28S n N A γ, MeasurableSet C := by
  rintro _ ⟨θ, rfl⟩
  exact measurableSet_lt (b28_pm_meas.mul ((b28g_meas A θ).comp measurable_fst)) measurable_const

open MeasureTheory VapnikChervonenkis.Shared in
lemma b28_relFreq_meas {Y : Type*} [MeasurableSpace Y] (A : Set Y) (hA : MeasurableSet A) (l : ℕ)
    {Z : Type*} [MeasurableSpace Z] (f : Z → Fin l → Y) (hf : ∀ i, Measurable fun z => f z i) :
    Measurable fun z => relFreq A (f z) := by
  classical
  unfold relFreq
  refine Measurable.div_const ?_ _
  have : (fun z => ((Finset.univ.filter fun i => f z i ∈ A).card : ℝ))
      = fun z => ∑ i : Fin l, A.indicator (fun _ => (1 : ℝ)) (f z i) := by
    funext z
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : f z i ∈ A <;> simp [Set.indicator_apply, h]
  rw [this]
  exact Finset.measurable_sum _ fun i _ => (measurable_const.indicator hA).comp (hf i)

open MeasureTheory VapnikChervonenkis.Shared in
lemma b28_rho_meas {Y : Type*} [MeasurableSpace Y] (S : Set (Set Y)) (hS : S.Countable)
    (hSm : ∀ A ∈ S, MeasurableSet A) (l : ℕ) : Measurable (semiSampleDeviation S l) := by
  have hc : Countable S := hS.to_subtype
  have hf : ∀ A : S, Measurable fun x : Fin (l + l) → Y =>
      |relFreq (A : Set Y) (fun i : Fin l => x (Fin.castAdd l i))
        - relFreq (A : Set Y) (fun i : Fin l => x (Fin.natAdd l i))| := by
    intro A
    have h1 : Measurable fun x : Fin (l + l) → Y => relFreq (A : Set Y) (fun i : Fin l => x (Fin.castAdd l i)) :=
      b28_relFreq_meas (Z := Fin (l + l) → Y) (A : Set Y) (hSm A A.2) l
        (fun x i => x (Fin.castAdd l i)) (fun i => measurable_pi_apply (Fin.castAdd l i))
    have h2 : Measurable fun x : Fin (l + l) → Y => relFreq (A : Set Y) (fun i : Fin l => x (Fin.natAdd l i)) :=
      b28_relFreq_meas (Z := Fin (l + l) → Y) (A : Set Y) (hSm A A.2) l
        (fun x i => x (Fin.natAdd l i)) (fun i => measurable_pi_apply (Fin.natAdd l i))
    exact (h1.sub h2).abs
  exact Measurable.iSup hf

open MeasureTheory ProbabilityTheory in
lemma vc47_cheb {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (A : Set X) (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) (l : ℕ)
    (hl : 2 / ε ^ 2 ≤ (l : ℝ)) :
    (1 / 2 : ENNReal) ≤ (Measure.pi fun _ : Fin l ↦ P)
      {y | |VapnikChervonenkis.Shared.relFreq A y - P.real A| ≤ ε / 2} := by
  classical
  set μ : Measure (Fin l → X) := Measure.pi fun _ : Fin l ↦ P with hμ
  set p : ℝ := P.real A with hp
  have hlε : 2 ≤ (l : ℝ) * ε ^ 2 := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)).1 hl
    exact this
  have hlpos : (0 : ℝ) < l := by
    by_contra h0
    have h0' := not_lt.1 h0
    nlinarith [sq_nonneg ε, mul_nonneg (Nat.cast_nonneg l : (0 : ℝ) ≤ l) (sq_nonneg ε)]
  set f : X → ℝ := A.indicator 1 with hf
  have hfm : Measurable f := measurable_one.indicator hA
  have hf01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x; simp only [hf, Set.indicator_apply, Pi.one_apply]; split_ifs <;> norm_num
  have hfL2 : MemLp f 2 P :=
    MemLp.of_bound hfm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hf01 x).1, (hf01 x).2])
  have hfint : ∫ x, f x ∂P = p := by
    rw [hf, integral_indicator_one hA]
  set N : (Fin l → X) → ℝ := ∑ i, fun y : Fin l → X => f (y i) with hN
  have hNapp : ∀ y, N y = ∑ i, f (y i) := fun y => by simp [hN, Finset.sum_apply]
  have hrf : ∀ y : Fin l → X, VapnikChervonenkis.Shared.relFreq A y = N y / l := by
    intro y
    unfold VapnikChervonenkis.Shared.relFreq
    rw [Finset.card_filter, Nat.cast_sum, hNapp]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : y i ∈ A <;> simp [hf, Set.indicator_apply, h]
  have hNm : Measurable N := by
    have : N = fun y => ∑ i, f (y i) := funext hNapp
    rw [this]; exact Finset.measurable_sum _ (fun i _ => hfm.comp (measurable_pi_apply i))
  have hNL2 : MemLp N 2 μ :=
    MemLp.of_bound hNm.aestronglyMeasurable l (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, hNapp]
      calc |∑ i, f (y i)| ≤ ∑ i, |f (y i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin l, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
            rw [abs_le]; constructor <;> linarith [(hf01 (y i)).1, (hf01 (y i)).2]
        _ = l := by simp)
  have hmean : μ[N] = l * p := by
    simp_rw [hNapp]
    rw [integral_finsetSum _ (fun i _ => ?_)]
    · rw [Finset.sum_congr rfl fun i _ =>
        integral_comp_eval (μ := fun _ : Fin l => P) (i := i) hfm.aestronglyMeasurable]
      simp [hfint]
    · exact integrable_comp_eval (μ := fun _ : Fin l => P) (hfL2.integrable one_le_two)
  have hvar : Var[N; μ] ≤ l * (1 / 4) := by
    have hv := variance_sum_pi (μ := fun _ : Fin l => P) (X := fun _ => f) (fun _ => hfL2)
    rw [hN, hv]
    have hv1 : Var[f; P] ≤ 1 / 4 := by
      have := variance_le_sub_mul_sub (μ := P) (a := 0) (b := 1)
        (Filter.Eventually.of_forall hf01) hfm.aemeasurable
      rw [hfint] at this
      nlinarith [sq_nonneg (p - 1 / 2)]
    calc ∑ _i : Fin l, Var[f; P] ≤ ∑ _i : Fin l, (1 / 4 : ℝ) := Finset.sum_le_sum fun _ _ => hv1
      _ = l * (1 / 4) := by simp
  set cc : ℝ := l * ε / 2 with hcc
  have hc : 0 < cc := by positivity
  have hcheb := meas_ge_le_variance_div_sq hNL2 hc
  set G : Set (Fin l → X) :=
    {y | |VapnikChervonenkis.Shared.relFreq A y - p| ≤ ε / 2} with hGdef
  have hsub : Gᶜ ⊆ {ω | cc ≤ |N ω - μ[N]|} := by
    intro y hy
    simp only [hGdef, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, hrf] at hy ⊢
    have h1 : |N y - μ[N]| = l * |N y / l - p| := by
      rw [hmean, show N y - l * p = l * (N y / l - p) by field_simp, abs_mul,
        abs_of_pos hlpos]
    rw [h1, hcc]
    have := mul_le_mul_of_nonneg_left hy.le hlpos.le
    linarith
  have hbound : ENNReal.ofReal (Var[N; μ] / cc ^ 2) ≤ 1 / 2 := by
    rw [show (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ (by positivity)]
    rw [hcc]
    have h2 : (l : ℝ) * (1 / 4) ≤ 1 / 2 * (l * ε / 2) ^ 2 := by
      have : (l : ℝ) * ε ^ 2 ≥ 2 := hlε
      nlinarith [mul_pos hlpos hlpos]
    linarith
  have hG : MeasurableSet G := by
    have : G = {y | |N y / l - p| ≤ ε / 2} := by
      ext y; simp only [hGdef, Set.mem_ofPred_eq, hrf]
    rw [this]
    exact measurableSet_le (continuous_abs.measurable.comp
      ((hNm.div_const _).sub_const _)) measurable_const
  have hcompl : μ Gᶜ ≤ 1 / 2 := (measure_mono hsub).trans (hcheb.trans hbound)
  have htot := measure_add_measure_compl (μ := μ) hG
  rw [measure_univ] at htot
  have h1 : μ G + μ Gᶜ ≤ μ G + 1 / 2 := add_le_add le_rfl hcompl
  rw [htot] at h1
  have h1' : (1 / 2 : ENNReal) + 1 / 2 ≤ μ G + 1 / 2 := by
    rw [ENNReal.add_halves]; exact h1
  exact ENNReal.le_of_add_le_add_right (by simp) h1'

open VapnikChervonenkis.Shared in
lemma vc47_index_le_growth {X : Type*} (S : Set (Set X)) (r : ℕ) (x : Fin r → X) :
    index S x ≤ growthFunction S r := by
  classical
  unfold growthFunction
  refine le_ciSup (f := fun x : Fin r → X => index S x) ?_ x
  refine ⟨2 ^ r, ?_⟩
  rintro _ ⟨y, rfl⟩
  show index S y ≤ 2 ^ r
  unfold index
  refine (Finset.card_filter_le _ _).trans ?_
  simp

lemma vc47_rho_eq {X : Type*} (S : Set (Set X)) (l : ℕ) (p : (Fin l → X) × (Fin l → X)) :
    VapnikChervonenkis.Shared.semiSampleDeviation S l (Fin.append p.1 p.2)
      = ⨆ A : S, |VapnikChervonenkis.Shared.relFreq (A : Set X) p.1
          - VapnikChervonenkis.Shared.relFreq (A : Set X) p.2| := by
  unfold VapnikChervonenkis.Shared.semiSampleDeviation
  simp only [Fin.append_left, Fin.append_right]

def vc47_swap {X : Type*} {m : ℕ} (σ : Fin m → Bool) (p : (Fin m → X) × (Fin m → X)) :
    (Fin m → X) × (Fin m → X) :=
  (fun i => if σ i then p.2 i else p.1 i, fun i => if σ i then p.1 i else p.2 i)

open VapnikChervonenkis.Shared in
lemma vc47_count {X : Type*} (S : Set (Set X)) (l : ℕ) (hl1 : 1 ≤ l) {ε : ℝ} (hε : 0 < ε)
    (p : (Fin l → X) × (Fin l → X)) :
    ((Finset.univ.filter fun σ : Fin l → Bool =>
        ε / 2 < semiSampleDeviation S l
          (Fin.append (vc47_swap σ p).1 (vc47_swap σ p).2)).card : ℝ)
      ≤ (growthFunction S (l + l) : ℝ)
        * (2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8)))) := by
  classical
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl1
  set x : Fin (l + l) → X := Fin.append p.1 p.2 with hx
  set T : Finset (Finset (Fin (l + l))) :=
    Finset.univ.filter (fun t : Finset (Fin (l + l)) => ∃ A ∈ S, ∀ i, i ∈ t ↔ x i ∈ A) with hT
  have hTcard : T.card = index S x := by
    unfold index
    first | rfl | congr
  set c : Finset (Fin (l + l)) → Fin l → ℝ := fun t i =>
    (if Fin.castAdd l i ∈ t then (1 : ℝ) else 0) - (if Fin.natAdd l i ∈ t then (1 : ℝ) else 0)
    with hc
  have hc1 : ∀ t i, |c t i| ≤ 1 := by
    intro t i
    simp only [hc]
    rw [abs_le]
    by_cases h1 : Fin.castAdd l i ∈ t <;> by_cases h2 : Fin.natAdd l i ∈ t <;>
      simp only [h1, h2, if_true, if_false, ↓reduceIte] <;> norm_num
  set Bad : Finset (Fin (l + l)) → Finset (Fin l → Bool) := fun t =>
    Finset.univ.filter (fun σ : Fin l → Bool =>
      (l : ℝ) * (ε / 2) ≤ |∑ i, (if σ i then (1 : ℝ) else -1) * c t i|) with hBad
  have hBadcard : ∀ t, ((Bad t).card : ℝ) ≤ 2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8))) := by
    intro t
    have hexp : (l * (ε / 2)) ^ 2 / (2 * (l : ℝ)) = ε ^ 2 * l / 8 := by
      field_simp; ring
    have hnn : 0 ≤ (l : ℝ) * (ε / 2) := by positivity
    have h1 := Hoeffding.card_filter_sign_sum_le hl1 (c t) (hc1 t) hnn
    have h2 := Hoeffding.card_filter_sign_sum_le hl1 (fun i => - c t i)
      (fun i => by simpa [abs_neg] using hc1 t i) hnn
    beta_reduce at h2
    rw [hexp] at h1 h2
    have hsub : Bad t ⊆
        (Finset.univ.filter fun s : Fin l → Bool =>
          (l : ℝ) * (ε / 2) ≤ ∑ i, (if s i then (1 : ℝ) else -1) * c t i) ∪
        (Finset.univ.filter fun s : Fin l → Bool =>
          (l : ℝ) * (ε / 2) ≤ ∑ i, (if s i then (1 : ℝ) else -1) * (- c t i)) := by
      intro σ hσ
      simp only [hBad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hσ ⊢
      have hneg : ∑ i, (if σ i then (1 : ℝ) else -1) * (- c t i)
          = - ∑ i, (if σ i then (1 : ℝ) else -1) * c t i := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hneg]
      rcases le_abs'.1 hσ with h | h
      · right; linarith
      · left; linarith
    have := (Nat.cast_le (α := ℝ)).2 ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
    push_cast at this
    linarith
  have hsubset : (Finset.univ.filter fun σ : Fin l → Bool =>
        ε / 2 < semiSampleDeviation S l
          (Fin.append (vc47_swap σ p).1 (vc47_swap σ p).2)) ⊆ T.biUnion Bad := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    rw [vc47_rho_eq S l (vc47_swap σ p)] at hσ
    have hne : Nonempty S := by
      by_contra h
      rw [not_nonempty_iff] at h
      rw [Real.iSup_of_isEmpty] at hσ
      linarith
    obtain ⟨A, hA⟩ := exists_lt_of_lt_ciSup hσ
    refine Finset.mem_biUnion.2 ⟨Finset.univ.filter (fun j : Fin (l + l) => x j ∈ (A : Set X)), ?_, ?_⟩
    · simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨A, A.2, fun i => by simp⟩
    · simp only [hBad, Finset.mem_filter, Finset.mem_univ, true_and]
      set tA : Finset (Fin (l + l)) := Finset.univ.filter (fun j : Fin (l + l) => x j ∈ (A : Set X))
        with htA
      have hmem_l : ∀ i : Fin l, Fin.castAdd l i ∈ tA ↔ p.1 i ∈ (A : Set X) := by
        intro i
        simp only [htA, Finset.mem_filter, Finset.mem_univ, true_and, hx, Fin.append_left]
      have hmem_r : ∀ i : Fin l, Fin.natAdd l i ∈ tA ↔ p.2 i ∈ (A : Set X) := by
        intro i
        simp only [htA, Finset.mem_filter, Finset.mem_univ, true_and, hx, Fin.append_right]
      have hci : ∀ i : Fin l, c tA i
          = (if p.1 i ∈ (A : Set X) then (1 : ℝ) else 0) - (if p.2 i ∈ (A : Set X) then (1 : ℝ) else 0) := by
        intro i
        simp only [hc, hmem_l i, hmem_r i]
      have hdiff : VapnikChervonenkis.Shared.relFreq (A : Set X) (vc47_swap σ p).1
          - VapnikChervonenkis.Shared.relFreq (A : Set X) (vc47_swap σ p).2
          = - (∑ i, (if σ i then (1 : ℝ) else -1) * c tA i) / l := by
        unfold VapnikChervonenkis.Shared.relFreq
        rw [Finset.card_filter, Finset.card_filter, Nat.cast_sum, Nat.cast_sum, ← sub_div,
          ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hci i]
        by_cases h : σ i <;> by_cases h1 : p.1 i ∈ (A : Set X) <;>
          by_cases h2 : p.2 i ∈ (A : Set X) <;>
          simp [vc47_swap, h, h1, h2]
      rw [hdiff, abs_div, abs_neg, abs_of_pos hlpos, lt_div_iff₀ hlpos] at hA
      linarith
  have hcard1 := Finset.card_le_card hsubset
  have hcard2 := hcard1.trans Finset.card_biUnion_le
  have hcard3 : ((Finset.univ.filter fun σ : Fin l → Bool =>
        ε / 2 < semiSampleDeviation S l
          (Fin.append (vc47_swap σ p).1 (vc47_swap σ p).2)).card : ℝ)
      ≤ ∑ t ∈ T, ((Bad t).card : ℝ) := by
    exact_mod_cast hcard2
  calc _ ≤ ∑ t ∈ T, ((Bad t).card : ℝ) := hcard3
    _ ≤ ∑ _t ∈ T, 2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8))) :=
        Finset.sum_le_sum fun t _ => hBadcard t
    _ = (T.card : ℝ) * (2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hTcard]
        exact_mod_cast vc47_index_le_growth S (l + l) x

open MeasureTheory in
lemma vc47_swap_mp {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    {m : ℕ} (σ : Fin m → Bool) :
    MeasurePreserving (vc47_swap σ)
      ((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin m => D))
      ((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin m => D)) := by
  let E := MeasurableEquiv.arrowProdEquivProdArrow X X (Fin m)
  have hE : MeasurePreserving E (Measure.pi fun _ : Fin m => D.prod D)
      ((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin m => D)) :=
    measurePreserving_arrowProdEquivProdArrow X X (Fin m) (fun _ => D) (fun _ => D)
  let f : Fin m → X × X → X × X := fun i => if σ i then Prod.swap else id
  have hf : ∀ i, MeasurePreserving (f i) (D.prod D) (D.prod D) := by
    intro i
    by_cases h : σ i
    · simp only [f, h, if_true]; exact Measure.measurePreserving_swap
    · simp only [f, h]; exact MeasurePreserving.id _
  have hF := measurePreserving_pi (fun _ : Fin m => D.prod D) (fun _ : Fin m => D.prod D) hf
  have hcomp := hE.comp (hF.comp hE.symm)
  have heq : vc47_swap σ = E ∘ ((fun a i => f i (a i)) ∘ E.symm) := by
    funext p
    ext i
    · by_cases h : σ i <;> simp [vc47_swap, f, h, E, MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.arrowProdEquivProdArrow]
    · by_cases h : σ i <;> simp [vc47_swap, f, h, E, MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.arrowProdEquivProdArrow]
  rw [heq]; exact hcomp

open MeasureTheory VapnikChervonenkis.Shared in
lemma vc47_perm {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (l : ℕ) (hl1 : 1 ≤ l)
    (hρ : Measurable (semiSampleDeviation S l)) {ε : ℝ} (hε : 0 < ε) :
    ((Measure.pi fun _ : Fin l => P).prod (Measure.pi fun _ : Fin l => P))
        {p | ε / 2 < semiSampleDeviation S l (Fin.append p.1 p.2)}
      ≤ ENNReal.ofReal (2 * (growthFunction S (l + l) : ℝ) * Real.exp (-(ε ^ 2 * l / 8))) := by
  classical
  set μ2 := (Measure.pi fun _ : Fin l => P).prod (Measure.pi fun _ : Fin l => P) with hμ2
  set B : Set ((Fin l → X) × (Fin l → X)) :=
    {p | ε / 2 < semiSampleDeviation S l (Fin.append p.1 p.2)} with hBdef
  have hB : MeasurableSet B :=
    measurableSet_lt measurable_const (hρ.comp (Measurable.fin_append l))
  have hswapm : ∀ σ : Fin l → Bool, Measurable (vc47_swap (X := X) σ) :=
    fun σ => (vc47_swap_mp P σ).measurable
  have h1 : ∀ σ : Fin l → Bool, μ2 ((vc47_swap σ) ⁻¹' B) = μ2 B :=
    fun σ => (vc47_swap_mp P σ).measure_preimage hB.nullMeasurableSet
  have hsum : ∫⁻ p, ((Finset.univ.filter fun σ : Fin l → Bool =>
        p ∈ (vc47_swap σ) ⁻¹' B).card : ENNReal) ∂μ2 = ∑ _σ : Fin l → Bool, μ2 B := by
    have : ∀ p, ((Finset.univ.filter fun σ : Fin l → Bool =>
        p ∈ (vc47_swap σ) ⁻¹' B).card : ENNReal)
        = ∑ σ : Fin l → Bool, ((vc47_swap σ) ⁻¹' B).indicator (fun _ => (1 : ENNReal)) p := by
      intro p
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun σ _ => ?_
      by_cases h : p ∈ (vc47_swap σ) ⁻¹' B <;> simp [Set.indicator_apply, h]
    simp_rw [this]
    rw [lintegral_finset_sum _ (fun σ _ => measurable_const.indicator ((hswapm σ) hB))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [lintegral_indicator_const ((hswapm σ) hB), one_mul, h1 σ]
  set K : ℝ := (growthFunction S (l + l) : ℝ)
    * (2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8)))) with hK
  have hint : ∫⁻ p, ((Finset.univ.filter fun σ : Fin l → Bool =>
        p ∈ (vc47_swap σ) ⁻¹' B).card : ENNReal) ∂μ2 ≤ ENNReal.ofReal K := by
    calc _ ≤ ∫⁻ _p, ENNReal.ofReal K ∂μ2 := by
          refine lintegral_mono fun p => ?_
          have := vc47_count S l hl1 hε p
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal this
      _ = ENNReal.ofReal K := by simp
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul] at hint
  have hK2 : ENNReal.ofReal K = (2 : ENNReal) ^ l *
      ENNReal.ofReal (2 * (growthFunction S (l + l) : ℝ) * Real.exp (-(ε ^ 2 * l / 8))) := by
    have : K = (2 : ℝ) ^ l * (2 * (growthFunction S (l + l) : ℝ) * Real.exp (-(ε ^ 2 * l / 8))) := by
      rw [hK]; ring
    rw [this, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp
  rw [hK2] at hint
  push_cast at hint
  exact (ENNReal.mul_le_mul_iff_right (by positivity) (by simp)).1 hint

lemma vc47_relFreq_bounds {X : Type*} (A : Set X) {l : ℕ} (hl : 1 ≤ l) (x : Fin l → X) :
    0 ≤ VapnikChervonenkis.Shared.relFreq A x ∧ VapnikChervonenkis.Shared.relFreq A x ≤ 1 := by
  classical
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  unfold VapnikChervonenkis.Shared.relFreq
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hlpos]
  have := Finset.card_filter_le (Finset.univ : Finset (Fin l)) (fun i => x i ∈ A)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  exact_mod_cast this

open MeasureTheory VapnikChervonenkis.Shared in
lemma b28_abstract {Y : Type*} [MeasurableSpace Y] (P : Measure Y) [IsProbabilityMeasure P]
    (S : Set (Set Y)) (hS : S.Countable) (hSm : ∀ A ∈ S, MeasurableSet A) (l : ℕ)
    {s : ℝ} (hs : 0 < s) (hl : 2 / s ^ 2 ≤ (l : ℝ)) (E : Set (Fin l → Y)) (hE : MeasurableSet E)
    (hcov : ∀ x ∈ E, ∃ M : Set Y, MeasurableSet M ∧ ∃ a : ℝ, a + s ≤ P.real M ∧
      ∀ y : Fin l → Y, ∃ A ∈ S, relFreq A x ≤ a ∧ relFreq M y ≤ relFreq A y) :
    Measure.pi (fun _ : Fin l => P) E
      ≤ ENNReal.ofReal (4 * (growthFunction S (l + l) : ℝ) * Real.exp (-((s / 2) ^ 2 * l / 8))) := by
  classical
  have hl1 : 1 ≤ l := by
    have : (0 : ℝ) < l := lt_of_lt_of_le (by positivity) hl
    exact_mod_cast this
  have hρ := b28_rho_meas S hS hSm l
  set Q : Measure (Fin l → Y) := Measure.pi fun _ : Fin l => P with hQ
  set B : Set ((Fin l → Y) × (Fin l → Y)) :=
    {p | (s / 2) / 2 < semiSampleDeviation S l (Fin.append p.1 p.2)} with hBdef
  have hB : MeasurableSet B :=
    measurableSet_lt measurable_const (hρ.comp (Measurable.fin_append l))
  have key : (1 / 2 : ENNReal) * Q E ≤ (Q.prod Q) B := by
    rw [Measure.prod_apply hB]
    refine le_trans (le_of_eq (lintegral_indicator_const hE (1 / 2 : ENNReal)).symm)
      (lintegral_mono fun x => ?_)
    by_cases hx : x ∈ E
    · rw [Set.indicator_apply, if_pos hx]
      obtain ⟨M, hM, a, ha, hA⟩ := hcov x hx
      refine le_trans (vc47_cheb P M hM hs l hl) (measure_mono ?_)
      intro y hy
      have hy' : |relFreq M y - P.real M| ≤ s / 2 := hy
      show (s / 2) / 2 < semiSampleDeviation S l (Fin.append x y)
      have := vc47_rho_eq S l (x, y)
      simp only at this
      rw [this]
      obtain ⟨A, hAS, hA1, hA2⟩ := hA y
      have hbdd : BddAbove (Set.range fun A : S =>
          |relFreq (A : Set Y) x - relFreq (A : Set Y) y|) := by
        refine ⟨1, ?_⟩
        rintro _ ⟨A', rfl⟩
        have h1 := vc47_relFreq_bounds (A' : Set Y) hl1 x
        have h2 := vc47_relFreq_bounds (A' : Set Y) hl1 y
        show |_| ≤ 1
        rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      have h3 := le_ciSup hbdd ⟨A, hAS⟩
      have h4 : relFreq A y - relFreq A x ≤ |relFreq A x - relFreq A y| := by
        rw [abs_sub_comm]; exact le_abs_self _
      have h5 := (abs_le.1 hy').1
      simp only at h3
      linarith
    · rw [Set.indicator_apply, if_neg hx]; exact zero_le
  have h2 := vc47_perm P S l hl1 hρ (ε := s / 2) (by positivity)
  have hQE : Q E = 2 * ((1 / 2 : ENNReal) * Q E) := by
    rw [← mul_assoc, one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  rw [hQE]
  calc 2 * ((1 / 2 : ENNReal) * Q E) ≤ 2 * (Q.prod Q) B := by gcongr
    _ ≤ 2 * ENNReal.ofReal (2 * (growthFunction S (l + l) : ℝ) * Real.exp (-((s / 2) ^ 2 * l / 8))) :=
        by gcongr
    _ = _ := by
        rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

lemma b28_layer (v : ℝ) (hv : v ∈ Set.Icc (-1 : ℝ) 1) (L : ℕ) (hL : 1 ≤ L) :
    |v - (∑ l : Fin L, (if -1 + 2 * (l : ℝ) / L < v then (1 : ℝ) else -1)) / L| ≤ 2 / L := by
  classical
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  set u : ℝ := L * (v + 1) / 2 with hu
  have hu0 : 0 ≤ u := by have := hv.1; rw [hu]; nlinarith
  have huL : u ≤ L := by have := hv.2; rw [hu]; nlinarith
  set c : ℕ := ⌈u⌉₊ with hc
  have hcL : c ≤ L := Nat.ceil_le.2 huL
  have hc1 : u ≤ c := Nat.le_ceil u
  have hc2 : (c : ℝ) < u + 1 := Nat.ceil_lt_add_one hu0
  have hiff : ∀ l : ℕ, (-1 + 2 * (l : ℝ) / L < v ↔ l < c) := by
    intro l
    rw [hc, Nat.lt_ceil, hu]
    constructor
    · intro h
      have : 2 * (l : ℝ) / L < v + 1 := by linarith
      rw [div_lt_iff₀ hLpos] at this
      linarith
    · intro h
      have : 2 * (l : ℝ) < (v + 1) * L := by linarith
      have : 2 * (l : ℝ) / L < v + 1 := by rw [div_lt_iff₀ hLpos]; linarith
      linarith
  have hsum : (∑ l : Fin L, (if -1 + 2 * (l : ℝ) / L < v then (1 : ℝ) else -1))
      = 2 * c - L := by
    rw [Fin.sum_univ_eq_sum_range (fun l : ℕ => if -1 + 2 * (l : ℝ) / L < v then (1 : ℝ) else -1)]
    have h1 : ∀ l ∈ Finset.range L, (if -1 + 2 * (l : ℝ) / L < v then (1 : ℝ) else -1)
        = 2 * (if l < c then (1 : ℝ) else 0) - 1 := by
      intro l _
      by_cases h : l < c
      · rw [if_pos ((hiff l).2 h), if_pos h]; ring
      · rw [if_neg (fun h' => h ((hiff l).1 h')), if_neg h]; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, mul_one]
    have : (Finset.range L).filter (fun l => l < c) = Finset.range c := by
      ext l; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this, Finset.card_range]
  rw [hsum]
  have hv' : v = 2 * u / L - 1 := by rw [hu]; field_simp; ring
  rw [hv', abs_le]
  constructor
  · rw [show 2 * u / L - 1 - (2 * c - L) / L = 2 * (u - c) / L by field_simp; ring]
    rw [show -(2 / (L : ℝ)) = (-2) / L by ring]
    rw [div_le_div_iff_of_pos_right hLpos]
    linarith
  · rw [show 2 * u / L - 1 - (2 * c - L) / L = 2 * (u - c) / L by field_simp; ring]
    rw [div_le_div_iff_of_pos_right hLpos]
    linarith

noncomputable def b28nu {M : ℕ} (p : Fin M → ℝ) : MeasureTheory.Measure (Fin M) :=
  ∑ i, ENNReal.ofReal (p i) • MeasureTheory.Measure.dirac i

open MeasureTheory in
lemma b28nu_integral {M : ℕ} (p : Fin M → ℝ) (hp0 : ∀ i, 0 ≤ p i) (f : Fin M → ℝ) :
    ∫ i, f i ∂(b28nu p) = ∑ i, p i * f i := by
  simp only [b28nu]
  rw [integral_finset_sum_measure (fun i _ => (Integrable.of_finite).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hp0 i), smul_eq_mul]

open MeasureTheory in
lemma b28nu_prob {M : ℕ} (p : Fin M → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    IsProbabilityMeasure (b28nu p) := by
  constructor
  simp only [b28nu, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp0 i), hp1, ENNReal.ofReal_one]

open MeasureTheory ProbabilityTheory in
lemma b28_tail {M : ℕ} (p : Fin M → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (v : Fin M → ℝ) (hv : ∀ i, |v i| ≤ 1) (N : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    (Measure.pi fun _ : Fin N => b28nu p).real
        {ω | (N : ℝ) * τ ≤ ∑ r, (v (ω r) - ∑ i, p i * v i)} ≤ Real.exp (-(N * τ ^ 2 / 2)) := by
  haveI := b28nu_prob p hp0 hp1
  set μ := Measure.pi fun _ : Fin N => b28nu p with hμ
  set c : ℝ := ∑ i, p i * v i with hc
  have hind : iIndepFun (fun (r : Fin N) (ω : Fin N → Fin M) => (fun i => v i - c) (ω r)) μ :=
    iIndepFun_pi (μ := fun _ : Fin N => b28nu p) (X := fun _ : Fin N => fun i => v i - c)
      (fun _ => (Measurable.of_discrete).aemeasurable)
  have hmean : ∀ r : Fin N, μ[fun ω : Fin N → Fin M => v (ω r)] = c := by
    intro r
    have hmp : MeasurePreserving (Function.eval r) μ (b28nu p) :=
      measurePreserving_eval (fun _ : Fin N => b28nu p) r
    rw [show (fun ω : Fin N → Fin M => v (ω r)) = fun ω => v (Function.eval r ω) from rfl,
      ← integral_map hmp.measurable.aemeasurable
      (Measurable.of_discrete (f := v)).aestronglyMeasurable, hmp.map_eq,
      b28nu_integral p hp0]
  have hsub : ∀ r ∈ (Finset.univ : Finset (Fin N)),
      HasSubgaussianMGF (fun ω : Fin N → Fin M => (fun i => v i - c) (ω r)) 1 μ := by
    intro r _
    have hb : ∀ᵐ ω ∂μ, (fun ω : Fin N → Fin M => v (ω r)) ω ∈ Set.Icc (-1 : ℝ) 1 :=
      Filter.Eventually.of_forall fun ω => abs_le.1 (hv (ω r))
    have h := hasSubgaussianMGF_of_mem_Icc (X := fun ω : Fin N → Fin M => v (ω r))
      ((Measurable.of_discrete (f := v)).comp (measurable_pi_apply r)).aemeasurable hb
    rw [hmean r] at h
    have hc1 : ((‖(1 : ℝ) - -1‖₊ / 2) ^ 2) = 1 := by
      have : ‖(1 : ℝ) - -1‖₊ = 2 := by
        rw [show (1 : ℝ) - -1 = 2 by norm_num]
        ext; simp
      rw [this]; norm_num
    rw [hc1] at h
    exact h
  have hNτ : (0 : ℝ) ≤ N * τ := by positivity
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub hNτ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    NNReal.coe_natCast] at h
  refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
  · rfl
  · by_cases hN0 : (N : ℝ) = 0
    · simp [hN0]
    · congr 1
      field_simp

open MeasureTheory in
lemma b28_maurey {M : ℕ} (p : Fin M → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) {K : ℕ}
    (v : Fin M → Fin K → ℝ) (hv : ∀ i k, |v i k| ≤ 1) (N : ℕ) (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 < τ)
    (hNτ : 2 * K * Real.exp (-(N * τ ^ 2 / 2)) < 1) :
    ∃ s : Fin N → Fin M, ∀ k, |(∑ r, v (s r) k) / N - ∑ i, p i * v i k| < τ := by
  classical
  haveI := b28nu_prob p hp0 hp1
  set μ := Measure.pi fun _ : Fin N => b28nu p with hμ
  set B : Fin K → Set (Fin N → Fin M) := fun k =>
    {ω | (N : ℝ) * τ ≤ ∑ r, (v (ω r) k - ∑ i, p i * v i k)} ∪
    {ω | (N : ℝ) * τ ≤ ∑ r, ((fun i => -v i k) (ω r) - ∑ i, p i * (fun i => -v i k) i)} with hB
  have hBk : ∀ k, μ.real (B k) ≤ 2 * Real.exp (-(N * τ ^ 2 / 2)) := by
    intro k
    refine (measureReal_union_le _ _).trans ?_
    have h1 := b28_tail p hp0 hp1 (fun i => v i k) (fun i => hv i k) N hτ
    have h2 := b28_tail p hp0 hp1 (fun i => -v i k) (fun i => by rw [abs_neg]; exact hv i k) N hτ
    linarith
  have hU : μ.real (⋃ k, B k) < 1 := by
    refine lt_of_le_of_lt (measureReal_iUnion_fintype_le _) ?_
    calc ∑ k, μ.real (B k) ≤ ∑ _k : Fin K, 2 * Real.exp (-(N * τ ^ 2 / 2)) :=
          Finset.sum_le_sum fun k _ => hBk k
      _ = 2 * K * Real.exp (-(N * τ ^ 2 / 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ < 1 := hNτ
  have hex : ∃ ω, ω ∉ ⋃ k, B k := by
    by_contra hcon
    push_neg at hcon
    have : (⋃ k, B k) = Set.univ := Set.eq_univ_of_forall hcon
    rw [this] at hU
    simp at hU
  obtain ⟨ω, hω⟩ := hex
  refine ⟨ω, fun k => ?_⟩
  have hωk : ω ∉ B k := fun h => hω (Set.mem_iUnion.2 ⟨k, h⟩)
  simp only [hB, Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hωk
  obtain ⟨h1, h2⟩ := hωk
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h1 h2
  have h2' : (∑ r, -v (ω r) k) = -∑ r, v (ω r) k := Finset.sum_neg_distrib (fun r => v (ω r) k)
  have h3 : (∑ i, p i * -v i k) = -∑ i, p i * v i k := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2', h3] at h2
  rw [abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hNpos]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hNpos]; nlinarith

lemma b28_pm_sq (β : Bool) : |BartlettNN.Margin.pm β| = 1 := by
  cases β <;> simp [BartlettNN.Margin.pm]

lemma b28_rat {n K : ℕ} (xs : Fin K → Fin n → ℝ) (U : Set ℝ)
    (hU : ∀ s t : ℝ, s ≤ t → s ∈ U → t ∈ U) (a : Fin n → ℝ) (b : ℝ) :
    ∃ q : (Fin n → ℚ) × ℚ, ∀ k,
      ((∑ i, a i * xs k i + b) ∈ U ↔ (q.2 : ℝ) < ∑ i, (q.1 i : ℝ) * xs k i) := by
  classical
  set V : Fin K → ℝ := fun k => ∑ i, a i * xs k i + b with hV
  by_cases hall : ∀ k, V k ∈ U
  · refine ⟨(0, -1), fun k => ?_⟩
    simp only [Pi.zero_apply, Rat.cast_zero, zero_mul, Finset.sum_const_zero, Rat.cast_neg,
      Rat.cast_one]
    exact ⟨fun _ => by norm_num, fun _ => hall k⟩
  by_cases hnone : ∀ k, V k ∉ U
  · refine ⟨(0, 0), fun k => ?_⟩
    simp only [Pi.zero_apply, Rat.cast_zero, zero_mul, Finset.sum_const_zero, lt_self_iff_false,
      iff_false]
    exact hnone k
  push_neg at hall hnone
  set O := Finset.univ.filter fun k => V k ∉ U with hO
  set I := Finset.univ.filter fun k => V k ∈ U with hI
  have hOne : O.Nonempty := by
    obtain ⟨k, hk⟩ := hall; exact ⟨k, by simp [hO, hk]⟩
  have hIne : I.Nonempty := by
    obtain ⟨k, hk⟩ := hnone; exact ⟨k, by simp [hI, hk]⟩
  obtain ⟨k1, hk1O, hk1⟩ := Finset.exists_max_image O V hOne
  obtain ⟨k0, hk0I, hk0⟩ := Finset.exists_min_image I V hIne
  have hk1U : V k1 ∉ U := (Finset.mem_filter.1 hk1O).2
  have hk0U : V k0 ∈ U := (Finset.mem_filter.1 hk0I).2
  have hlohi : V k1 < V k0 := by
    by_contra h
    push_neg at h
    exact hk1U (hU _ _ h hk0U)
  set g : ℝ := V k0 - V k1 with hg
  have hgpos : 0 < g := by rw [hg]; linarith
  set R : ℝ := 1 + ∑ k, ∑ i, |xs k i| with hR
  have hRk : ∀ k, ∑ i, |xs k i| ≤ R := by
    intro k
    have : ∑ i, |xs k i| ≤ ∑ k', ∑ i, |xs k' i| :=
      Finset.single_le_sum (f := fun k' => ∑ i, |xs k' i|)
        (fun k' _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ k)
    rw [hR]; linarith
  have hRpos : 0 < R := by
    have : 0 ≤ ∑ k, ∑ i, |xs k i| :=
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => abs_nonneg _
    rw [hR]; linarith
  set η : ℝ := g / (4 * R) with hη
  have hηpos : 0 < η := by positivity
  have hqa : ∀ i, ∃ r : ℚ, |(r : ℝ) - a i| < η := by
    intro i
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show a i - η < a i + η by linarith)
    exact ⟨r, abs_lt.2 ⟨by linarith, by linarith⟩⟩
  choose a' ha' using hqa
  obtain ⟨c', hc1, hc2⟩ := exists_rat_btwn
    (show (V k1 + V k0) / 2 - b - g / 4 < (V k1 + V k0) / 2 - b + g / 4 by linarith)
  have hdiff : ∀ k, |∑ i, (a' i : ℝ) * xs k i - ∑ i, a i * xs k i| ≤ g / 4 := by
    intro k
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |(a' i : ℝ) * xs k i - a i * xs k i| ≤ ∑ i, η * |xs k i| := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← sub_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right (ha' i).le (abs_nonneg _)
      _ = η * ∑ i, |xs k i| := by rw [Finset.mul_sum]
      _ ≤ η * R := mul_le_mul_of_nonneg_left (hRk k) hηpos.le
      _ = g / 4 := by rw [hη]; field_simp
  refine ⟨(a', c'), fun k => ?_⟩
  simp only
  have hd := abs_le.1 (hdiff k)
  constructor
  · intro hk
    have hkI : k ∈ I := Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩
    have := hk0 k hkI
    have hVk : V k = ∑ i, a i * xs k i + b := rfl
    rw [hg] at hd hc2
    linarith
  · intro hk
    by_contra hkU
    have hkO : k ∈ O := Finset.mem_filter.2 ⟨Finset.mem_univ _, hkU⟩
    have := hk1 k hkO
    have hVk : V k = ∑ i, a i * xs k i + b := rfl
    rw [hg] at hd hc1
    linarith

lemma b28b_abs {n : ℕ} (q : (Fin n → ℚ) × ℚ) (x : Fin n → ℝ) : |b28b q x| = 1 := by
  unfold b28b; split_ifs <;> simp

lemma b28_approx {n : ℕ} (σ : ℝ → ℝ) (hσ : Monotone σ) (hσb : ∀ t, σ t ∈ Set.Icc (-1 : ℝ) 1)
    {A γ : ℝ} (hA : 0 < A) (hγ : 0 < γ) {h : (Fin n → ℝ) → ℝ}
    (hh : h ∈ BartlettNN.FatNet.combos (BartlettNN.Sigmoid.sigmoidUnits σ n) A)
    {K N : ℕ} (hN : 1 ≤ N) (hNK : 2 * K * Real.exp (-(N * (γ / (4 * A)) ^ 2 / 2)) < 1)
    (xs : Fin K → Fin n → ℝ) :
    ∃ θ : Fin N → Bool × ((Fin n → ℚ) × ℚ), ∀ k, |b28g A θ (xs k) - h (xs k)| < γ / 2 := by
  classical
  obtain ⟨J, w, f, hf, hw, rfl⟩ := hh
  choose a b hab using hf
  set W : ℝ := ∑ j, |w j| with hW
  set L : ℕ := ⌈16 * A / γ⌉₊ + 1 with hL
  have hL1 : 1 ≤ L := by omega
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hLbig : 16 * A / γ ≤ L := by
    rw [hL]; push_cast; linarith [Nat.le_ceil (16 * A / γ)]
  have h2AL : 2 * A / L ≤ γ / 8 := by
    rw [div_le_iff₀ hLpos]
    have := (div_le_iff₀ hγ).1 hLbig
    nlinarith
  -- thresholds and their rational halfspaces
  have hUp : ∀ l : Fin L, ∀ s t : ℝ, s ≤ t →
      s ∈ {t' : ℝ | -1 + 2 * (l : ℝ) / L < σ t'} → t ∈ {t' : ℝ | -1 + 2 * (l : ℝ) / L < σ t'} :=
    fun l s t hst hs => lt_of_lt_of_le hs (hσ hst)
  have hq := fun (j : Fin J) (l : Fin L) =>
    b28_rat xs {t' : ℝ | -1 + 2 * (l : ℝ) / L < σ t'} (hUp l) (a j) (b j)
  choose q hq using hq
  set ι := (Fin J × Fin L) ⊕ Bool with hι
  let tag : ι → Bool × ((Fin n → ℚ) × ℚ) := fun i => match i with
    | Sum.inl jl => (decide (0 ≤ w jl.1), q jl.1 jl.2)
    | Sum.inr β => (β, (0, -1))
  let p' : ι → ℝ := fun i => match i with
    | Sum.inl jl => |w jl.1| / (L * A)
    | Sum.inr _ => (A - W) / (2 * A)
  let vf : ι → Fin K → ℝ := fun i k => BartlettNN.Margin.pm (tag i).1 * b28b (tag i).2 (xs k)
  have hvf : ∀ i k, |vf i k| ≤ 1 := by
    intro i k
    simp only [vf, abs_mul, b28_pm_sq, b28b_abs, mul_one, le_refl]
  have hp0 : ∀ i, 0 ≤ p' i := by
    intro i
    rcases i with jl | β
    · exact div_nonneg (abs_nonneg _) (by positivity)
    · exact div_nonneg (by linarith) (by positivity)
  have hp1 : ∑ i, p' i = 1 := by
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [p', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hx : ∀ x : Fin J, (L : ℝ) * (|w x| / (L * A)) = |w x| / A := by
      intro x; field_simp
    rw [Finset.sum_congr rfl (fun x _ => hx x), ← Finset.sum_div, ← hW]
    field_simp
    ring
  let e := Fintype.equivFin ι
  obtain ⟨s, hs⟩ := b28_maurey (fun i => p' (e.symm i)) (fun i => hp0 _)
    (by rw [Equiv.sum_comp e.symm p']; exact hp1) (fun i k => vf (e.symm i) k)
    (fun i k => hvf _ _) N hN (τ := γ / (4 * A)) (by positivity) hNK
  refine ⟨fun r => tag (e.symm (s r)), fun k => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  -- the proxy value
  have hg : b28g A (fun r => tag (e.symm (s r))) (xs k) = A * ((∑ r, vf (e.symm (s r)) k) / N) := by
    simp only [b28g, vf]
    field_simp
  -- the mean
  have hmean : ∑ i, p' (e.symm i) * vf (e.symm i) k
      = (∑ j, w j * ((∑ l : Fin L, (if -1 + 2 * (l : ℝ) / L < σ (∑ i, a j i * xs k i + b j)
          then (1 : ℝ) else -1)) / L)) / A := by
    rw [Equiv.sum_comp e.symm (fun i => p' i * vf i k)]
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool]
    have hbeta : ∀ j (l : Fin L), b28b (q j l) (xs k)
        = if -1 + 2 * (l : ℝ) / L < σ (∑ i, a j i * xs k i + b j) then (1 : ℝ) else -1 := by
      intro j l
      unfold b28b
      have := hq j l k
      simp only [Set.mem_setOf_eq] at this
      by_cases hc : -1 + 2 * (l : ℝ) / L < σ (∑ i, a j i * xs k i + b j)
      · rw [if_pos hc, if_pos (this.1 hc)]
      · rw [if_neg hc, if_neg (fun h' => hc (this.2 h'))]
    have hpmw : ∀ j, |w j| * BartlettNN.Margin.pm (decide (0 ≤ w j)) = w j := by
      intro j
      by_cases hj : 0 ≤ w j
      · simp [BartlettNN.Margin.pm, hj, abs_of_nonneg hj]
      · push_neg at hj
        simp [BartlettNN.Margin.pm, not_le.2 hj, abs_of_neg hj]
    have hb0 : b28b ((0 : Fin n → ℚ), (-1 : ℚ)) (xs k) = 1 := by
      unfold b28b; simp
    have hinr : p' (Sum.inr true) * vf (Sum.inr true) k
        + p' (Sum.inr false) * vf (Sum.inr false) k = 0 := by
      simp only [p', vf, tag, hb0, BartlettNN.Margin.pm]
      simp
    rw [hinr, add_zero, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [p', vf, tag, hbeta]
    have hterm : ∀ l : Fin L, |w j| / (L * A) * (BartlettNN.Margin.pm (decide (0 ≤ w j)) *
        (if -1 + 2 * (l : ℝ) / L < σ (∑ i, a j i * xs k i + b j) then (1 : ℝ) else -1))
        = (|w j| * BartlettNN.Margin.pm (decide (0 ≤ w j))) / (L * A) *
          (if -1 + 2 * (l : ℝ) / L < σ (∑ i, a j i * xs k i + b j) then (1 : ℝ) else -1) := by
      intro l; ring
    rw [Finset.sum_congr rfl (fun l _ => hterm l), ← Finset.mul_sum, hpmw j]
    field_simp
  -- h at the point
  have hhk : (fun x => ∑ j, w j * f j x) (xs k) = ∑ j, w j * σ (∑ i, a j i * xs k i + b j) := by
    simp only [hab]
  have hlay : |(∑ j, w j * ((∑ l : Fin L, (if -1 + 2 * (l : ℝ) / L < σ (∑ i, a j i * xs k i + b j)
          then (1 : ℝ) else -1)) / L)) - ∑ j, w j * σ (∑ i, a j i * xs k i + b j)| ≤ γ / 8 := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ j, |w j| * (2 / L) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← mul_sub, abs_mul, abs_sub_comm]
          exact mul_le_mul_of_nonneg_left (b28_layer _ (hσb _) L hL1) (abs_nonneg _)
      _ = W * (2 / L) := by rw [hW, Finset.sum_mul]
      _ ≤ A * (2 / L) := mul_le_mul_of_nonneg_right hw (by positivity)
      _ = 2 * A / L := by ring
      _ ≤ γ / 8 := h2AL
  have hsk := hs k
  rw [hmean] at hsk
  rw [hhk, hg]
  set avg := (∑ r, vf (e.symm (s r)) k) / N
  set mean := (∑ j, w j * ((∑ l : Fin L, (if -1 + 2 * (l : ℝ) / L < σ (∑ i, a j i * xs k i + b j)
          then (1 : ℝ) else -1)) / L))
  have h1 : |A * avg - mean| < γ / 4 := by
    have : A * avg - mean = A * (avg - mean / A) := by field_simp
    rw [this, abs_mul, abs_of_pos hA]
    calc A * |avg - mean / A| < A * (γ / (4 * A)) := mul_lt_mul_of_pos_left hsk hA
      _ = γ / 4 := by field_simp
  have h2 := abs_sub_le (A * avg) mean (∑ j, w j * σ (∑ i, a j i * xs k i + b j))
  linarith

lemma b28_log_le3 (m : ℕ) (hm : 2 ≤ m) :
    Real.log (4 * m) ≤ 3 * Real.log m ∧ Real.log (2 * m + 1) ≤ 3 * Real.log m := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have h3 : 3 * Real.log m = Real.log ((m : ℝ) ^ 3) := by rw [Real.log_pow]; norm_num
  rw [h3]
  have h4 : (4 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have h5 := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ m by linarith)
  have h6 : (m : ℝ) ^ 3 = m * m ^ 2 := by ring
  constructor
  · exact Real.log_le_log (by positivity) (by linarith)
  · exact Real.log_le_log (by positivity) (by linarith)

lemma b28_arith {n m N : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) {G ℓ Q : ℝ} (hG : 1 ≤ G)
    (hℓ : Real.log 2 ≤ ℓ) (hN : (N : ℝ) ≤ 32 * G ^ 2 * Real.log (4 * m) + 1)
    (hQ : 10000 * (n * G ^ 2 * Real.log (32 * G) * Real.log m ^ 2 + ℓ) / 32 ≤ Q) :
    4 * (2 ^ N * ((((m + m : ℕ) : ℝ) + 1) ^ (n + 1)) ^ N) * Real.exp (-Q) ≤ Real.exp (-ℓ) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set Lm := Real.log m with hLm
  have hl2 : (0.6931 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hLm2 : Real.log 2 ≤ Lm := Real.log_le_log (by norm_num) hm'
  obtain ⟨h4m, h2m1⟩ := b28_log_le3 m hm
  have hB : (((m + m : ℕ) : ℝ) + 1) = 2 * m + 1 := by push_cast; ring
  rw [hB]
  have hlog32 : (3.46 : ℝ) ≤ Real.log (32 * G) := by
    have h1 : Real.log 32 = 5 * Real.log 2 := by
      rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
    have h2 : Real.log 32 ≤ Real.log (32 * G) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  set X : ℝ := Real.log 4 + (N * Real.log 2 + N * ((n + 1) * Real.log (2 * m + 1))) with hX
  have hprod : 4 * (2 ^ N * (((2 : ℝ) * m + 1) ^ (n + 1)) ^ N) = Real.exp X := by
    have hpos : (0 : ℝ) < 2 * m + 1 := by positivity
    rw [hX, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]
    rw [show (N : ℝ) * Real.log 2 = Real.log (2 ^ N) by rw [Real.log_pow]]
    rw [show (N : ℝ) * ((n + 1) * Real.log (2 * m + 1)) = Real.log ((((2 : ℝ) * m + 1) ^ (n + 1)) ^ N) by
      rw [Real.log_pow, Real.log_pow]; push_cast; ring]
    rw [Real.exp_log (by positivity), Real.exp_log (by positivity)]
  rw [hprod, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hG2 : 1 ≤ G ^ 2 := by nlinarith
  have hN' : (N : ℝ) ≤ 98 * G ^ 2 * Lm := by
    have h1 : 32 * G ^ 2 * Real.log (4 * m) ≤ 32 * G ^ 2 * (3 * Lm) :=
      mul_le_mul_of_nonneg_left h4m (by positivity)
    have h2 : 1 ≤ 2 * G ^ 2 * Lm := by nlinarith
    linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hLm0 : 0 ≤ Lm := by linarith
  have hb1 : (N : ℝ) * Real.log 2 ≤ N * Lm := mul_le_mul_of_nonneg_left hLm2 hN0
  have hb2 : (N : ℝ) * ((n + 1) * Real.log (2 * m + 1)) ≤ N * ((n + 1) * (3 * Lm)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2m1 (by positivity)) hN0
  have hb3 : (N : ℝ) * Lm + N * ((n + 1) * (3 * Lm)) ≤ 7 * n * (N * Lm) := by
    have : 0 ≤ (N : ℝ) * Lm := mul_nonneg hN0 hLm0
    nlinarith
  have hb4 : 7 * n * (N * Lm) ≤ 7 * n * (98 * G ^ 2 * Lm * Lm) := by
    have : (N : ℝ) * Lm ≤ 98 * G ^ 2 * Lm * Lm := mul_le_mul_of_nonneg_right hN' hLm0
    have h7 : (0 : ℝ) ≤ 7 * n := by positivity
    exact mul_le_mul_of_nonneg_left this h7
  have hP0 : 0 ≤ (n : ℝ) * G ^ 2 * Lm ^ 2 := by positivity
  have hb5 : 7 * n * (98 * G ^ 2 * Lm * Lm) ≤ 199 * (n * G ^ 2 * Real.log (32 * G) * Lm ^ 2) := by
    have : 7 * n * (98 * G ^ 2 * Lm * Lm) = 686 * (n * G ^ 2 * Lm ^ 2) := by ring
    rw [this]
    have : 199 * (n * G ^ 2 * Real.log (32 * G) * Lm ^ 2)
        = (199 * Real.log (32 * G)) * (n * G ^ 2 * Lm ^ 2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) hP0
  have h4 : Real.log 4 ≤ 2 * ℓ := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hT0 : 0 ≤ (n : ℝ) * G ^ 2 * Real.log (32 * G) * Lm ^ 2 := by
    have : 0 ≤ Real.log (32 * G) := by linarith
    positivity
  rw [hX]
  nlinarith

lemma b28_combos_meas {n : ℕ} (σ : ℝ → ℝ) (hσ : Monotone σ) {A : ℝ} {h : (Fin n → ℝ) → ℝ}
    (hh : h ∈ BartlettNN.FatNet.combos (BartlettNN.Sigmoid.sigmoidUnits σ n) A) : Measurable h := by
  obtain ⟨J, w, f, hf, _, rfl⟩ := hh
  refine Finset.measurable_sum _ fun j _ => ?_
  obtain ⟨a, b, hab⟩ := hf j
  have hm : Measurable (f j) := by
    rw [hab]
    exact hσ.measurable.comp
      ((Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _).add_const _)
  exact hm.const_mul _

lemma b28_sgn_le (α : ℝ) (b : Bool) (h : BartlettNN.Margin.sgn α ≠ BartlettNN.Margin.pm b) :
    BartlettNN.Margin.pm b * α ≤ 0 := by
  unfold BartlettNN.Margin.sgn BartlettNN.Margin.pm at *
  cases b
  · by_cases h1 : α < 0
    · rw [if_pos h1] at h; simp at h
    · simp only [Bool.false_eq_true, if_false]; push_neg at h1; linarith
  · by_cases h1 : α < 0
    · simp only [if_true]; linarith
    · rw [if_neg h1] at h; simp at h

lemma b28_sgn_meas : Measurable BartlettNN.Margin.sgn := by
  unfold BartlettNN.Margin.sgn
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    measurable_const

open MeasureTheory in
lemma b28_core {n : ℕ} (σ : ℝ → ℝ) (hσ : Monotone σ) (hσb : ∀ t, σ t ∈ Set.Icc (-1 : ℝ) 1)
    (P : Measure ((Fin n → ℝ) × Bool)) [IsProbabilityMeasure P] {γ A s : ℝ} (hγ : 0 < γ)
    (hA : 0 < A) (hs : 0 < s) (m : ℕ) (hm : 2 / s ^ 2 ≤ (m : ℝ)) (N : ℕ) (hN : 1 ≤ N)
    (hNK : 2 * ((m + m : ℕ) : ℝ) * Real.exp (-(N * (γ / (4 * A)) ^ 2 / 2)) < 1)
    (hE : MeasurableSet {z : Fin m → (Fin n → ℝ) × Bool |
      ∃ h ∈ BartlettNN.FatNet.combos (BartlettNN.Sigmoid.sigmoidUnits σ n) A,
        BartlettNN.Margin.erHat γ z h + s ≤ BartlettNN.Margin.er P h}) :
    Measure.pi (fun _ : Fin m => P) {z : Fin m → (Fin n → ℝ) × Bool |
      ∃ h ∈ BartlettNN.FatNet.combos (BartlettNN.Sigmoid.sigmoidUnits σ n) A,
        BartlettNN.Margin.erHat γ z h + s ≤ BartlettNN.Margin.er P h}
      ≤ ENNReal.ofReal (4 * (2 ^ N * ((((m + m : ℕ) : ℝ) + 1) ^ (n + 1)) ^ N)
          * Real.exp (-((s / 2) ^ 2 * m / 8))) := by
  classical
  refine (b28_abstract P (b28S n N A γ) (b28S_countable n N A γ) (b28S_meas n N A γ) m hs hm _ hE
    ?_).trans ?_
  · intro x hx
    obtain ⟨h, hh, hle⟩ := hx
    have hmeas := b28_combos_meas σ hσ hh
    refine ⟨{p | BartlettNN.Margin.sgn (h p.1) ≠ BartlettNN.Margin.pm p.2}, ?_,
      BartlettNN.Margin.erHat γ x h, hle, ?_⟩
    · exact (measurableSet_eq_fun (b28_sgn_meas.comp (hmeas.comp measurable_fst)) b28_pm_meas).compl
    · intro y
      obtain ⟨θ, hθ⟩ := b28_approx σ hσ hσb hA hγ hh hN hNK
        (Fin.append (fun i => (x i).1) (fun i => (y i).1))
      refine ⟨{p | BartlettNN.Margin.pm p.2 * b28g A θ p.1 < γ / 2}, ⟨θ, rfl⟩, ?_, ?_⟩
      · unfold VapnikChervonenkis.Shared.relFreq BartlettNN.Margin.erHat
        refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
        have hsub : (Finset.univ.filter fun i =>
            x i ∈ {p : (Fin n → ℝ) × Bool | BartlettNN.Margin.pm p.2 * b28g A θ p.1 < γ / 2}) ⊆
            Finset.univ.filter fun i => BartlettNN.Margin.pm (x i).2 * h (x i).1 < γ := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
          have h1 := hθ (Fin.castAdd m i)
          simp only [Fin.append_left] at h1
          have h2 : |BartlettNN.Margin.pm (x i).2 * h (x i).1
              - BartlettNN.Margin.pm (x i).2 * b28g A θ (x i).1| < γ / 2 := by
            rw [← mul_sub, abs_mul, b28_pm_sq, one_mul, abs_sub_comm]; exact h1
          linarith [(abs_lt.1 h2).2]
        exact_mod_cast Finset.card_le_card hsub
      · unfold VapnikChervonenkis.Shared.relFreq
        refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
        have hsub : (Finset.univ.filter fun i =>
            y i ∈ {p : (Fin n → ℝ) × Bool | BartlettNN.Margin.sgn (h p.1) ≠ BartlettNN.Margin.pm p.2}) ⊆
            Finset.univ.filter fun i =>
            y i ∈ {p : (Fin n → ℝ) × Bool | BartlettNN.Margin.pm p.2 * b28g A θ p.1 < γ / 2} := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
          have h0 := b28_sgn_le _ _ hi
          have h1 := hθ (Fin.natAdd m i)
          simp only [Fin.append_right] at h1
          have h2 : |BartlettNN.Margin.pm (y i).2 * b28g A θ (y i).1
              - BartlettNN.Margin.pm (y i).2 * h (y i).1| < γ / 2 := by
            rw [← mul_sub, abs_mul, b28_pm_sq, one_mul]; exact h1
          linarith [(abs_lt.1 h2).2]
        exact_mod_cast Finset.card_le_card hsub
  · apply ENNReal.ofReal_le_ofReal
    have hg := b28S_growth n N A γ (m + m)
    have he : 0 ≤ Real.exp (-((s / 2) ^ 2 * m / 8)) := (Real.exp_pos _).le
    gcongr

open MeasureTheory in
lemma b28_core0 (σ : ℝ → ℝ) (P : Measure ((Fin 0 → ℝ) × Bool)) [IsProbabilityMeasure P]
    {γ A s : ℝ} (hγ : 0 < γ) (hs : 0 < s) (m : ℕ) (hm : 2 / s ^ 2 ≤ (m : ℝ))
    (hE : MeasurableSet {z : Fin m → (Fin 0 → ℝ) × Bool |
      ∃ h ∈ BartlettNN.FatNet.combos (BartlettNN.Sigmoid.sigmoidUnits σ 0) A,
        BartlettNN.Margin.erHat γ z h + s ≤ BartlettNN.Margin.er P h}) :
    Measure.pi (fun _ : Fin m => P) {z : Fin m → (Fin 0 → ℝ) × Bool |
      ∃ h ∈ BartlettNN.FatNet.combos (BartlettNN.Sigmoid.sigmoidUnits σ 0) A,
        BartlettNN.Margin.erHat γ z h + s ≤ BartlettNN.Margin.er P h}
      ≤ ENNReal.ofReal (4 * 2 * Real.exp (-((s / 2) ^ 2 * m / 8))) := by
  classical
  refine (b28_abstract P b28S0 b28S0_countable b28S0_meas m hs hm _ hE ?_).trans ?_
  · intro x hx
    obtain ⟨h, hh, hle⟩ := hx
    have hconst : ∀ u v : Fin 0 → ℝ, h u = h v := fun u v => congrArg h (Subsingleton.elim u v)
    have hmeas : Measurable h := measurable_const' hconst
    set x0 : Fin 0 → ℝ := fun i => i.elim0 with hx0
    refine ⟨{p | BartlettNN.Margin.sgn (h p.1) ≠ BartlettNN.Margin.pm p.2}, ?_,
      BartlettNN.Margin.erHat γ x h, hle, ?_⟩
    · exact (measurableSet_eq_fun (b28_sgn_meas.comp (hmeas.comp measurable_fst)) b28_pm_meas).compl
    · intro y
      by_cases h0 : 0 ≤ h x0
      · refine ⟨{p | p.2 = false}, Or.inl rfl, ?_, ?_⟩
        · unfold VapnikChervonenkis.Shared.relFreq BartlettNN.Margin.erHat
          refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
          have hsub : (Finset.univ.filter fun i => x i ∈ {p : (Fin 0 → ℝ) × Bool | p.2 = false}) ⊆
              Finset.univ.filter fun i => BartlettNN.Margin.pm (x i).2 * h (x i).1 < γ := by
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
            rw [hi, hconst (x i).1 x0]
            simp only [BartlettNN.Margin.pm, Bool.false_eq_true, if_false]
            linarith
          exact Nat.cast_le.2 (by convert Finset.card_le_card hsub)
        · unfold VapnikChervonenkis.Shared.relFreq
          refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
          have hsub : (Finset.univ.filter fun i =>
              y i ∈ {p : (Fin 0 → ℝ) × Bool | BartlettNN.Margin.sgn (h p.1) ≠ BartlettNN.Margin.pm p.2}) ⊆
              Finset.univ.filter fun i => y i ∈ {p : (Fin 0 → ℝ) × Bool | p.2 = false} := by
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
            rw [hconst (y i).1 x0] at hi
            have hs1 : BartlettNN.Margin.sgn (h x0) = 1 := by
              unfold BartlettNN.Margin.sgn; rw [if_neg (not_lt.2 h0)]
            rw [hs1] at hi
            cases hb : (y i).2
            · rfl
            · rw [hb] at hi; simp [BartlettNN.Margin.pm] at hi
          exact Nat.cast_le.2 (by convert Finset.card_le_card hsub)
      · push_neg at h0
        refine ⟨{p | p.2 = true}, Or.inr rfl, ?_, ?_⟩
        · unfold VapnikChervonenkis.Shared.relFreq BartlettNN.Margin.erHat
          refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
          have hsub : (Finset.univ.filter fun i => x i ∈ {p : (Fin 0 → ℝ) × Bool | p.2 = true}) ⊆
              Finset.univ.filter fun i => BartlettNN.Margin.pm (x i).2 * h (x i).1 < γ := by
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
            rw [hi, hconst (x i).1 x0]
            simp only [BartlettNN.Margin.pm, if_true, one_mul]
            linarith
          exact Nat.cast_le.2 (by convert Finset.card_le_card hsub)
        · unfold VapnikChervonenkis.Shared.relFreq
          refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
          have hsub : (Finset.univ.filter fun i =>
              y i ∈ {p : (Fin 0 → ℝ) × Bool | BartlettNN.Margin.sgn (h p.1) ≠ BartlettNN.Margin.pm p.2}) ⊆
              Finset.univ.filter fun i => y i ∈ {p : (Fin 0 → ℝ) × Bool | p.2 = true} := by
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
            rw [hconst (y i).1 x0] at hi
            have hs1 : BartlettNN.Margin.sgn (h x0) = -1 := by
              unfold BartlettNN.Margin.sgn; rw [if_pos h0]
            rw [hs1] at hi
            cases hb : (y i).2
            · rw [hb] at hi; simp [BartlettNN.Margin.pm] at hi
            · rfl
          exact Nat.cast_le.2 (by convert Finset.card_le_card hsub)
  · apply ENNReal.ofReal_le_ofReal
    have hg := b28S0_growth (m + m)
    have he : 0 ≤ Real.exp (-((s / 2) ^ 2 * m / 8)) := (Real.exp_pos _).le
    gcongr

open MeasureTheory BartlettNN.Sigmoid in
theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) (σ : ℝ → ℝ)
        (P : Measure ((Fin n → ℝ) × Bool)) (_ : IsProbabilityMeasure P)
        (γ δ A : ℝ) (m : ℕ),
        Monotone σ → (∀ t, σ t ∈ Set.Icc (-1 : ℝ) 1) →
        0 < γ → γ ≤ 1 → 0 < δ → δ < 1 / 2 → 1 ≤ A → 1 ≤ m →
        MeasurableSet {z : Fin m → (Fin n → ℝ) × Bool |
          ∃ h ∈ BartlettNN.FatNet.combos (sigmoidUnits σ n) A,
            BartlettNN.Margin.erHat γ z h + Real.sqrt ((c / m) *
              ((A ^ 2 * n / γ ^ 2) * Real.log (32 * A / γ) * (Real.log m) ^ 2 +
                Real.log (1 / δ))) ≤ BartlettNN.Margin.er P h} →
        (Measure.pi fun _ : Fin m => P) {z |
          ∃ h ∈ BartlettNN.FatNet.combos (sigmoidUnits σ n) A,
            BartlettNN.Margin.erHat γ z h + Real.sqrt ((c / m) *
              ((A ^ 2 * n / γ ^ 2) * Real.log (32 * A / γ) * (Real.log m) ^ 2 +
                Real.log (1 / δ))) ≤ BartlettNN.Margin.er P h} ≤ ENNReal.ofReal δ := by
  refine ⟨10000, by norm_num, ?_⟩
  intro n σ P hP γ δ A m hσ hσb hγ hγ1 hδ hδ2 hA hm hE
  set T : ℝ := (A ^ 2 * n / γ ^ 2) * Real.log (32 * A / γ) * (Real.log m) ^ 2 with hT
  set ℓ : ℝ := Real.log (1 / δ) with hℓ
  set s : ℝ := Real.sqrt ((10000 / m) * (T + ℓ)) with hs
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hl2 : (0.6931 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hℓ2 : Real.log 2 ≤ ℓ := by
    rw [hℓ]
    refine Real.log_le_log (by norm_num) ?_
    rw [le_div_iff₀ hδ]; linarith
  have hT0 : 0 ≤ T := by
    have h1 : 0 ≤ Real.log (32 * A / γ) := by
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ hγ]; linarith
    rw [hT]; positivity
  have hpos : 0 < (10000 / m) * (T + ℓ) := by
    have : (0 : ℝ) < m := by linarith
    have : 0 < T + ℓ := by linarith
    positivity
  have hs2 : s ^ 2 = (10000 / m) * (T + ℓ) := Real.sq_sqrt hpos.le
  have hspos : 0 < s := Real.sqrt_pos.2 hpos
  by_cases hs1 : 1 < s
  · have hempty : {z : Fin m → (Fin n → ℝ) × Bool |
        ∃ h ∈ BartlettNN.FatNet.combos (sigmoidUnits σ n) A,
          BartlettNN.Margin.erHat γ z h + s ≤ BartlettNN.Margin.er P h} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro h _ hle
      have h0 : 0 ≤ BartlettNN.Margin.erHat γ z h := by
        unfold BartlettNN.Margin.erHat; positivity
      have h1 : BartlettNN.Margin.er P h ≤ 1 := by
        unfold BartlettNN.Margin.er Measure.real
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
      linarith
    rw [hempty, measure_empty]
    exact zero_le
  · push_neg at hs1
    have hs21 : s ^ 2 ≤ 1 := by nlinarith
    have hm2 : 2 ≤ m := by
      by_contra hcon
      have h1 : m = 1 := by omega
      have hT1 : T = 0 := by rw [hT, h1]; simp
      rw [hs2, hT1, h1] at hs21
      norm_num at hs21
      linarith
    have hcheb : 2 / s ^ 2 ≤ (m : ℝ) := by
      rw [hs2, div_le_iff₀ hpos]
      have : (m : ℝ) * (10000 / m * (T + ℓ)) = 10000 * (T + ℓ) := by field_simp
      rw [this]; nlinarith
    have hQ : (s / 2) ^ 2 * m / 8 = 10000 * (T + ℓ) / 32 := by
      rw [div_pow, hs2]; field_simp; ring
    have hδe : Real.exp (-ℓ) = δ := by
      rw [hℓ, one_div, Real.log_inv, neg_neg, Real.exp_log hδ]
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst hn0
      refine (b28_core0 σ P hγ hspos m hcheb hE).trans ?_
      apply ENNReal.ofReal_le_ofReal
      rw [hQ]
      have hT0' : T = 0 := by rw [hT]; simp
      rw [hT0', zero_add, ← hδe]
      have h8 : (4 : ℝ) * 2 = Real.exp (Real.log 8) := by rw [Real.exp_log (by norm_num)]; norm_num
      rw [h8, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
      linarith
    · set N : ℕ := ⌊32 * (A / γ) ^ 2 * Real.log (4 * m)⌋₊ + 1 with hNdef
      have hN1 : 1 ≤ N := by omega
      have hNgt : 32 * (A / γ) ^ 2 * Real.log (4 * m) < N := by
        rw [hNdef]; push_cast; exact Nat.lt_floor_add_one _
      have hNK : 2 * ((m + m : ℕ) : ℝ) * Real.exp (-(N * (γ / (4 * A)) ^ 2 / 2)) < 1 := by
        have hA0 : 0 < A := by linarith
        have hk : Real.log (4 * m) < N * (γ / (4 * A)) ^ 2 / 2 := by
          have : (N : ℝ) * (γ / (4 * A)) ^ 2 / 2 = N / (32 * (A / γ) ^ 2) := by
            field_simp; ring
          rw [this, lt_div_iff₀ (by positivity)]; linarith
        have h1 : Real.exp (-(N * (γ / (4 * A)) ^ 2 / 2)) < Real.exp (-Real.log (4 * m)) :=
          Real.exp_lt_exp.2 (by linarith)
        rw [Real.exp_neg (Real.log _), Real.exp_log (by positivity)] at h1
        have h2m : 2 * ((m + m : ℕ) : ℝ) = 4 * m := by push_cast; ring
        rw [h2m]
        calc 4 * (m : ℝ) * Real.exp (-(N * (γ / (4 * A)) ^ 2 / 2)) < 4 * (m : ℝ) * (4 * (m : ℝ))⁻¹ :=
              mul_lt_mul_of_pos_left h1 (by positivity)
          _ = 1 := by field_simp
      refine (b28_core σ hσ hσb P hγ (by linarith) hspos m hcheb N hN1 hNK hE).trans ?_
      apply ENNReal.ofReal_le_ofReal
      rw [← hδe]
      have hG : 1 ≤ A / γ := by rw [le_div_iff₀ hγ]; linarith
      have hNle : (N : ℝ) ≤ 32 * (A / γ) ^ 2 * Real.log (4 * m) + 1 := by
        rw [hNdef]; push_cast
        have := Nat.floor_le (show 0 ≤ 32 * (A / γ) ^ 2 * Real.log (4 * m) by
          have : 0 ≤ Real.log (4 * m) := Real.log_nonneg (by linarith)
          positivity)
        linarith
      refine b28_arith hn hm2 hG hℓ2 hNle ?_
      rw [hQ]
      have hTe : (n : ℝ) * (A / γ) ^ 2 * Real.log (32 * (A / γ)) * Real.log m ^ 2 = T := by
        rw [hT, show 32 * (A / γ) = 32 * A / γ by ring]
        field_simp
      rw [hTe]

end
