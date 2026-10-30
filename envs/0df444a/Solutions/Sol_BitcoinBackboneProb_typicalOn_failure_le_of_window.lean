-- Prove2me | solution 1 for BitcoinBackboneProb.typicalOn_failure_le_of_window
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T00:35:40.67746+00:00
-- url     : https://prove2.me/submissions/530fa351-e763-4859-a35c-e5a35f41fab5

import Definitions.Def_BitcoinBackboneProb
import Theorems.Thm_BitcoinBackboneProb_integral_advCount
import Theorems.Thm_BitcoinBackboneProb_integral_roundY

open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

private theorem integral_pi_prod_ber (m : ℕ) (p : unitInterval) (g : Fin m → Bool → ℝ) :
    ∫ f : Fin m → Bool, ∏ i, g i (f i) ∂(Measure.pi fun _ => ber p) =
      ∏ i, ((p : ℝ) * g i true + (1 - (p : ℝ)) * g i false) := by
  rw [integral_fintype_prod_eq_prod]
  congr 1; ext i
  simp [ber, integral_bernoulliMeasure]

private theorem integral_pi_eval_ber (m : ℕ) (p : unitInterval) (j : Fin m) (g : Bool → ℝ) :
    ∫ f : Fin m → Bool, g (f j) ∂(Measure.pi fun _ => ber p) =
      (p : ℝ) * g true + (1 - (p : ℝ)) * g false := by
  have h := integral_pi_prod_ber m p (fun i b => if i = j then g b else 1)
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true] at h
  rw [h]
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

private theorem honestCount_eq_zero_iff {n t : ℕ} (ρ : Round n t) :
    honestCount ρ = 0 ↔ ∀ i, ρ.1 i = false := by
  simp [honestCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

private theorem honestCount_eq_one_iff {n t : ℕ} (ρ : Round n t) (i : Fin n) :
    (∀ j, ρ.1 j = decide (j = i)) → honestCount ρ = 1 := by
  intro h
  unfold honestCount
  rw [Finset.card_eq_one]
  exact ⟨i, by ext j; simp [h j]⟩

private theorem roundY_real_eq {n t : ℕ} (ρ : Round n t) :
    (roundY ρ : ℝ) = ∑ i, ∏ j, (if ρ.1 j = decide (j = i) then (1 : ℝ) else 0) := by
  simp only [Finset.prod_boole, Finset.mem_univ, true_implies]
  rw [Finset.sum_boole]
  unfold roundY
  by_cases h : honestCount ρ = 1
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h
    have hf : ∀ j, ρ.1 j = decide (j = a) := by
      intro j
      have := congrArg (fun s => j ∈ s) ha
      simp at this
      cases hj : ρ.1 j <;> simp_all
    have : (Finset.univ.filter fun i => ∀ j, ρ.1 j = decide (j = i)) = {a} := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hi; have := (hi a).symm.trans (hf a); simpa [eq_comm] using this
      · rintro rfl; exact hf
    simp [h, this]
  · have : (Finset.univ.filter fun i => ∀ j, ρ.1 j = decide (j = i)) = ∅ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hi; exact h (honestCount_eq_one_iff ρ i hi)
    simp [h, this]

private theorem roundX_real_eq {n t : ℕ} (ρ : Round n t) :
    (roundX ρ : ℝ) = 1 - ∏ i, (if ρ.1 i = false then (1 : ℝ) else 0) := by
  rw [Finset.prod_boole]
  unfold roundX
  have := honestCount_eq_zero_iff ρ
  by_cases h : honestCount ρ = 0
  · simp [h, this.1 h]
  · have h' : ¬ ∀ i, ρ.1 i = false := fun h'' => h (this.2 h'')
    simp [Nat.pos_of_ne_zero h, h']

private theorem advCount_real_eq {n t : ℕ} (ρ : Round n t) :
    (advCount ρ : ℝ) = ∑ j, (if ρ.2 j = true then (1 : ℝ) else 0) := by
  simp [advCount, Finset.sum_boole]

private theorem integral_round_fst (n t : ℕ) (p : unitInterval) (g : (Fin n → Bool) → ℝ) :
    ∫ ρ, g ρ.1 ∂(roundMeasure n t p) = ∫ f, g f ∂(Measure.pi fun _ => ber p) := by
  unfold roundMeasure
  rw [integral_fun_fst]; simp

private theorem integral_round_snd (n t : ℕ) (p : unitInterval) (g : (Fin t → Bool) → ℝ) :
    ∫ ρ, g ρ.2 ∂(roundMeasure n t p) = ∫ f, g f ∂(Measure.pi fun _ => ber p) := by
  unfold roundMeasure
  rw [integral_fun_snd]; simp

private theorem integral_trace_eval (n t : ℕ) (p : unitInterval) (r : ℕ) (g : Round n t → ℝ) :
    ∫ ω, g (ω r) ∂(P n t p) = ∫ ρ, g ρ ∂(roundMeasure n t p) := by
  unfold P
  conv_rhs => rw [← Measure.infinitePi_map_eval (fun _ : ℕ => roundMeasure n t p) r]
  rw [integral_map (measurable_pi_apply r).aemeasurable (Measurable.of_discrete.aestronglyMeasurable)]

private theorem advCount_le {n t : ℕ} (ρ : Round n t) : advCount ρ ≤ t := by
  unfold advCount
  exact (Finset.card_filter_le _ _).trans (by simp)

private theorem roundY_le_one {n t : ℕ} (ρ : Round n t) : roundY ρ ≤ 1 := by
  unfold roundY; split_ifs <;> simp

private theorem hoeffding_core (n t : ℕ) (p : unitInterval) (S T : Finset ℕ) (hTS : T ⊆ S)
    (j : ℕ) (ε : ℝ)
    (hεdef : ε = j + T.card * (n * p * (1 - (p : ℝ)) ^ (n - 1)) - S.card * (t * p))
    (hε : 0 ≤ ε) :
    (P n t p).real {ω | ∑ i ∈ T, Y ω i + j ≤ ∑ i ∈ S, Z ω i} ≤
      Real.exp (-2 * ε ^ 2 / (S.card * ((t : ℝ) + 1) ^ 2)) := by
  classical
  set y : ℝ := n * p * (1 - (p : ℝ)) ^ (n - 1) with hy
  set z : ℝ := t * p with hz
  let V : ℕ → Round n t → ℝ := fun i ρ => (advCount ρ : ℝ) - if i ∈ T then (roundY ρ : ℝ) else 0
  have hVint : ∀ i, ∫ ω, V i (ω i) ∂(P n t p) = z - if i ∈ T then y else 0 := by
    intro i
    rw [integral_trace_eval n t p i (V i)]
    simp only [V]
    rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_advCount]
    split_ifs
    · rw [integral_roundY]
    · simp [hz]
  let Xf : ℕ → Trace n t → ℝ := fun i ω => V i (ω i) - (z - if i ∈ T then y else 0)
  have hind : iIndepFun Xf (P n t p) :=
    iIndepFun_infinitePi (X := fun i ρ => V i ρ - (z - if i ∈ T then y else 0))
      (fun _ => Measurable.of_discrete)
  have hsub : ∀ i ∈ S, HasSubgaussianMGF (Xf i) ((‖(t : ℝ) - (-1)‖₊ / 2) ^ 2) (P n t p) := by
    intro i _
    have h := hasSubgaussianMGF_of_mem_Icc (X := fun ω => V i (ω i)) (μ := P n t p)
      (a := -1) (b := t) ((Measurable.of_discrete (f := V i)).comp (measurable_pi_apply i)).aemeasurable
      (ae_of_all _ (fun ω => by
        have h1 := advCount_le (ω i)
        have h2 := roundY_le_one (ω i)
        have h1' : (advCount (ω i) : ℝ) ≤ t := by exact_mod_cast h1
        have h2' : (roundY (ω i) : ℝ) ≤ 1 := by exact_mod_cast h2
        have h3 : (0 : ℝ) ≤ advCount (ω i) := Nat.cast_nonneg _
        have h4 : (0 : ℝ) ≤ roundY (ω i) := Nat.cast_nonneg _
        simp only [V, Set.mem_Icc]
        split_ifs <;> constructor <;> linarith))
    rw [hVint i] at h
    exact h
  have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub hε
  have hset : {ω : Trace n t | ∑ i ∈ T, Y ω i + j ≤ ∑ i ∈ S, Z ω i} =
      {ω | ε ≤ ∑ i ∈ S, Xf i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Xf, V]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hTS]
    simp only [Finset.sum_const, nsmul_eq_mul, hεdef]
    have : ∀ i, (advCount (ω i) : ℝ) = Z ω i := fun i => rfl
    have : ∀ i, (roundY (ω i) : ℝ) = Y ω i := fun i => rfl
    simp only [*]
    constructor
    · intro h
      have : ((∑ i ∈ T, Y ω i + j : ℕ) : ℝ) ≤ ((∑ i ∈ S, Z ω i : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this
      linarith
    · intro h
      have : ((∑ i ∈ T, Y ω i + j : ℕ) : ℝ) ≤ ((∑ i ∈ S, Z ω i : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast this
  rw [hset]
  refine hH.trans (le_of_eq ?_)
  congr 1
  simp only [Finset.sum_const, nsmul_eq_mul]
  push_cast
  rw [sub_neg_eq_add, Real.norm_of_nonneg (by positivity)]
  rcases Nat.eq_zero_or_pos S.card with h | h
  · simp [h]
  · have : (0 : ℝ) < S.card := by exact_mod_cast h
    field_simp

private theorem exp_le_rate (ε m c k s : ℝ) (hc : 0 < c) (hs : 0 < s) (hsk : s ≤ k + 1)
    (hm : 0 ≤ m) (hk : 0 ≤ k + 1) (hε : (k + 1) * m ≤ 2 * ε) :
    Real.exp (-2 * ε ^ 2 / (s * c)) ≤ Real.exp (-(m ^ 2 / (2 * c)) * (k + 1)) := by
  apply Real.exp_le_exp.2
  have h1 : 0 ≤ (k + 1) * m := mul_nonneg hk hm
  have h2 : ((k + 1) * m) ^ 2 ≤ (2 * ε) ^ 2 := pow_le_pow_left₀ h1 hε 2
  have h3 : m ^ 2 * (k + 1) * s ≤ m ^ 2 * (k + 1) * (k + 1) :=
    mul_le_mul_of_nonneg_left hsk (by positivity)
  have e : -2 * ε ^ 2 / (s * c) = -(2 * ε ^ 2 / (s * c)) := by ring
  rw [e, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith

/-- Union bound: if typicality fails on each window `[a, a + k]` with `lam ≤ k` with probability at
most `β`, then it fails somewhere on the horizon `[0, L]` with probability at most `L² β`. -/
theorem solution (n t : ℕ) (p : unitInterval)
    (lam L : ℕ) (hlam : 1 ≤ lam) (β : ℝ)
    (hβ : ∀ a k : ℕ, lam ≤ k → (P n t p).real
      {ω | ∑ i ∈ Finset.Ioo a (a + k), Y ω i ≤ ∑ i ∈ Finset.Icc a (a + k), Z ω i} ≤ β) :
    (P n t p).real {ω | ¬ TypicalOn ω lam L} ≤ (L : ℝ) ^ 2 * β := by
  classical
  have hβ0 : 0 ≤ β := measureReal_nonneg.trans (hβ 0 lam le_rfl)
  let W : Finset (ℕ × ℕ) := (Finset.range L ×ˢ Finset.Icc 1 L).filter (fun x => x.1 + lam ≤ x.2)
  let F : ℕ × ℕ → Set (Trace n t) := fun x =>
    {ω | ∑ i ∈ Finset.Ioo x.1 x.2, Y ω i ≤ ∑ i ∈ Finset.Icc x.1 x.2, Z ω i}
  have hsub : {ω : Trace n t | ¬ TypicalOn ω lam L} ⊆ ⋃ x ∈ W, F x := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, TypicalOn, not_forall, not_lt] at hω
    obtain ⟨a, b, hab, hbL, hfail⟩ := hω
    simp only [Set.mem_iUnion]
    refine ⟨(a, b), ?_, hfail⟩
    simp only [W, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_Icc]
    omega
  have hcard : (W.card : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : W.card ≤ L * L := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_product]; simp
    have : (W.card : ℝ) ≤ ((L * L : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; nlinarith
  calc (P n t p).real {ω | ¬ TypicalOn ω lam L}
      ≤ (P n t p).real (⋃ x ∈ W, F x) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ x ∈ W, (P n t p).real (F x) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ W, β := by
        apply Finset.sum_le_sum
        rintro ⟨a, b⟩ hx
        simp only [W, Finset.mem_filter] at hx
        obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
        exact hβ a k (by omega)
    _ = W.card * β := by simp
    _ ≤ (L : ℝ) ^ 2 * β := mul_le_mul_of_nonneg_right hcard hβ0
