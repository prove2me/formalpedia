-- Prove2me | solution 1 for GMCPBandit.Regret.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T14:42:50.17877+00:00
-- url     : https://prove2.me/submissions/1bd55f56-f71c-4a1c-9679-d7437c965cae

import Mathlib
import Definitions.Def_GMCPBandit_Regret_Model
import Definitions.Def_GMCPBandit_Regret_Algorithm

open MeasureTheory ProbabilityTheory

namespace GMCPChernoff

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*}

/-- For a `{0,1}`-valued variable, `e^{tY} = 1 + (e^t − 1) Y`. -/
lemma exp_mul_01 (y t : ℝ) (hy : y = 0 ∨ y = 1) :
    Real.exp (t * y) = 1 + (Real.exp t - 1) * y := by
  rcases hy with rfl | rfl <;> simp

lemma mgf_01_le (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y)
    (h01 : ∀ ω, Y ω = 0 ∨ Y ω = 1) (t : ℝ) :
    mgf Y P t ≤ Real.exp ((Real.exp t - 1) * ∫ ω, Y ω ∂P) := by
  have hint : Integrable Y P := by
    refine Integrable.of_bound hY.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
    rcases h01 ω with h | h <;> simp [h]
  have : mgf Y P t = 1 + (Real.exp t - 1) * ∫ ω, Y ω ∂P := by
    unfold mgf
    simp_rw [fun ω => exp_mul_01 (Y ω) t (h01 ω)]
    rw [integral_add (integrable_const _) (hint.const_mul _), integral_const_mul]
    simp
  rw [this]
  have := Real.add_one_le_exp ((Real.exp t - 1) * ∫ ω, Y ω ∂P)
  linarith

lemma integral_01_mem (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (h01 : ∀ ω, Y ω = 0 ∨ Y ω = 1) : 0 ≤ ∫ ω, Y ω ∂P ∧ ∫ ω, Y ω ∂P ≤ 1 := by
  have h0 : ∀ ω, 0 ≤ Y ω := fun ω => by rcases h01 ω with h | h <;> simp [h]
  have h1 : ∀ ω, Y ω ≤ 1 := fun ω => by rcases h01 ω with h | h <;> simp [h]
  refine ⟨integral_nonneg h0, ?_⟩
  calc ∫ ω, Y ω ∂P ≤ ∫ _ω, (1 : ℝ) ∂P := by
        by_cases hi : Integrable Y P
        · exact integral_mono hi (integrable_const _) h1
        · rw [integral_undef hi]; simp
    _ = 1 := by simp

lemma mgf_sum_le (P : Measure Ω) [IsProbabilityMeasure P] (Y : ι → Ω → ℝ)
    (hind : iIndepFun Y P) (hmeas : ∀ i, Measurable (Y i))
    (h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1) (S : Finset ι) (t : ℝ) :
    mgf (∑ i ∈ S, Y i) P t ≤ Real.exp ((Real.exp t - 1) * ∑ i ∈ S, ∫ ω, Y i ω ∂P) := by
  rw [hind.mgf_sum hmeas S, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => ?_)
  exact mgf_01_le P (Y i) (hmeas i) (h01 i) t

lemma integrable_exp_sum (P : Measure Ω) [IsProbabilityMeasure P] (Y : ι → Ω → ℝ)
    (hmeas : ∀ i, Measurable (Y i)) (h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1) (S : Finset ι) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * (∑ i ∈ S, Y i) ω)) P := by
  have hm : Measurable (fun ω => (∑ i ∈ S, Y i) ω) := by
    simp only [Finset.sum_apply]
    exact Finset.measurable_sum S (fun i _ => hmeas i)
  refine Integrable.of_bound (by fun_prop) (Real.exp (|t| * S.card))
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hb : |(∑ i ∈ S, Y i) ω| ≤ S.card := by
    rw [Finset.sum_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ S, |Y i ω| ≤ ∑ _i ∈ S, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => by rcases h01 i ω with h | h <;> simp [h]
      _ = S.card := by simp
  calc t * (∑ i ∈ S, Y i) ω ≤ |t * (∑ i ∈ S, Y i) ω| := le_abs_self _
    _ = |t| * |(∑ i ∈ S, Y i) ω| := abs_mul _ _
    _ ≤ |t| * S.card := mul_le_mul_of_nonneg_left hb (abs_nonneg _)

/-- **Chernoff upper tail** for a sum of independent `{0,1}` variables. -/
theorem chernoff_upper (P : Measure Ω) [IsProbabilityMeasure P] (Y : ι → Ω → ℝ)
    (hind : iIndepFun Y P) (hmeas : ∀ i, Measurable (Y i))
    (h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1) (S : Finset ι) (s : ℝ) (hs : 0 ≤ s) (B : ℝ) :
    P.real {ω | B ≤ ∑ i ∈ S, Y i ω} ≤
      Real.exp (-s * B + (Real.exp s - 1) * ∑ i ∈ S, ∫ ω, Y i ω ∂P) := by
  have h := measure_ge_le_exp_mul_mgf (X := ∑ i ∈ S, Y i) (μ := P) B hs
    (integrable_exp_sum P Y hmeas h01 S s)
  have h2 := mgf_sum_le P Y hind hmeas h01 S s
  simp only [Finset.sum_apply] at h
  calc _ ≤ _ := h
    _ ≤ Real.exp (-s * B) * Real.exp ((Real.exp s - 1) * ∑ i ∈ S, ∫ ω, Y i ω ∂P) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]

/-- **Chernoff lower tail** for a sum of independent `{0,1}` variables. -/
theorem chernoff_lower (P : Measure Ω) [IsProbabilityMeasure P] (Y : ι → Ω → ℝ)
    (hind : iIndepFun Y P) (hmeas : ∀ i, Measurable (Y i))
    (h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1) (S : Finset ι) (s : ℝ) (hs : 0 ≤ s) (a : ℝ) :
    P.real {ω | ∑ i ∈ S, Y i ω ≤ a} ≤
      Real.exp (s * a + (Real.exp (-s) - 1) * ∑ i ∈ S, ∫ ω, Y i ω ∂P) := by
  have h := measure_le_le_exp_mul_mgf (X := ∑ i ∈ S, Y i) (μ := P) a (t := -s) (by linarith)
    (integrable_exp_sum P Y hmeas h01 S (-s))
  have h2 := mgf_sum_le P Y hind hmeas h01 S (-s)
  simp only [Finset.sum_apply] at h
  calc _ ≤ _ := h
    _ ≤ Real.exp (- -s * a) * Real.exp ((Real.exp (-s) - 1) * ∑ i ∈ S, ∫ ω, Y i ω ∂P) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, neg_neg]

end GMCPChernoff

namespace GMCPHarm

/-- `G(x) = ∫₀ˣ min(1, t₀/y) dy`. -/
noncomputable def G (t0 x : ℝ) : ℝ := if x ≤ t0 then x else t0 * (1 + Real.log x - Real.log t0)

lemma G_of_ge {t0 x : ℝ} (ht0 : 0 < t0) (hx : t0 ≤ x) :
    G t0 x = t0 * (1 + Real.log x - Real.log t0) := by
  unfold G
  split_ifs with h
  · have : x = t0 := le_antisymm h hx
    subst this; ring
  · rfl

lemma G_of_le {t0 x : ℝ} (hx : x ≤ t0) : G t0 x = x := by
  unfold G; rw [if_pos hx]

lemma phi_eq_one {t0 τ : ℝ} (hτ : 0 < τ) (h : τ ≤ t0) : min 1 (t0 / τ) = 1 :=
  min_eq_left ((one_le_div hτ).mpr h)

lemma phi_eq_div {t0 τ : ℝ} (hτ : 0 < τ) (h : t0 ≤ τ) : min 1 (t0 / τ) = t0 / τ :=
  min_eq_right ((div_le_one hτ).mpr h)

lemma phi_le_G_diff {t0 : ℝ} (ht0 : 0 < t0) (τ : ℝ) (hτ : 1 ≤ τ) :
    min 1 (t0 / τ) ≤ G t0 τ - G t0 (τ - 1) := by
  have hτ0 : 0 < τ := by linarith
  rcases le_or_gt τ t0 with h1 | h1
  · rw [phi_eq_one hτ0 h1, G_of_le h1, G_of_le (by linarith)]; ring_nf; rfl
  · rw [phi_eq_div hτ0 h1.le, G_of_ge ht0 h1.le]
    rcases le_or_gt t0 (τ - 1) with h2 | h2
    · rw [G_of_ge ht0 h2]
      have hτ1 : 0 < τ - 1 := lt_of_lt_of_le ht0 h2
      have hl := Real.log_le_sub_one_of_pos (show 0 < (τ - 1) / τ by positivity)
      rw [Real.log_div hτ1.ne' hτ0.ne'] at hl
      have : (τ - 1) / τ - 1 = -(1 / τ) := by field_simp; ring
      rw [this] at hl
      have : t0 / τ = t0 * (1 / τ) := by ring
      rw [this]
      nlinarith
    · rw [G_of_le h2.le]
      have hl := Real.log_le_sub_one_of_pos (show 0 < t0 / τ by positivity)
      rw [Real.log_div ht0.ne' hτ0.ne'] at hl
      -- t0 log(τ/t0) ≥ t0 (1 - t0/τ)
      have key : t0 * (1 - t0 / τ) ≤ t0 * (Real.log τ - Real.log t0) := by
        apply mul_le_mul_of_nonneg_left _ ht0.le; linarith
      have hq : t0 / τ ≤ t0 * (1 - t0 / τ) + t0 - τ + 1 := by
        rw [div_le_iff₀ hτ0]
        have e1 : (t0 * (1 - t0 / τ) + t0 - τ + 1) * τ = 2 * t0 * τ - t0 ^ 2 - τ ^ 2 + τ := by
          field_simp; ring
        rw [e1]; nlinarith
      nlinarith

lemma G_diff_le_phi {t0 : ℝ} (ht0 : 0 < t0) (τ : ℝ) (hτ : 1 ≤ τ) :
    G t0 (τ + 1) - G t0 τ ≤ min 1 (t0 / τ) := by
  have hτ0 : 0 < τ := by linarith
  rcases le_or_gt t0 τ with h1 | h1
  · rw [phi_eq_div hτ0 h1, G_of_ge ht0 h1, G_of_ge ht0 (by linarith)]
    have hl := Real.log_le_sub_one_of_pos (show 0 < (τ + 1) / τ by positivity)
    rw [Real.log_div (by linarith) hτ0.ne'] at hl
    have : (τ + 1) / τ - 1 = 1 / τ := by field_simp; ring
    rw [this] at hl
    have : t0 / τ = t0 * (1 / τ) := by ring
    rw [this]; nlinarith
  · rw [phi_eq_one hτ0 h1.le, G_of_le h1.le]
    rcases le_or_gt (τ + 1) t0 with h2 | h2
    · rw [G_of_le h2]; linarith
    · rw [G_of_ge ht0 h2.le]
      have hl := Real.log_le_sub_one_of_pos (show 0 < (τ + 1) / t0 by positivity)
      rw [Real.log_div (by linarith) ht0.ne'] at hl
      have : t0 * ((τ + 1) / t0 - 1) = τ + 1 - t0 := by field_simp
      nlinarith

/-- `∑_{t=1}^T min(1, t₀/t) ≤ G(T)`. -/
lemma sum_le_G {t0 : ℝ} (ht0 : 0 < t0) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, min 1 (t0 / (t : ℝ)) ≤ G t0 T := by
  induction T with
  | zero => simp [G_of_le ht0.le]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := phi_le_G_diff ht0 ((n + 1 : ℕ) : ℝ) (by simp)
    push_cast at this ⊢
    have e : (n : ℝ) + 1 - 1 = n := by ring
    rw [e] at this
    linarith

/-- `∑_{t=1}^T min(1, t₀/t) ≥ G(T+1) − G(1)`. -/
lemma G_le_sum {t0 : ℝ} (ht0 : 0 < t0) (T : ℕ) :
    G t0 ((T : ℝ) + 1) - G t0 1 ≤ ∑ t ∈ Finset.Icc 1 T, min 1 (t0 / (t : ℝ)) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := G_diff_le_phi ht0 ((n + 1 : ℕ) : ℝ) (by simp)
    push_cast at this ⊢
    linarith

end GMCPHarm

namespace GMCPProp2

open GMCPBandit.Regret

lemma sum_range_eq_Icc (f : ℕ → ℝ) (T : ℕ) :
    ∑ j ∈ Finset.range T, f (j + 1) = ∑ t ∈ Finset.Icc 1 T, f t := by
  induction T with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

/-- The exploration indicator `1{V_{j+1} ≤ min(1, t₀/(j+1)), A_{j+1} = k}`. -/
noncomputable def ind {Ω : Type*} {K : ℕ} (t0 : ℝ) (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K)
    (k : Fin K) (j : ℕ) (ω : Ω) : ℝ :=
  by classical exact
    (if V (j + 1) ω ≤ min 1 (t0 / ((j + 1 : ℕ) : ℝ)) ∧ A (j + 1) ω = k then 1 else 0)

lemma ind_01 {Ω : Type*} {K : ℕ} (t0 : ℝ) (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K)
    (k : Fin K) (j : ℕ) (ω : Ω) : ind t0 V A k j ω = 0 ∨ ind t0 V A k j ω = 1 := by
  unfold ind; split_ifs <;> simp

lemma card_randomSet {Ω : Type*} {K : ℕ} (t0 : ℝ) (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K)
    (k : Fin K) (T : ℕ) (ω : Ω) :
    ((randomSet t0 (fun s => V s ω) (fun s => A s ω) k T).card : ℝ) =
      ∑ j ∈ Finset.range T, ind t0 V A k j ω := by
  classical
  unfold randomSet
  rw [Finset.card_filter]
  push_cast
  rw [← sum_range_eq_Icc]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold ind explore
  simp only

lemma indep_ind {Ω : Type*} [MeasurableSpace Ω] {K : ℕ} (P : Measure Ω) (t0 : ℝ)
    (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K) (hVA : IsExplorationCoins P V A) (k : Fin K) :
    iIndepFun (fun j => ind t0 V A k j) P := by
  classical
  have hg : ∀ j : ℕ, Measurable (fun p : ℝ × Fin K =>
      if p.1 ≤ min 1 (t0 / ((j + 1 : ℕ) : ℝ)) ∧ p.2 = k then (1 : ℝ) else 0) := by
    intro j
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (measurable_fst measurableSet_Iic).inter (measurable_snd (measurableSet_singleton k))
  have := hVA.iIndep_time.comp _ hg
  convert this using 1
  funext j ω
  simp only [ind, Function.comp]

lemma measurable_ind {Ω : Type*} [MeasurableSpace Ω] {K : ℕ} (P : Measure Ω) (t0 : ℝ)
    (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K) (hVA : IsExplorationCoins P V A) (k : Fin K) (j : ℕ) :
    Measurable (ind t0 V A k j) := by
  classical
  unfold ind
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (hVA.measurable_V (j + 1) (by omega) measurableSet_Iic).inter
    (hVA.measurable_A (j + 1) (by omega) (measurableSet_singleton k))

lemma integral_ind {Ω : Type*} [MeasurableSpace Ω] {K : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (t0 : ℝ) (ht0 : 0 < t0)
    (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K) (hVA : IsExplorationCoins P V A) (k : Fin K) (j : ℕ) :
    ∫ ω, ind t0 V A k j ω ∂P = min 1 (t0 / ((j + 1 : ℕ) : ℝ)) / K := by
  classical
  set c := min 1 (t0 / ((j + 1 : ℕ) : ℝ)) with hc
  have hc0 : 0 ≤ c := le_min zero_le_one (by positivity)
  have hc1 : c ≤ 1 := min_le_left _ _
  set E := V (j + 1) ⁻¹' Set.Iic c ∩ A (j + 1) ⁻¹' {k} with hE
  have hmE : MeasurableSet E := (hVA.measurable_V (j + 1) (by omega) measurableSet_Iic).inter
    (hVA.measurable_A (j + 1) (by omega) (measurableSet_singleton k))
  have hind : ind t0 V A k j = E.indicator 1 := by
    funext ω
    simp only [ind, Set.indicator, hE, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic,
      Set.mem_singleton_iff, Pi.one_apply]
    rfl
  rw [hind, integral_indicator_one hmE]
  have hPE : P E = ENNReal.ofReal c * (K : ENNReal)⁻¹ := by
    rw [hE, (hVA.indep_V_A (j + 1) (by omega)).measure_inter_preimage_eq_mul _ _
      measurableSet_Iic (measurableSet_singleton k)]
    congr 1
    · rw [← Measure.map_apply (hVA.measurable_V (j + 1) (by omega)) measurableSet_Iic,
        hVA.law_V (j + 1) (by omega), Measure.restrict_apply measurableSet_Iic]
      have : Set.Iic c ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 c := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        constructor
        · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hc1⟩
      rw [this, Real.volume_Icc, sub_zero]
    · exact hVA.law_A (j + 1) (by omega) k
  rw [measureReal_def, hPE, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0, ENNReal.toReal_inv]
  simp [div_eq_mul_inv]

end GMCPProp2

open GMCPBandit.Regret GMCPProp2 GMCPChernoff GMCPHarm in
theorem solution {K : ℕ} (hK : 2 ≤ K) (C0 t0 : ℝ) (hC0 : 10 ≤ C0) (ht0 : t0 = 2 * C0 * K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K) (hVA : IsExplorationCoins P V A)
    (T : ℕ) (hT : (t0 + 1) ^ 2 / Real.exp 1 ^ 2 < (T : ℝ)) (k : Fin K) :
    ENNReal.ofReal (1 - 2 / ((T : ℝ) + 1)) ≤
      P {ω | C0 * (1 + Real.log ((T : ℝ) + 1) - Real.log (t0 + 1)) ≤
              ((randomSet t0 (fun s => V s ω) (fun s => A s ω) k T).card : ℝ) ∧
            ((randomSet t0 (fun s => V s ω) (fun s => A s ω) k T).card : ℝ) ≤
              3 * C0 * (1 + Real.log (T : ℝ) - Real.log t0)} := by
  classical
  -- numerics
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have ht0_40 : 40 ≤ t0 := by rw [ht0]; nlinarith
  have ht0pos : 0 < t0 := by linarith
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hT' : (t0 + 1) ^ 2 < (T : ℝ) * Real.exp 1 ^ 2 := by
    rwa [div_lt_iff₀ (by positivity)] at hT
  have he2 : Real.exp 1 ^ 2 < 7.4 := by nlinarith
  have hTge : t0 + 1 ≤ (T : ℝ) := by
    have h0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    have : (T : ℝ) * Real.exp 1 ^ 2 ≤ (T : ℝ) * 7.4 := by nlinarith
    nlinarith
  have hTpos : (0 : ℝ) < T := by linarith
  set u := Real.log (T : ℝ) with hu
  set L := Real.log ((T : ℝ) + 1) with hL
  set l0 := Real.log t0 with hl0
  set l1 := Real.log (t0 + 1) with hl1
  have hl1u : 2 * l1 < 2 + u := by
    have := Real.log_lt_log (by positivity) hT'
    rw [Real.log_pow, Real.log_mul hTpos.ne' (by positivity), Real.log_pow, Real.log_exp] at this
    push_cast at this; linarith
  have hl0l1 : l0 ≤ l1 := Real.log_le_log ht0pos (by linarith)
  have huL : u ≤ L := Real.log_le_log hTpos (by linarith)
  have hLu : L ≤ u + 1 / T := by
    have := Real.log_le_sub_one_of_pos (show 0 < ((T : ℝ) + 1) / T by positivity)
    rw [Real.log_div (by positivity) hTpos.ne'] at this
    have e : ((T : ℝ) + 1) / T - 1 = 1 / T := by field_simp; ring
    linarith
  have hu1 : 1 ≤ u := by
    rw [hu, Real.le_log_iff_exp_le hTpos]; linarith
  have hinvT : 1 / (T : ℝ) ≤ 1 / 41 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith
  -- the count as a sum of independent indicators
  set n : Ω → ℝ := fun ω => ∑ j ∈ Finset.range T, ind t0 V A k j ω with hn
  have hcard : ∀ ω, ((randomSet t0 (fun s => V s ω) (fun s => A s ω) k T).card : ℝ) = n ω :=
    fun ω => card_randomSet t0 V A k T ω
  set Sφ := ∑ t ∈ Finset.Icc 1 T, min 1 (t0 / (t : ℝ)) with hSφ
  have hμ : ∑ j ∈ Finset.range T, ∫ ω, ind t0 V A k j ω ∂P = Sφ / K := by
    simp_rw [integral_ind P t0 ht0pos V A hVA k]
    rw [← Finset.sum_div, sum_range_eq_Icc (fun t => min 1 (t0 / (t : ℝ)))]
  have hSup : Sφ ≤ t0 * (1 + u - l0) := by
    have := sum_le_G ht0pos T
    rwa [G_of_ge ht0pos (by linarith)] at this
  have hSlo : t0 * (1 + L - l0) - 1 ≤ Sφ := by
    have := G_le_sum ht0pos T
    rwa [G_of_ge ht0pos (by linarith), G_of_le (by linarith)] at this
  have ht0K : t0 / K = 2 * C0 := by rw [ht0]; field_simp
  have hind := indep_ind P t0 V A hVA k
  have hmeas := measurable_ind P t0 V A hVA k
  have h01 := ind_01 t0 V A k
  -- lower tail
  set a := C0 * (1 + L - l1) with ha
  have ha5 : 5 * L ≤ a := by
    have hX : L / 2 ≤ 1 + L - l1 := by linarith
    have hX0 : 0 ≤ L / 2 := by linarith
    have : 10 * (L / 2) ≤ C0 * (1 + L - l1) := mul_le_mul hC0 hX hX0 (by linarith)
    rw [ha]; linarith
  have hlo := chernoff_lower P (ind t0 V A k) hind hmeas h01 (Finset.range T) (Real.log 2)
    (Real.log_nonneg (by norm_num)) a
  rw [hμ, Real.exp_neg, Real.exp_log (by norm_num)] at hlo
  have hμlo : 2 * a - 1 / K ≤ Sφ / K := by
    have h1 : t0 * (1 + L - l1) - 1 ≤ Sφ := by nlinarith
    have h2 : (t0 * (1 + L - l1) - 1) / K ≤ Sφ / K := div_le_div_of_nonneg_right h1 hKpos.le
    have h3 : (t0 * (1 + L - l1) - 1) / K = 2 * a - 1 / K := by
      rw [sub_div, mul_comm t0, mul_div_assoc, div_eq_mul_inv t0, ← div_eq_mul_inv, ht0K, ha]
      ring
    linarith
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hK1 : 1 / (K : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hK2
  have hexp_lo : Real.log 2 * a + (2⁻¹ - 1) * (Sφ / K) ≤ -L := by
    have ha0 : 0 ≤ a := by linarith
    have : Real.log 2 * a ≤ 0.6931471808 * a := mul_le_mul_of_nonneg_right hlog2.le ha0
    have h32 : (2⁻¹ - 1 : ℝ) * (Sφ / K) ≤ (2⁻¹ - 1) * (2 * a - 1 / K) :=
      mul_le_mul_of_nonpos_left hμlo (by norm_num)
    linarith
  have hPlo : P.real {ω | n ω ≤ a} ≤ 1 / ((T : ℝ) + 1) := by
    refine hlo.trans ((Real.exp_le_exp.mpr hexp_lo).trans ?_)
    rw [Real.exp_neg, hL, Real.exp_log (by positivity), one_div]
  -- upper tail
  set B := 3 * C0 * (1 + u - l0) with hB
  have hB15 : 15 * u ≤ B := by
    have hX : u / 2 ≤ 1 + u - l0 := by linarith
    have hX0 : 0 ≤ u / 2 := by linarith
    have : 3 * 10 * (u / 2) ≤ 3 * C0 * (1 + u - l0) :=
      mul_le_mul (by linarith) hX hX0 (by linarith)
    rw [hB]; linarith
  have hup := chernoff_upper P (ind t0 V A k) hind hmeas h01 (Finset.range T) (Real.log (3 / 2))
    (Real.log_nonneg (by norm_num)) B
  rw [hμ, Real.exp_log (by norm_num)] at hup
  have hμup : Sφ / K ≤ 2 / 3 * B := by
    have h2 : Sφ / K ≤ t0 * (1 + u - l0) / K := div_le_div_of_nonneg_right hSup hKpos.le
    have h3 : t0 * (1 + u - l0) / K = 2 / 3 * B := by
      rw [mul_comm t0, mul_div_assoc, ht0K, hB]; ring
    linarith
  have hlog32 : 0.4054651077 ≤ Real.log (3 / 2) := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    have h3 := Real.log_three_near_10
    have h2 := Real.log_two_lt_d9
    rw [abs_le] at h3
    norm_num at h3 h2 ⊢
    linarith
  have hexp_up : -Real.log (3 / 2) * B + (3 / 2 - 1) * (Sφ / K) ≤ -L := by
    have hB0 : 0 ≤ B := by linarith
    have : 0.4054651077 * B ≤ Real.log (3 / 2) * B := mul_le_mul_of_nonneg_right hlog32 hB0
    have h32 : (3 / 2 - 1 : ℝ) * (Sφ / K) ≤ (3 / 2 - 1) * (2 / 3 * B) :=
      mul_le_mul_of_nonneg_left hμup (by norm_num)
    have hneg : -Real.log (3 / 2) * B = -(Real.log (3 / 2) * B) := by ring
    rw [hneg]
    linarith
  have hPup : P.real {ω | B ≤ n ω} ≤ 1 / ((T : ℝ) + 1) := by
    refine hup.trans ((Real.exp_le_exp.mpr hexp_up).trans ?_)
    rw [Real.exp_neg, hL, Real.exp_log (by positivity), one_div]
  -- combine
  have hnm : Measurable n := by
    rw [hn]; exact Finset.measurable_sum _ (fun j _ => hmeas j)
  have hset : {ω | C0 * (1 + Real.log ((T : ℝ) + 1) - Real.log (t0 + 1)) ≤
              ((randomSet t0 (fun s => V s ω) (fun s => A s ω) k T).card : ℝ) ∧
            ((randomSet t0 (fun s => V s ω) (fun s => A s ω) k T).card : ℝ) ≤
              3 * C0 * (1 + Real.log (T : ℝ) - Real.log t0)} = {ω | a ≤ n ω ∧ n ω ≤ B} := by
    ext ω; simp only [Set.mem_setOf_eq, hcard ω]; rfl
  rw [hset]
  have hgm : MeasurableSet {ω | a ≤ n ω ∧ n ω ≤ B} :=
    (measurableSet_le measurable_const hnm).inter (measurableSet_le hnm measurable_const)
  have hsub : {ω | a ≤ n ω ∧ n ω ≤ B}ᶜ ⊆ {ω | n ω ≤ a} ∪ {ω | B ≤ n ω} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_le] at hω
    rcases hω with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le
  have hcompl := probReal_compl_eq_one_sub (μ := P) hgm
  have hc2 : P.real {ω | a ≤ n ω ∧ n ω ≤ B}ᶜ ≤ 2 / ((T : ℝ) + 1) := by
    refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
    have : 2 / ((T : ℝ) + 1) = 1 / ((T : ℝ) + 1) + 1 / ((T : ℝ) + 1) := by ring
    rw [this]; exact add_le_add hPlo hPup
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  linarith
