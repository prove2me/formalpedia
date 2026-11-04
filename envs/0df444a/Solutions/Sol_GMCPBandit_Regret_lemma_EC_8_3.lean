-- Prove2me | solution 1 for GMCPBandit.Regret.lemma_EC_8_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T14:49:42.401136+00:00
-- url     : https://prove2.me/submissions/9ee0b1dd-53bf-45f2-9239-7626cc81bc25

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

namespace GMCPEC8

open GMCPBandit.Regret GMCPProp2

lemma sfinite_of_glm {ν : Measure ℝ} {g : ℝ → ℝ → ℝ} {Rmax : ℝ} (hglm : IsGLMFamily ν g Rmax) :
    SFinite ν := by
  set f : ℝ → ENNReal := fun r => ENNReal.ofReal (g r 0) with hf
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp (hglm.measurable_g.comp (measurable_id.prodMk measurable_const))
  have hae : ∀ᵐ r ∂ν, r ∈ Set.Icc (-Rmax) Rmax := mem_ae_iff.mpr hglm.concentrated
  have hne0 : ∀ᵐ r ∂ν, f r ≠ 0 := hae.mono fun r hr => by
    simp only [hf, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hglm.pos r hr 0
  have hneT : ∀ᵐ r ∂ν, f r ≠ ⊤ := Filter.Eventually.of_forall fun r => ENNReal.ofReal_ne_top
  have hfin : IsFiniteMeasure (ν.withDensity f) :=
    isFiniteMeasure_withDensity_ofReal (hglm.integrable 0).2
  have hsig : SigmaFinite ((ν.withDensity f).withDensity (fun r => (f r)⁻¹)) := by
    refine SigmaFinite.withDensity_of_ne_top ?_
    have : ∀ᵐ r ∂(ν.withDensity f), f r ≠ 0 := (withDensity_absolutelyContinuous ν f).ae_le hne0
    exact this.mono fun r hr => ENNReal.inv_ne_top.mpr hr
  rw [withDensity_inv_same hfm hne0 hneT] at hsig
  infer_instance

lemma measurable_meanFn {ν : Measure ℝ} {g : ℝ → ℝ → ℝ} {Rmax : ℝ} (hglm : IsGLMFamily ν g Rmax) :
    Measurable (meanFn ν g) := by
  have := sfinite_of_glm hglm
  have hm : Measurable (Function.uncurry fun (η r : ℝ) => r * g r η) :=
    measurable_snd.mul (hglm.measurable_g.comp measurable_swap)
  exact (hm.stronglyMeasurable.integral_prod_right (ν := ν)).measurable

lemma measurableSet_optRegion {d K : ℕ} {𝒳 : Set (Fin d → ℝ)} {ν : Measure ℝ} {g : ℝ → ℝ → ℝ}
    {Rmax : ℝ} (hglm : IsGLMFamily ν g Rmax) (h𝒳 : MeasurableSet 𝒳) (β : Fin K → Fin d → ℝ)
    (h : ℝ) (k : Fin K) : MeasurableSet (optRegion 𝒳 ν g β h k) := by
  have hmf := measurable_meanFn hglm
  have hj : ∀ j : Fin K, Measurable (fun x : Fin d → ℝ => meanFn ν g (x ⬝ᵥ β j)) := fun j =>
    hmf.comp (continuous_id.dotProduct continuous_const).measurable
  have hmax : Measurable (fun x => maxOther ν g β x k) := by
    unfold maxOther
    exact Measurable.iSup fun j => hj j.1
  exact h𝒳.inter (measurableSet_lt (hmax.add_const h) (hj k))


/-- `1{V_{j+1} ≤ min(1, t₀/(j+1)), A_{j+1} = k, X_{j+1} ∈ U}`. -/
noncomputable def ind2 {Ω : Type*} {d K : ℕ} (t0 : ℝ) (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K)
    (X : ℕ → Ω → Fin d → ℝ) (U : Set (Fin d → ℝ)) (k : Fin K) (j : ℕ) (ω : Ω) : ℝ :=
  by classical exact
    (if V (j + 1) ω ≤ min 1 (t0 / ((j + 1 : ℕ) : ℝ)) ∧ A (j + 1) ω = k ∧ X (j + 1) ω ∈ U
      then 1 else 0)

lemma ind2_01 {Ω : Type*} {d K : ℕ} (t0 : ℝ) (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K)
    (X : ℕ → Ω → Fin d → ℝ) (U : Set (Fin d → ℝ)) (k : Fin K) (j : ℕ) (ω : Ω) :
    ind2 t0 V A X U k j ω = 0 ∨ ind2 t0 V A X U k j ω = 1 := by
  unfold ind2; split_ifs <;> simp

lemma card_randomSamplesIn {Ω : Type*} {d K : ℕ} (t0 : ℝ) (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K)
    (X : ℕ → Ω → Fin d → ℝ) (U : Set (Fin d → ℝ)) (k : Fin K) (T : ℕ) (ω : Ω) :
    ((randomSamplesIn t0 (fun s => V s ω) (fun s => A s ω) (fun s => X s ω) U k T).card : ℝ) =
      ∑ j ∈ Finset.range T, ind2 t0 V A X U k j ω := by
  classical
  unfold randomSamplesIn randomSet
  rw [Finset.filter_filter, Finset.card_filter]
  push_cast
  rw [← sum_range_eq_Icc]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold ind2 explore
  simp only [and_assoc]

lemma indep_ind2 {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ} (P : Measure Ω)
    {𝒳 : Set (Fin d → ℝ)} {PX : Measure (Fin d → ℝ)} {ν : Measure ℝ} {g : ℝ → ℝ → ℝ}
    {β : Fin K → Fin d → ℝ} {Rmax : ℝ} (t0 : ℝ) (X : ℕ → Ω → Fin d → ℝ) (R : ℕ → Ω → Fin K → ℝ)
    (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K) (hprim : IsPrimitives P 𝒳 PX ν g β Rmax X R V A)
    (U : Set (Fin d → ℝ)) (hU : MeasurableSet U) (k : Fin K) :
    iIndepFun (fun j => ind2 t0 V A X U k j) P := by
  classical
  have hg : ∀ j : ℕ, Measurable (fun p : (Fin d → ℝ) × (Fin K → ℝ) × ℝ × Fin K =>
      if p.2.2.1 ≤ min 1 (t0 / ((j + 1 : ℕ) : ℝ)) ∧ p.2.2.2 = k ∧ p.1 ∈ U
        then (1 : ℝ) else 0) := by
    intro j
    refine Measurable.ite ?_ measurable_const measurable_const
    exact ((measurable_fst.comp (measurable_snd.comp measurable_snd)) measurableSet_Iic).inter
      (((measurable_snd.comp (measurable_snd.comp measurable_snd)) (measurableSet_singleton k)).inter
        (measurable_fst hU))
  have := hprim.iIndep_time.comp _ hg
  convert this using 1
  funext j ω
  simp only [ind2, Function.comp]

lemma measurable_ind2 {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ} (P : Measure Ω)
    {𝒳 : Set (Fin d → ℝ)} {PX : Measure (Fin d → ℝ)} {ν : Measure ℝ} {g : ℝ → ℝ → ℝ}
    {β : Fin K → Fin d → ℝ} {Rmax : ℝ} (t0 : ℝ) (X : ℕ → Ω → Fin d → ℝ) (R : ℕ → Ω → Fin K → ℝ)
    (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K) (hprim : IsPrimitives P 𝒳 PX ν g β Rmax X R V A)
    (U : Set (Fin d → ℝ)) (hU : MeasurableSet U) (k : Fin K) (j : ℕ) :
    Measurable (ind2 t0 V A X U k j) := by
  classical
  unfold ind2
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (hprim.coins.measurable_V (j + 1) (by omega) measurableSet_Iic).inter
    ((hprim.coins.measurable_A (j + 1) (by omega) (measurableSet_singleton k)).inter
      (hprim.measurable_X (j + 1) (by omega) hU))

lemma prob_explore {Ω : Type*} [MeasurableSpace Ω] {K : ℕ} (P : Measure Ω)
    (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K) (hVA : IsExplorationCoins P V A) (k : Fin K) (t : ℕ)
    (ht : 1 ≤ t) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    P (V t ⁻¹' Set.Iic c ∩ A t ⁻¹' {k}) = ENNReal.ofReal c * (K : ENNReal)⁻¹ := by
  rw [(hVA.indep_V_A t ht).measure_inter_preimage_eq_mul _ _
    measurableSet_Iic (measurableSet_singleton k)]
  congr 1
  · rw [← Measure.map_apply (hVA.measurable_V t ht) measurableSet_Iic,
      hVA.law_V t ht, Measure.restrict_apply measurableSet_Iic]
    have : Set.Iic c ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 c := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hc1⟩
    rw [this, Real.volume_Icc, sub_zero]
  · exact hVA.law_A t ht k

lemma integral_ind2 {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P]
    {𝒳 : Set (Fin d → ℝ)} {PX : Measure (Fin d → ℝ)} {ν : Measure ℝ} {g : ℝ → ℝ → ℝ}
    {β : Fin K → Fin d → ℝ} {Rmax : ℝ} (t0 : ℝ) (ht0 : 0 < t0) (X : ℕ → Ω → Fin d → ℝ)
    (R : ℕ → Ω → Fin K → ℝ)
    (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K) (hprim : IsPrimitives P 𝒳 PX ν g β Rmax X R V A)
    (U : Set (Fin d → ℝ)) (hU : MeasurableSet U) (k : Fin K) (j : ℕ) :
    ∫ ω, ind2 t0 V A X U k j ω ∂P =
      (PX U).toReal * (min 1 (t0 / ((j + 1 : ℕ) : ℝ)) / K) := by
  classical
  set c := min 1 (t0 / ((j + 1 : ℕ) : ℝ)) with hc
  have hc0 : 0 ≤ c := le_min zero_le_one (by positivity)
  have hc1 : c ≤ 1 := min_le_left _ _
  set S1 : Set ((Fin d → ℝ) × (Fin K → ℝ)) := Prod.fst ⁻¹' U with hS1
  set S2 : Set (ℝ × Fin K) := {q | q.1 ≤ c ∧ q.2 = k} with hS2
  have hS1m : MeasurableSet S1 := measurable_fst hU
  have hS2m : MeasurableSet S2 :=
    (measurable_fst measurableSet_Iic).inter (measurable_snd (measurableSet_singleton k))
  set E := (fun ω => (X (j + 1) ω, R (j + 1) ω)) ⁻¹' S1 ∩
    (fun ω => (V (j + 1) ω, A (j + 1) ω)) ⁻¹' S2 with hE
  have hXRm : Measurable (fun ω => (X (j + 1) ω, R (j + 1) ω)) :=
    (hprim.measurable_X (j + 1) (by omega)).prodMk (hprim.measurable_R (j + 1) (by omega))
  have hVAm : Measurable (fun ω => (V (j + 1) ω, A (j + 1) ω)) :=
    (hprim.coins.measurable_V (j + 1) (by omega)).prodMk
      (hprim.coins.measurable_A (j + 1) (by omega))
  have hmE : MeasurableSet E := (hXRm hS1m).inter (hVAm hS2m)
  have hmem : ∀ ω, ω ∈ E ↔ (V (j + 1) ω ≤ c ∧ A (j + 1) ω = k ∧ X (j + 1) ω ∈ U) := by
    intro ω
    simp only [hE, Set.mem_inter_iff, Set.mem_preimage, hS1, hS2, Set.mem_setOf_eq]
    tauto
  have hind : ind2 t0 V A X U k j = E.indicator 1 := by
    funext ω
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω]
      have := (hmem ω).mp hω
      simp only [ind2, Pi.one_apply]
      rw [if_pos this]
    · rw [Set.indicator_of_notMem hω]
      have : ¬ (V (j + 1) ω ≤ c ∧ A (j + 1) ω = k ∧ X (j + 1) ω ∈ U) := fun h => hω ((hmem ω).mpr h)
      simp only [ind2]
      rw [if_neg this]
  rw [hind, integral_indicator_one hmE]
  have hPE : P E = PX U * (ENNReal.ofReal c * (K : ENNReal)⁻¹) := by
    rw [hE, (hprim.indep_XR_VA (j + 1) (by omega)).measure_inter_preimage_eq_mul _ _ hS1m hS2m]
    congr 1
    · have : (fun ω => (X (j + 1) ω, R (j + 1) ω)) ⁻¹' S1 = X (j + 1) ⁻¹' U := by
        ext ω; simp [hS1]
      rw [this, ← Measure.map_apply (hprim.measurable_X (j + 1) (by omega)) hU,
        hprim.law_X (j + 1) (by omega)]
    · have : (fun ω => (V (j + 1) ω, A (j + 1) ω)) ⁻¹' S2 =
          V (j + 1) ⁻¹' Set.Iic c ∩ A (j + 1) ⁻¹' {k} := by
        ext ω; simp [hS2]
      rw [this, prob_explore P V A hprim.coins k (j + 1) (by omega) c hc0 hc1]
  rw [measureReal_def, hPE, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0,
    ENNReal.toReal_inv]
  simp [div_eq_mul_inv]


/-- Elementary consequences of `t₀ = 2C₀K`, `C₀ ≥ 10`, `T ≥ max{(t₀+1)²/e² − 1, e}`. -/
lemma numerics {K : ℕ} (hK : 2 ≤ K) (C0 t0 : ℝ) (hC0 : 10 ≤ C0) (ht0 : t0 = 2 * C0 * K) (T : ℕ)
    (hT : max ((t0 + 1) ^ 2 / Real.exp 1 ^ 2 - 1) (Real.exp 1) ≤ (T : ℝ)) :
    40 ≤ t0 ∧ t0 ≤ (T : ℝ) ∧ 1 ≤ Real.log ((T : ℝ) + 1) ∧
      Real.log (t0 + 1) ≤ 1 + Real.log ((T : ℝ) + 1) / 2 ∧ 1 ≤ Real.log t0 ∧
      Real.log (T : ℝ) ≤ Real.log ((T : ℝ) + 1) := by
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have ht0_40 : 40 ≤ t0 := by rw [ht0]; nlinarith
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have he2 : Real.exp 1 ^ 2 < 7.4 := by nlinarith
  have hT1 : (t0 + 1) ^ 2 / Real.exp 1 ^ 2 - 1 ≤ (T : ℝ) := (le_max_left _ _).trans hT
  have hT2 : Real.exp 1 ≤ (T : ℝ) := (le_max_right _ _).trans hT
  have hT' : (t0 + 1) ^ 2 ≤ ((T : ℝ) + 1) * Real.exp 1 ^ 2 := by
    rw [← div_le_iff₀ (by positivity)]; linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hTge : t0 ≤ (T : ℝ) := by
    have : ((T : ℝ) + 1) * Real.exp 1 ^ 2 ≤ ((T : ℝ) + 1) * 7.4 := by nlinarith
    nlinarith
  refine ⟨ht0_40, hTge, ?_, ?_, ?_, Real.log_le_log hTpos (by linarith)⟩
  · rw [Real.le_log_iff_exp_le (by positivity)]; linarith
  · have := Real.log_le_log (by positivity) hT'
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_exp] at this
    push_cast at this; linarith
  · rw [Real.le_log_iff_exp_le (by positivity)]; linarith

open GMCPChernoff GMCPHarm in
/-- The lower tail of `|𝒜|`: `ℙ(|𝒜| ≤ ¼ p* C₀ log(T+1)) ≤ 1/(T+1)`. -/
lemma lowerA {d K : ℕ} (hK : 2 ≤ K)
    (𝒳 : Set (Fin d → ℝ)) (PX : Measure (Fin d → ℝ)) (ν : Measure ℝ) (g : ℝ → ℝ → ℝ)
    (β : Fin K → Fin d → ℝ) (Rmax h pstar : ℝ) (Ko Ks : Finset (Fin K))
    (hglm : IsGLMFamily ν g Rmax) (hA3 : A3 𝒳 PX ν g β Ko Ks h pstar)
    (C0 t0 : ℝ) (hC0 : C0 = max 10 (16 / pstar)) (ht0 : t0 = 2 * C0 * K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin d → ℝ) (R : ℕ → Ω → Fin K → ℝ) (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K)
    (hprim : IsPrimitives P 𝒳 PX ν g β Rmax X R V A)
    (T : ℕ) (hT : max ((t0 + 1) ^ 2 / Real.exp 1 ^ 2 - 1) (Real.exp 1) ≤ (T : ℝ))
    (k : Fin K) (hk : k ∈ Ko) :
    P.real {ω | ∑ j ∈ Finset.range T,
        ind2 t0 V A X (optRegion 𝒳 ν g β h k) k j ω ≤
          1 / 4 * pstar * C0 * Real.log ((T : ℝ) + 1)} ≤ 1 / ((T : ℝ) + 1) := by
  classical
  obtain ⟨-, hpstar, -, -, -, hpU⟩ := hA3
  have hC10 : 10 ≤ C0 := by rw [hC0]; exact le_max_left _ _
  have hC16 : 16 ≤ pstar * C0 := by
    have : 16 / pstar ≤ C0 := by rw [hC0]; exact le_max_right _ _
    rw [div_le_iff₀ hpstar] at this; linarith
  obtain ⟨ht40, htT, hL1, hl1, -, -⟩ := numerics hK C0 t0 hC10 ht0 T hT
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have ht0pos : 0 < t0 := by linarith
  set U := optRegion 𝒳 ν g β h k with hUdef
  have hU : MeasurableSet U :=
    measurableSet_optRegion hglm hprim.measurableSet_domain β h k
  have : IsProbabilityMeasure PX := by
    rw [← hprim.law_X 1 le_rfl]
    exact Measure.isProbabilityMeasure_map (hprim.measurable_X 1 le_rfl).aemeasurable
  have hpU1 : pstar ≤ (PX U).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp (hpU k hk)
  have hpU2 : (PX U).toReal ≤ 1 := by
    have := prob_le_one (μ := PX) (s := U)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  set L := Real.log ((T : ℝ) + 1) with hL
  set l0 := Real.log t0
  set l1 := Real.log (t0 + 1)
  have hl0l1 : l0 ≤ l1 := Real.log_le_log ht0pos (by linarith)
  set Sφ := ∑ t ∈ Finset.Icc 1 T, min 1 (t0 / (t : ℝ)) with hSφ
  have hSlo : t0 * (1 + L - l0) - 1 ≤ Sφ := by
    have := G_le_sum ht0pos T
    rwa [G_of_ge ht0pos (by linarith), G_of_le (by linarith)] at this
  have hμ : ∑ j ∈ Finset.range T, ∫ ω, ind2 t0 V A X U k j ω ∂P = (PX U).toReal * (Sφ / K) := by
    simp_rw [integral_ind2 P t0 ht0pos X R V A hprim U hU k]
    rw [← Finset.mul_sum, ← Finset.sum_div, sum_range_eq_Icc (fun t => min 1 (t0 / (t : ℝ)))]
  have ht0K : t0 / K = 2 * C0 := by rw [ht0]; field_simp
  have hSK : C0 * L - 1 / 2 ≤ Sφ / K := by
    have h1 : t0 * (1 + L - l1) - 1 ≤ Sφ := by nlinarith
    have h2 : (t0 * (1 + L - l1) - 1) / K ≤ Sφ / K := div_le_div_of_nonneg_right h1 hKpos.le
    have h3 : (t0 * (1 + L - l1) - 1) / K = 2 * C0 * (1 + L - l1) - 1 / K := by
      rw [sub_div, mul_comm t0, mul_div_assoc, div_eq_mul_inv t0, ← div_eq_mul_inv, ht0K]; ring
    have hX : L / 2 ≤ 1 + L - l1 := by linarith
    have h4 : 2 * C0 * (L / 2) ≤ 2 * C0 * (1 + L - l1) :=
      mul_le_mul_of_nonneg_left hX (by linarith)
    have hK1 : 1 / (K : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hK2
    nlinarith
  have hSK0 : 0 ≤ Sφ / K := by
    have : 0 ≤ Sφ := Finset.sum_nonneg fun t _ => le_min zero_le_one (by positivity)
    positivity
  have hμlo : pstar * (C0 * L - 1 / 2) ≤ (PX U).toReal * (Sφ / K) :=
    mul_le_mul hpU1 hSK (by nlinarith) (by linarith)
  have hlo := chernoff_lower P (ind2 t0 V A X U k) (indep_ind2 P t0 X R V A hprim U hU k)
    (measurable_ind2 P t0 X R V A hprim U hU k) (ind2_01 t0 V A X U k) (Finset.range T)
    (Real.log 2) (Real.log_nonneg (by norm_num)) (1 / 4 * pstar * C0 * L)
  rw [hμ, Real.exp_neg, Real.exp_log (by norm_num)] at hlo
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hq : 16 * L ≤ pstar * C0 * L := mul_le_mul_of_nonneg_right hC16 (by linarith)
  have hp1 : pstar ≤ 1 := hpU1.trans hpU2
  have hexp : Real.log 2 * (1 / 4 * pstar * C0 * L) +
      (2⁻¹ - 1) * ((PX U).toReal * (Sφ / K)) ≤ -L := by
    have ha0 : 0 ≤ 1 / 4 * pstar * C0 * L := by nlinarith
    have h1 : Real.log 2 * (1 / 4 * pstar * C0 * L) ≤ 0.6931471808 * (1 / 4 * pstar * C0 * L) :=
      mul_le_mul_of_nonneg_right hlog2.le ha0
    have h2 : (2⁻¹ - 1 : ℝ) * ((PX U).toReal * (Sφ / K)) ≤ (2⁻¹ - 1) * (pstar * (C0 * L - 1 / 2)) :=
      mul_le_mul_of_nonpos_left hμlo (by norm_num)
    have e1 : pstar * (C0 * L - 1 / 2) = pstar * C0 * L - pstar / 2 := by ring
    have e2 : 0.6931471808 * (1 / 4 * pstar * C0 * L) = 0.1732867952 * (pstar * C0 * L) := by ring
    rw [e1] at h2
    linarith
  refine hlo.trans ((Real.exp_le_exp.mpr hexp).trans ?_)
  rw [Real.exp_neg, hL, Real.exp_log (by positivity), one_div]

theorem ec8_2_main {d K : ℕ} (hd : 1 ≤ d) (hK : 2 ≤ K)
    (𝒳 : Set (Fin d → ℝ)) (PX : Measure (Fin d → ℝ)) (ν : Measure ℝ) (g : ℝ → ℝ → ℝ)
    (β : Fin K → Fin d → ℝ) (Rmax h pstar : ℝ) (Ko Ks : Finset (Fin K))
    (hglm : IsGLMFamily ν g Rmax) (hA3 : A3 𝒳 PX ν g β Ko Ks h pstar)
    (C0 t0 : ℝ) (hC0 : C0 = max 10 (16 / pstar)) (ht0 : t0 = 2 * C0 * K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin d → ℝ) (R : ℕ → Ω → Fin K → ℝ) (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K)
    (hprim : IsPrimitives P 𝒳 PX ν g β Rmax X R V A)
    (T : ℕ) (hT : max ((t0 + 1) ^ 2 / Real.exp 1 ^ 2 - 1) (Real.exp 1) ≤ (T : ℝ))
    (k : Fin K) (hk : k ∈ Ko) :
    P {ω | ((randomSamplesIn t0 (fun s => V s ω) (fun s => A s ω) (fun s => X s ω)
              (optRegion 𝒳 ν g β h k) k T).card : ℝ) <
            1 / 4 * pstar * C0 * Real.log ((T : ℝ) + 1)} ≤
      ENNReal.ofReal (1 / ((T : ℝ) + 1)) := by
  have hb := lowerA hK 𝒳 PX ν g β Rmax h pstar Ko Ks hglm hA3 C0 t0 hC0 ht0 P X R V A hprim T hT
    k hk
  have hsub : {ω | ((randomSamplesIn t0 (fun s => V s ω) (fun s => A s ω) (fun s => X s ω)
              (optRegion 𝒳 ν g β h k) k T).card : ℝ) <
            1 / 4 * pstar * C0 * Real.log ((T : ℝ) + 1)} ⊆
      {ω | ∑ j ∈ Finset.range T, ind2 t0 V A X (optRegion 𝒳 ν g β h k) k j ω ≤
          1 / 4 * pstar * C0 * Real.log ((T : ℝ) + 1)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, card_randomSamplesIn] at hω ⊢
    exact hω.le
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hb

open GMCPChernoff GMCPHarm in
theorem ec8_3_main {d K : ℕ} (hd : 1 ≤ d) (hK : 2 ≤ K)
    (𝒳 : Set (Fin d → ℝ)) (PX : Measure (Fin d → ℝ)) (ν : Measure ℝ) (g : ℝ → ℝ → ℝ)
    (β : Fin K → Fin d → ℝ) (Rmax h pstar : ℝ) (Ko Ks : Finset (Fin K))
    (hglm : IsGLMFamily ν g Rmax) (hA3 : A3 𝒳 PX ν g β Ko Ks h pstar)
    (C0 t0 : ℝ) (hC0 : C0 = max 10 (16 / pstar)) (ht0 : t0 = 2 * C0 * K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin d → ℝ) (R : ℕ → Ω → Fin K → ℝ) (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K)
    (hprim : IsPrimitives P 𝒳 PX ν g β Rmax X R V A)
    (T : ℕ) (hT : max ((t0 + 1) ^ 2 / Real.exp 1 ^ 2 - 1) (Real.exp 1) ≤ (T : ℝ))
    (k : Fin K) (hk : k ∈ Ko) :
    P {ω | ((randomSamplesIn t0 (fun s => V s ω) (fun s => A s ω) (fun s => X s ω)
              (optRegion 𝒳 ν g β h k) k T).card : ℝ) <
            1 / 24 * pstar * ((randomSet t0 (fun s => V s ω) (fun s => A s ω) k T).card : ℝ)} ≤
      ENNReal.ofReal (3 / ((T : ℝ) + 1)) := by
  classical
  have hb := lowerA hK 𝒳 PX ν g β Rmax h pstar Ko Ks hglm hA3 C0 t0 hC0 ht0 P X R V A hprim T hT
    k hk
  have hpstar : 0 < pstar := hA3.2.1
  have hC10 : 10 ≤ C0 := by rw [hC0]; exact le_max_left _ _
  obtain ⟨ht40, htT, hL1, -, hl01, huL⟩ := numerics hK C0 t0 hC10 ht0 T hT
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have ht0pos : 0 < t0 := by linarith
  set L := Real.log ((T : ℝ) + 1) with hL
  set u := Real.log (T : ℝ)
  set l0 := Real.log t0
  -- upper tail of n
  set Sφ := ∑ t ∈ Finset.Icc 1 T, min 1 (t0 / (t : ℝ)) with hSφ
  have hSup : Sφ ≤ t0 * (1 + u - l0) := by
    have := sum_le_G ht0pos T
    rwa [G_of_ge ht0pos htT] at this
  have hμ : ∑ j ∈ Finset.range T, ∫ ω, ind t0 V A k j ω ∂P = Sφ / K := by
    simp_rw [integral_ind P t0 ht0pos V A hprim.coins k]
    rw [← Finset.sum_div, sum_range_eq_Icc (fun t => min 1 (t0 / (t : ℝ)))]
  have ht0K : t0 / K = 2 * C0 := by rw [ht0]; field_simp
  have hμup : Sφ / K ≤ 2 * C0 * L := by
    have h2 : Sφ / K ≤ t0 * (1 + u - l0) / K := div_le_div_of_nonneg_right hSup hKpos.le
    have h3 : t0 * (1 + u - l0) / K = 2 * C0 * (1 + u - l0) := by
      rw [mul_comm t0, mul_div_assoc, ht0K]; ring
    have h4 : 2 * C0 * (1 + u - l0) ≤ 2 * C0 * L :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hup := chernoff_upper P (ind t0 V A k) (indep_ind P t0 V A hprim.coins k)
    (measurable_ind P t0 V A hprim.coins k) (ind_01 t0 V A k) (Finset.range T) (Real.log 3)
    (Real.log_nonneg (by norm_num)) (6 * C0 * L)
  rw [hμ, Real.exp_log (by norm_num)] at hup
  have hlog3 : 0.6931471803 < Real.log 3 :=
    Real.log_two_gt_d9.trans_le (Real.log_le_log (by norm_num) (by norm_num))
  have hexp : -Real.log 3 * (6 * C0 * L) + (3 - 1) * (Sφ / K) ≤ -L := by
    have hCL : 10 * L ≤ C0 * L := mul_le_mul_of_nonneg_right hC10 (by linarith)
    have h1 : 0.6931471803 * (6 * C0 * L) ≤ Real.log 3 * (6 * C0 * L) :=
      mul_le_mul_of_nonneg_right hlog3.le (by nlinarith)
    have e1 : -Real.log 3 * (6 * C0 * L) = -(Real.log 3 * (6 * C0 * L)) := by ring
    have e2 : 0.6931471803 * (6 * C0 * L) = 4.1588830818 * (C0 * L) := by ring
    have e3 : 2 * C0 * L = 2 * (C0 * L) := by ring
    rw [e1]; rw [e3] at hμup
    linarith
  have hPup : P.real {ω | 6 * C0 * L ≤ ∑ j ∈ Finset.range T, ind t0 V A k j ω} ≤
      1 / ((T : ℝ) + 1) := by
    refine hup.trans ((Real.exp_le_exp.mpr hexp).trans ?_)
    rw [Real.exp_neg, hL, Real.exp_log (by positivity), one_div]
  -- inclusion
  have hsub : {ω | ((randomSamplesIn t0 (fun s => V s ω) (fun s => A s ω) (fun s => X s ω)
              (optRegion 𝒳 ν g β h k) k T).card : ℝ) <
            1 / 24 * pstar * ((randomSet t0 (fun s => V s ω) (fun s => A s ω) k T).card : ℝ)} ⊆
      {ω | ∑ j ∈ Finset.range T, ind2 t0 V A X (optRegion 𝒳 ν g β h k) k j ω ≤
          1 / 4 * pstar * C0 * L} ∪
      {ω | 6 * C0 * L ≤ ∑ j ∈ Finset.range T, ind t0 V A k j ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, card_randomSamplesIn, card_randomSet] at hω
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    have : 1 / 24 * pstar * ∑ j ∈ Finset.range T, ind t0 V A k j ω ≤
        1 / 24 * pstar * (6 * C0 * L) :=
      mul_le_mul_of_nonneg_left h2.le (by positivity)
    have e : 1 / 24 * pstar * (6 * C0 * L) = 1 / 4 * pstar * C0 * L := by ring
    linarith
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [← ofReal_measureReal, ← ofReal_measureReal, ← ENNReal.ofReal_add measureReal_nonneg
    measureReal_nonneg]
  apply ENNReal.ofReal_le_ofReal
  have : (3 : ℝ) / ((T : ℝ) + 1) = 1 / ((T : ℝ) + 1) + 2 / ((T : ℝ) + 1) := by ring
  have h2 : 1 / ((T : ℝ) + 1) ≤ 2 / ((T : ℝ) + 1) :=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  linarith

end GMCPEC8

open GMCPBandit.Regret in
theorem solution {d K : ℕ} (hd : 1 ≤ d) (hK : 2 ≤ K)
    (𝒳 : Set (Fin d → ℝ)) (PX : Measure (Fin d → ℝ)) (ν : Measure ℝ) (g : ℝ → ℝ → ℝ)
    (β : Fin K → Fin d → ℝ) (Rmax h pstar : ℝ) (Ko Ks : Finset (Fin K))
    (hglm : IsGLMFamily ν g Rmax) (hA3 : A3 𝒳 PX ν g β Ko Ks h pstar)
    (C0 t0 : ℝ) (hC0 : C0 = max 10 (16 / pstar)) (ht0 : t0 = 2 * C0 * K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin d → ℝ) (R : ℕ → Ω → Fin K → ℝ) (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K)
    (hprim : IsPrimitives P 𝒳 PX ν g β Rmax X R V A)
    (T : ℕ) (hT : max ((t0 + 1) ^ 2 / Real.exp 1 ^ 2 - 1) (Real.exp 1) ≤ (T : ℝ))
    (k : Fin K) (hk : k ∈ Ko) :
    P {ω | ((randomSamplesIn t0 (fun s => V s ω) (fun s => A s ω) (fun s => X s ω)
              (optRegion 𝒳 ν g β h k) k T).card : ℝ) <
            1 / 24 * pstar * ((randomSet t0 (fun s => V s ω) (fun s => A s ω) k T).card : ℝ)} ≤
      ENNReal.ofReal (3 / ((T : ℝ) + 1)) :=
  GMCPEC8.ec8_3_main hd hK 𝒳 PX ν g β Rmax h pstar Ko Ks hglm hA3 C0 t0 hC0 ht0 P X R V A hprim
    T hT k hk
