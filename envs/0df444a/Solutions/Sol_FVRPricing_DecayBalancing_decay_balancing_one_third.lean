-- Prove2me | solution 1 for FVRPricing.DecayBalancing.decay_balancing_one_third
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T22:51:55.220774+00:00
-- url     : https://prove2.me/submissions/22719e8b-f2e0-49cd-917d-a051d17f5b8e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_Policies
import Theorems.Thm_FVRPricing_DecayBalancing_decay_balancing_one_third_normalized

open MeasureTheory ProbabilityTheory FVRPricing.DecayBalancing

lemma fvr10_expDensity_eq (r : ℝ) (hr : 0 < r) (s : ℝ) :
    expDensity r s = r⁻¹ * expDensity 1 (r⁻¹ * s) := by
  unfold expDensity
  have h : (0 ≤ r⁻¹ * s ↔ 0 ≤ s) := by
    constructor
    · intro h; exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hr)).mp h
    · intro h; exact mul_nonneg (inv_pos.mpr hr).le h
  by_cases hs : 0 ≤ s
  · rw [if_pos hs, if_pos (h.mpr hs)]
    congr 2
    field_simp
  · rw [if_neg hs, if_neg (fun h' => hs (h.mp h'))]
    simp

lemma fvr10_Fbar_eq (r : ℝ) (hr : 0 < r) (p : ℝ) :
    Fbar (expDensity r) p = Fbar (expDensity 1) ((1 / r) * p) := by
  unfold Fbar
  have : (fun s => expDensity r s) = fun s => r⁻¹ * expDensity 1 (r⁻¹ * s) := by
    funext s; exact fvr10_expDensity_eq r hr s
  rw [this, integral_const_mul, integral_comp_mul_left_Ioi (fun t => expDensity 1 t) p
    (inv_pos.mpr hr), smul_eq_mul, ← mul_assoc, inv_inv, inv_mul_cancel₀ hr.ne', one_mul,
    one_div]

lemma fvr10_pathRevenue (r α : ℝ) (hr : 0 < r) (π : ℕ → ℝ → ℝ → ℝ) (x : ℕ) (a b lam : ℝ)
    (e : Fin x → ℝ) :
    pathRevenue (expDensity r) α π π x a b lam e =
      ENNReal.ofReal r * pathRevenue (expDensity 1) α (fun x a b => (1 / r) * π x a b)
        (fun x a b => (1 / r) * π x a b) x a b lam e := by
  have hsd : ∀ k, saleTime (expDensity r) π x a b lam e k =
      saleTime (expDensity 1) (fun x a b => (1 / r) * π x a b) x a b lam e k := by
    intro k
    unfold saleTime stageDuration
    simp_rw [fvr10_Fbar_eq r hr]
  unfold pathRevenue
  split_ifs with hl
  · simp
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hsd, mul_left_comm, ← ENNReal.ofReal_mul hr.le]
    congr 3
    field_simp

lemma fvr10_Jpi (r α : ℝ) (hr : 0 < r) (π : ℕ → ℝ → ℝ → ℝ) (x : ℕ) (a b : ℝ) :
    Jpi (expDensity r) α π x a b =
      ENNReal.ofReal r * Jpi (expDensity 1) α (fun x a b => (1 / r) * π x a b) x a b := by
  unfold Jpi
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun lam => ?_)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun e => ?_)
  exact fvr10_pathRevenue r α hr π x a b lam e

lemma fvr5_subst (c : ℝ) (hc : 0 < c) (G : ℝ → ENNReal) :
    ∫⁻ y, G y = ENNReal.ofReal c * ∫⁻ t, G (c * t) := by
  have h1 : ∫⁻ t, G (c * t) = ∫⁻ y, G y ∂(Measure.map (c * ·) volume) := by
    have := lintegral_map_equiv (μ := (volume : Measure ℝ)) G (MeasurableEquiv.mulLeft₀ c hc.ne')
    rw [MeasurableEquiv.coe_mulLeft₀] at this
    exact this.symm
  rw [h1, Real.map_volume_mul_left hc.ne', lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    abs_of_pos (inv_pos.mpr hc), ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne',
    ENNReal.ofReal_one, one_mul]

lemma fvr5_subst_Ioc (c : ℝ) (hc : 0 < c) (u v : ℝ) (H : ℝ → ENNReal) :
    ∫⁻ β in Set.Ioc (c * u) (c * v), H β = ENNReal.ofReal c * ∫⁻ t in Set.Ioc u v, H (c * t) := by
  rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc,
    fvr5_subst c hc]
  congr 1
  refine lintegral_congr (fun t => ?_)
  have hmem : c * t ∈ Set.Ioc (c * u) (c * v) ↔ t ∈ Set.Ioc u v := by
    simp only [Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(mul_lt_mul_iff_right₀ hc).mp h1, (mul_le_mul_iff_right₀ hc).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(mul_lt_mul_iff_right₀ hc).mpr h1, (mul_le_mul_iff_right₀ hc).mpr h2⟩
  by_cases ht : t ∈ Set.Ioc u v
  · rw [Set.indicator_of_mem (hmem.mpr ht), Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem (fun h => ht (hmem.mp h)), Set.indicator_of_notMem ht]

lemma fvr5_bClock (α b μ : ℝ) (hα : 0 < α) (hμ : 0 < μ) {x : ℕ} (e : Fin x → ℝ) (j : ℕ) :
    bClock (α * b) μ e j = α * bClock b (α * μ) e j := by
  unfold bClock
  field_simp

lemma fvr5_pathRevenue (f : ℝ → ℝ) (α : ℝ) (hα : 0 < α) (π : ℕ → ℝ → ℝ → ℝ) (x : ℕ)
    (a b μ : ℝ) (e : Fin x → ℝ) :
    pathRevenue f α π π x a b (α * μ) e =
      pathRevenue f 1 (fun x a b => π x a (b / α)) (fun x a b => π x a (b / α)) x a (α * b) μ e := by
  unfold pathRevenue
  by_cases hμ : μ ≤ 0
  · rw [if_pos hμ, if_pos (mul_nonpos_of_nonneg_of_nonpos hα.le hμ)]
  push Not at hμ
  rw [if_neg (not_le.mpr (mul_pos hα hμ)), if_neg (not_le.mpr hμ)]
  have hsd : ∀ j, stageDuration f (fun x a b => π x a (b / α)) x a (α * b) μ e j =
      ENNReal.ofReal α * stageDuration f π x a b (α * μ) e j := by
    intro j
    unfold stageDuration
    rw [fvr5_bClock α b μ hα hμ, fvr5_bClock α b μ hα hμ, fvr5_subst_Ioc α hα]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    simp only [mul_div_cancel_left₀ _ hα.ne']
  have hst : ∀ k, saleTime f (fun x a b => π x a (b / α)) x a (α * b) μ e k =
      ENNReal.ofReal α * saleTime f π x a b (α * μ) e k := by
    intro k
    unfold saleTime
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => hsd j)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hst, fvr5_bClock α b μ hα hμ]
  simp only [mul_div_cancel_left₀ _ hα.ne']
  congr 1
  unfold disc
  set T := saleTime f π x a b (α * μ) e ((j : ℕ) + 1)
  by_cases hT : T = ⊤
  · rw [if_pos hT, if_pos (by rw [hT]; exact ENNReal.mul_top (by simpa using hα))]
  · have hT' : ENNReal.ofReal α * T ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT
    rw [if_neg hT, if_neg hT', ENNReal.toReal_mul, ENNReal.toReal_ofReal hα.le, one_mul]

-- PART2
/-! ### Scaling in `r` -/

lemma red_JpiKnown_r (r α lam : ℝ) (hr : 0 < r) (σ : ℕ → ℝ) (x : ℕ) :
    JpiKnown (expDensity r) α lam σ x =
      ENNReal.ofReal r * JpiKnown (expDensity 1) α lam (fun n => (1 / r) * σ n) x := by
  unfold JpiKnown
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun e => ?_)
  exact fvr10_pathRevenue r α hr (fun n _ _ => σ n) x 0 0 lam e

lemma red_JstarKnown_r (r α lam : ℝ) (hr : 0 < r) (x : ℕ) :
    JstarKnown (expDensity r) α lam x = ENNReal.ofReal r * JstarKnown (expDensity 1) α lam x := by
  unfold JstarKnown
  simp_rw [red_JpiKnown_r r α lam hr _ x]
  rw [ENNReal.mul_iSup]
  apply le_antisymm
  · refine iSup₂_le (fun σ hσ => ?_)
    have hσ' : ∀ n, 0 ≤ (1 / r) * σ n := fun n => mul_nonneg (by positivity) (hσ n)
    rw [← ENNReal.mul_iSup]
    gcongr
    exact le_iSup₂ (f := fun (σ : ℕ → ℝ) (_ : ∀ n, 0 ≤ σ n) => JpiKnown (expDensity 1) α lam σ x)
      _ hσ'
  · refine iSup_le (fun σ => ?_)
    rw [ENNReal.mul_iSup]
    refine iSup_le (fun hσ => ?_)
    have hσ' : ∀ n, 0 ≤ r * σ n := fun n => mul_nonneg hr.le (hσ n)
    have := le_iSup₂ (f := fun (σ : ℕ → ℝ) (_ : ∀ n, 0 ≤ σ n) =>
      ENNReal.ofReal r * JpiKnown (expDensity 1) α lam (fun n => (1 / r) * σ n) x) _ hσ'
    have heq : (fun n => (1 / r) * (r * σ n)) = σ := by funext n; field_simp
    rw [heq] at this
    exact this

lemma red_Jtilde_r (r α : ℝ) (hr : 0 < r) (x : ℕ) (a b : ℝ) :
    Jtilde (expDensity r) α x a b = ENNReal.ofReal r * Jtilde (expDensity 1) α x a b := by
  unfold Jtilde
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_congr (fun lam => red_JstarKnown_r r α lam hr x)

lemma red_Q_r (r : ℝ) (hr : 0 < r) (p : ℝ) :
    Fbar (expDensity r) p / hazard (expDensity r) p =
      r * (Fbar (expDensity 1) ((1 / r) * p) / hazard (expDensity 1) ((1 / r) * p)) := by
  unfold hazard
  rw [fvr10_Fbar_eq r hr p, fvr10_expDensity_eq r hr p, ← one_div, div_div_eq_mul_div,
    div_div_eq_mul_div]
  ring_nf
  rw [inv_inv]; ring

lemma red_balance_r (r α V μ : ℝ) (hr : 0 < r) :
    balancePrice (expDensity r) α (r * V) μ = r * balancePrice (expDensity 1) α V μ := by
  unfold balancePrice
  conv_rhs => rw [← smul_eq_mul, ← Real.sInf_smul_of_nonneg hr.le]
  congr 1
  ext p
  rw [Set.mem_smul_set]
  simp only [Set.mem_ofPred_eq, smul_eq_mul]
  constructor
  · rintro ⟨hp, heq⟩
    refine ⟨(1 / r) * p, ⟨mul_nonneg (by positivity) hp, ?_⟩, by field_simp⟩
    rw [red_Q_r r hr p] at heq
    have : r * ((Fbar (expDensity 1) (1 / r * p) / hazard (expDensity 1) (1 / r * p)) * μ) =
        r * (α * V) := by linarith
    exact mul_left_cancel₀ hr.ne' this
  · rintro ⟨q, ⟨hq, heq⟩, rfl⟩
    refine ⟨mul_nonneg hr.le hq, ?_⟩
    rw [red_Q_r r hr]
    have : 1 / r * (r * q) = q := by field_simp
    rw [this, mul_assoc, heq]; ring

lemma red_πdb_r (r α : ℝ) (hr : 0 < r) :
    πdb (expDensity r) α = fun x a b => r * πdb (expDensity 1) α x a b := by
  funext x a b
  unfold πdb
  rw [red_Jtilde_r r α hr, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr.le, red_balance_r _ _ _ _ hr]

lemma red_Jstar_r (r α : ℝ) (hr : 0 < r) (x : ℕ) (a b : ℝ) :
    Jstar (expDensity r) α x a b = ENNReal.ofReal r * Jstar (expDensity 1) α x a b := by
  unfold Jstar
  have key : (⨆ (π : ℕ → ℝ → ℝ → ℝ) (_ : IsPolicy π),
      Jpi (expDensity 1) α (fun x a b => (1 / r) * π x a b) x a b) =
      ⨆ (π : ℕ → ℝ → ℝ → ℝ) (_ : IsPolicy π), Jpi (expDensity 1) α π x a b := by
    apply le_antisymm
    · refine iSup₂_le (fun σ hσ => ?_)
      have hσ' : IsPolicy (fun x a b => (1 / r) * σ x a b) := by
        refine ⟨fun n => ((hσ.1 n).const_mul _), fun n a b => ?_⟩
        exact mul_nonneg (by positivity) (hσ.2 n a b)
      exact le_iSup₂ (f := fun (π : ℕ → ℝ → ℝ → ℝ) (_ : IsPolicy π) =>
        Jpi (expDensity 1) α π x a b) _ hσ'
    · refine iSup₂_le (fun σ hσ => ?_)
      have hσ' : IsPolicy (fun x a b => r * σ x a b) := by
        refine ⟨fun n => ((hσ.1 n).const_mul _), fun n a b => ?_⟩
        exact mul_nonneg hr.le (hσ.2 n a b)
      have := le_iSup₂ (f := fun (π : ℕ → ℝ → ℝ → ℝ) (_ : IsPolicy π) =>
        Jpi (expDensity 1) α (fun x a b => (1 / r) * π x a b) x a b) _ hσ'
      have heq : (fun x a b => (1 / r) * (r * σ x a b)) = σ := by
        funext x a b; field_simp
      rw [heq] at this
      exact this
  rw [← key, ENNReal.mul_iSup]
  refine iSup_congr (fun σ => ?_)
  rw [ENNReal.mul_iSup]
  exact iSup_congr (fun _ => fvr10_Jpi r α hr σ x a b)

lemma red_Jpi_πdb_r (r α : ℝ) (hr : 0 < r) (x : ℕ) (a b : ℝ) :
    Jpi (expDensity r) α (πdb (expDensity r) α) x a b =
      ENNReal.ofReal r * Jpi (expDensity 1) α (πdb (expDensity 1) α) x a b := by
  rw [fvr10_Jpi r α hr]
  congr 2
  rw [red_πdb_r r α hr]
  funext x a b
  field_simp

/-! ### Scaling in `α` -/

lemma red_mul_rpow (α b s : ℝ) (hα : 0 < α) : (α * b) ^ s = α ^ s * b ^ s := by
  rcases le_or_gt 0 b with hb | hb
  · exact Real.mul_rpow hα.le hb
  · have hab : α * b < 0 := mul_neg_of_pos_of_neg hα hb
    rw [Real.rpow_def_of_neg hab, Real.rpow_def_of_neg hb, Real.rpow_def_of_pos hα,
      Real.log_mul hα.ne' hb.ne, add_mul, Real.exp_add]
    ring

lemma red_gammaPDF (α a b μ : ℝ) (hα : 0 < α) :
    ENNReal.ofReal α * gammaPDF a b (α * μ) = gammaPDF a (α * b) μ := by
  by_cases hμ : μ < 0
  · rw [gammaPDF_of_neg hμ, gammaPDF_of_neg (mul_neg_of_pos_of_neg hα hμ), mul_zero]
  push Not at hμ
  rw [gammaPDF_of_nonneg hμ, gammaPDF_of_nonneg (mul_nonneg hα.le hμ), ← ENNReal.ofReal_mul hα.le]
  congr 1
  rw [Real.mul_rpow hα.le hμ, red_mul_rpow α b a hα, Real.rpow_sub_one hα.ne']
  have : -(b * (α * μ)) = -(α * b * μ) := by ring
  rw [this]
  field_simp

lemma red_gamma_subst (α : ℝ) (hα : 0 < α) (a b : ℝ) (g : ℝ → ENNReal) :
    ∫⁻ lam, g lam ∂(gammaMeasure a b) = ∫⁻ μ, g (α * μ) ∂(gammaMeasure a (α * b)) := by
  unfold gammaMeasure
  have hm : ∀ c d : ℝ, Measurable (gammaPDF c d) := fun c d =>
    (measurable_gammaPDFReal c d).ennreal_ofReal
  have hfin : ∀ c d : ℝ, ∀ᵐ y ∂(volume : Measure ℝ), gammaPDF c d y < ⊤ := fun c d =>
    Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top)
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (hm a b) (hfin a b),
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ (hm a (α * b)) (hfin a (α * b)),
    fvr5_subst α hα, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun μ => ?_)
  simp only [Pi.mul_apply]
  rw [← mul_assoc, red_gammaPDF α a b μ hα]

lemma red_Jpi_α (f : ℝ → ℝ) (α : ℝ) (hα : 0 < α) (π : ℕ → ℝ → ℝ → ℝ) (x : ℕ) (a b : ℝ) :
    Jpi f α π x a b = Jpi f 1 (fun x a b => π x a (b / α)) x a (α * b) := by
  unfold Jpi
  rw [red_gamma_subst α hα a b]
  refine lintegral_congr (fun μ => ?_)
  refine lintegral_congr (fun e => ?_)
  exact fvr5_pathRevenue f α hα π x a b μ e

lemma red_JstarKnown_α (f : ℝ → ℝ) (α : ℝ) (hα : 0 < α) (μ : ℝ) (x : ℕ) :
    JstarKnown f α (α * μ) x = JstarKnown f 1 μ x := by
  unfold JstarKnown JpiKnown
  refine iSup_congr (fun σ => iSup_congr (fun _ => lintegral_congr (fun e => ?_)))
  have := fvr5_pathRevenue f α hα (fun n _ _ => σ n) x 0 0 μ e
  rw [mul_zero] at this
  exact this

lemma red_Jtilde_α (f : ℝ → ℝ) (α : ℝ) (hα : 0 < α) (x : ℕ) (a b : ℝ) :
    Jtilde f α x a b = Jtilde f 1 x a (α * b) := by
  unfold Jtilde
  rw [red_gamma_subst α hα a b]
  exact lintegral_congr (fun μ => red_JstarKnown_α f α hα μ x)

lemma red_πdb_α (f : ℝ → ℝ) (α : ℝ) (hα : 0 < α) (x : ℕ) (a b : ℝ) :
    πdb f α x a b = πdb f 1 x a (α * b) := by
  unfold πdb balancePrice
  rw [red_Jtilde_α f α hα]
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, one_mul]
  refine and_congr_right (fun _ => ?_)
  rw [div_mul_eq_div_div_swap]
  have : ∀ Q V : ℝ, (Q * (a / b) = α * V ↔ Q * (a / b / α) = V) := by
    intro Q V
    rw [show Q * (a / b / α) = Q * (a / b) / α by ring, div_eq_iff hα.ne']
    constructor <;> intro h <;> linarith
  exact this _ _

lemma red_Jpi_πdb_α (f : ℝ → ℝ) (α : ℝ) (hα : 0 < α) (x : ℕ) (a b : ℝ) :
    Jpi f α (πdb f α) x a b = Jpi f 1 (πdb f 1) x a (α * b) := by
  rw [red_Jpi_α f α hα]
  congr 1
  funext x a b
  rw [red_πdb_α f α hα, mul_div_cancel₀ _ hα.ne']

lemma red_Jstar_α (f : ℝ → ℝ) (α : ℝ) (hα : 0 < α) (x : ℕ) (a b : ℝ) :
    Jstar f α x a b = Jstar f 1 x a (α * b) := by
  unfold Jstar
  simp_rw [red_Jpi_α f α hα _ x a b]
  apply le_antisymm
  · refine iSup₂_le (fun σ hσ => ?_)
    have hσ' : IsPolicy (fun x a b => σ x a (b / α)) := by
      refine ⟨fun n => ?_, fun n a b => hσ.2 n a _⟩
      exact (hσ.1 n).comp (measurable_fst.prodMk (measurable_snd.div_const α))
    exact le_iSup₂ (f := fun (π : ℕ → ℝ → ℝ → ℝ) (_ : IsPolicy π) =>
      Jpi f 1 π x a (α * b)) _ hσ'
  · refine iSup₂_le (fun σ hσ => ?_)
    have hσ' : IsPolicy (fun x a b => σ x a (α * b)) := by
      refine ⟨fun n => ?_, fun n a b => hσ.2 n a _⟩
      exact (hσ.1 n).comp (measurable_fst.prodMk (measurable_snd.const_mul α))
    have := le_iSup₂ (f := fun (π : ℕ → ℝ → ℝ → ℝ) (_ : IsPolicy π) =>
      Jpi f 1 (fun x a b => π x a (b / α)) x a (α * b)) _ hσ'
    have heq : (fun x a b => σ x a (α * (b / α))) = σ := by
      funext x a b; rw [mul_div_cancel₀ _ hα.ne']
    rw [heq] at this
    exact this

theorem solution (r α : ℝ) (hr : 0 < r) (hα : 0 < α)
    (x : ℕ) (hx : 1 < x) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Jstar (expDensity r) α x a b ≠ ⊤ ∧
    Jstar (expDensity r) α x a b ≤ 3 * Jpi (expDensity r) α (πdb (expDensity r) α) x a b := by
  have he : 0 < Real.exp (-1) := Real.exp_pos _
  have hb' : 0 < α * b / Real.exp (-1) := div_pos (mul_pos hα hb) he
  obtain ⟨h1, h2⟩ := decay_balancing_one_third_normalized x hx a (α * b / Real.exp (-1)) ha hb'
  rw [red_Jstar_α _ _ he, mul_div_cancel₀ _ he.ne'] at h1
  rw [red_Jstar_α _ _ he, red_Jpi_πdb_α _ _ he, mul_div_cancel₀ _ he.ne'] at h2
  rw [red_Jstar_r r α hr, red_Jpi_πdb_r r α hr, red_Jstar_α _ α hα, red_Jpi_πdb_α _ α hα]
  refine ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top h1, ?_⟩
  rw [mul_left_comm]
  exact mul_le_mul_right h2 _
