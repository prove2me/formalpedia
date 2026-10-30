-- Prove2me | solution 1 for BudgetMgmt.Profit.theorem_4_2_part_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T21:06:53.697824+00:00
-- url     : https://prove2.me/submissions/c699f124-9eed-4cd6-aba4-83fb327aefc2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BudgetMgmt_Profit_Model
import Theorems.Thm_BudgetMgmt_Profit_proposition_4_1_TS
import Theorems.Thm_BudgetMgmt_Profit_proposition_4_1_R
import Theorems.Thm_BudgetMgmt_Profit_lemma_B_2
import Theorems.Thm_BudgetMgmt_Profit_lemma_B_3
import Theorems.Thm_BudgetMgmt_Profit_items_sold_shading_identity
import Theorems.Thm_BudgetMgmt_Profit_expend_sym
import Theorems.Thm_BudgetMgmt_Profit_G1_reserve_c_le_lower_end

open BudgetMgmt.Profit MeasureTheory

/-- the price/threshold term of bid shading at `μ = 0` equals that of thresholding at `τ = c`. -/
theorem solution_aux_maxeq {n : ℕ} (c : ℝ) (hc : 0 < c) (x : Fin n → ℝ) (i : Fin n) :
    max (compShaded (sym 0) x i) c = max (compQual (sym c) x i) c := by
  have key : ∀ y : ℝ, max (compShaded (sym 0) x i) c ≤ y ↔ max (compQual (sym c) x i) c ≤ y := by
    intro y
    unfold compShaded compQual
    rw [max_le_iff, max_le_iff, Finset.fold_max_le, Finset.fold_max_le]
    constructor
    · rintro ⟨⟨h0, h⟩, hcy⟩
      refine ⟨⟨h0, fun j hj => ?_⟩, hcy⟩
      rw [Finset.mem_filter] at hj
      have := h j (Finset.mem_filter.mpr ⟨hj.1, hj.2.1⟩)
      simpa [sym] using this
    · rintro ⟨⟨h0, h⟩, hcy⟩
      refine ⟨⟨h0, fun j hj => ?_⟩, hcy⟩
      rw [Finset.mem_filter] at hj
      simp only [sym, add_zero, div_one]
      by_cases hj' : c ≤ x j
      · exact h j (Finset.mem_filter.mpr ⟨hj.1, hj.2, hj'⟩)
      · linarith [not_le.mp hj']
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

open Classical in
theorem solution_aux_alloc {n : ℕ} (c : ℝ) (hc : 0 < c) (x : Fin n → ℝ) (i : Fin n) :
    alloc c .shading (sym 0) x i = alloc c .thresholding (sym c) x i := by
  have hw : ∀ j, wins c .shading (sym 0) x j ↔ wins c .thresholding (sym c) x j := by
    intro j
    change max (compShaded (sym 0) x j) c ≤ x j / (1 + sym (n := n) 0 j) ↔
      max (compQual (sym c) x j) (sym (n := n) c j) ≤ x j
    have h1 : x j / (1 + sym (n := n) 0 j) = x j := by simp [sym]
    have h2 : max (compQual (sym c) x j) (sym (n := n) c j) = max (compQual (sym c) x j) c := rfl
    rw [h1, h2, solution_aux_maxeq c hc x j]
  have hc' : (wins c .shading (sym 0) x i ∧ ∀ j, j < i → ¬ wins c .shading (sym 0) x j) ↔
      (wins c .thresholding (sym c) x i ∧ ∀ j, j < i → ¬ wins c .thresholding (sym c) x j) := by
    simp only [hw]
  unfold alloc
  exact if_congr hc' rfl rfl

theorem solution_aux_payment {n : ℕ} (c : ℝ) (hc : 0 < c) (x : Fin n → ℝ) (i : Fin n) :
    payment c .shading (sym 0) x i = payment c .thresholding (sym c) x i := by
  unfold payment
  rw [solution_aux_alloc c hc x i]
  simp only [price]
  rw [solution_aux_maxeq c hc x i]

theorem solution_aux_reserve_c {n : ℕ} (P : SymInstance n) [NeZero n] :
    G1 P .reserve P.c = G1 P .thresholding P.c := rfl

theorem solution_aux_G1_S0 {n : ℕ} (P : SymInstance n) [NeZero n] :
    G1 P .shading 0 = G1 P .thresholding P.c := by
  unfold G1 expend
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    solution_aux_payment P.c P.c_pos x 0)

theorem solution_aux_profit_S0 {n : ℕ} (P : SymInstance n) :
    profit P .shading (sym 0) = profit P .thresholding (sym P.c) := by
  unfold profit expend itemsSold
  have hp : ∀ i, (∫ x, payment P.c .shading (sym 0) x i ∂P.law) =
      ∫ x, payment P.c .thresholding (sym P.c) x i ∂P.law := fun i =>
    integral_congr_ae (Filter.Eventually.of_forall fun x => solution_aux_payment P.c P.c_pos x i)
  have ha : ∀ i, (∫ x, alloc P.c .shading (sym 0) x i ∂P.law) =
      ∫ x, alloc P.c .thresholding (sym P.c) x i ∂P.law := fun i =>
    integral_congr_ae (Filter.Eventually.of_forall fun x => solution_aux_alloc P.c P.c_pos x i)
  simp only [hp, ha]

theorem solution_aux_profit_eq {n : ℕ} [NeZero n] (P : SymInstance n) (m : Mech) (s : ℝ) :
    profit P m (sym s) = n * G1 P m s - P.c * itemsSold P m (sym s) := by
  unfold profit
  simp only [expend_sym, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem solution_aux_finite {n : ℕ} (P : SymInstance n) : IsFiniteMeasure P.law := by
  have hint : Integrable P.f := by
    by_contra h
    have := integral_undef h
    rw [P.f_integral] at this
    exact one_ne_zero this
  refine ⟨?_⟩
  unfold SymInstance.law
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall P.f_nonneg),
    P.f_integral]
  exact ENNReal.ofReal_lt_top

theorem solution_aux_cdf_mono {n : ℕ} (P : SymInstance n) (a b : ℝ) (hab : a ≤ b) :
    cdf P (sym a) ≤ cdf P (sym b) := by
  have := solution_aux_finite P
  unfold cdf
  apply measureReal_mono _ (measure_ne_top _ _)
  intro x hx j
  exact (hx j).trans hab

theorem solution {n : ℕ} [NeZero n] (P : SymInstance n) (taubar mubar : ℝ)
    (hT : AdmissibleT P taubar) (hS : AdmissibleS P mubar) :
    (∀ τ μ : ℝ, IsSymSysEq P .thresholding P.c taubar τ → IsSymSysEq P .shading 0 mubar μ →
      profit P .shading (sym μ) ≤ profit P .thresholding (sym τ)) ∧
    (Assumption1 P → ∀ rbar : ℝ, AdmissibleR P rbar → ∀ r τ : ℝ,
      IsSymRestrictedSysEq P rbar r → IsSymSysEq P .thresholding P.c taubar τ →
      profit P .thresholding (sym τ) ≤ profit P .reserve (sym r)) := by
  obtain ⟨hTS_T, hTS_S⟩ := proposition_4_1_TS P
  obtain ⟨huT, hcharT⟩ := hTS_T taubar hT
  obtain ⟨huS, hcharS⟩ := hTS_S mubar hS
  have hc := P.c_pos
  -- the lower end of thresholding is the equilibrium as soon as `G^T(c) ≤ B`
  have hTc : G1 P .thresholding P.c ≤ P.B → ∀ τ, IsSymSysEq P .thresholding P.c taubar τ →
      τ = P.c := by
    intro hle τ hτ
    have hcEq : IsSymSysEq P .thresholding P.c taubar P.c :=
      (hcharT P.c).2 ⟨⟨le_rfl, hT.1⟩, hle, Or.inr rfl⟩
    exact huT.unique hτ hcEq
  have hS0 : G1 P .shading 0 ≤ P.B → ∀ μ, IsSymSysEq P .shading 0 mubar μ → μ = 0 := by
    intro hle μ hμ
    have h0Eq : IsSymSysEq P .shading 0 mubar 0 :=
      (hcharS 0).2 ⟨⟨le_rfl, hS.1⟩, hle, Or.inr rfl⟩
    exact huS.unique hμ h0Eq
  obtain ⟨hIT, hIR, -, -⟩ := items_sold_shading_identity P
  refine ⟨?_, ?_⟩
  · intro τ μ hτ hμ
    by_cases hg : G1 P .thresholding P.c ≤ P.B
    · have e1 := hTc hg τ hτ
      have e2 := hS0 (by rw [solution_aux_G1_S0]; exact hg) μ hμ
      subst e1 e2
      rw [solution_aux_profit_S0]
    · push Not at hg
      obtain ⟨⟨hτ1, -⟩, hτB, hτor⟩ := (hcharT τ).1 hτ
      obtain ⟨⟨hμ1, -⟩, hμB, hμor⟩ := (hcharS μ).1 hμ
      have hτB' : G1 P .thresholding τ = P.B := by
        rcases hτor with h | h
        · exact h
        · subst h; linarith
      have hμB' : G1 P .shading μ = P.B := by
        rcases hμor with h | h
        · exact h
        · subst h; rw [solution_aux_G1_S0] at hμB; linarith
      have hI : itemsSold P .thresholding (sym τ) ≤ itemsSold P .shading (sym μ) := by
        by_contra hlt
        push Not at hlt
        have := lemma_B_3 P τ μ hτ1 hμ1 hlt
        linarith
      rw [solution_aux_profit_eq, solution_aux_profit_eq, hτB', hμB']
      nlinarith
  · intro hA rbar hR r τ hr hτ
    obtain ⟨-, hcharR⟩ := proposition_4_1_R P hA rbar hR
    obtain ⟨hrS, hrB, hror⟩ := (hcharR r).1 hr
    obtain ⟨⟨hτ1, -⟩, hτB, hτor⟩ := (hcharT τ).1 hτ
    have hr1 : P.c ≤ r := hrS.1.1
    have hlow := G1_reserve_c_le_lower_end P hA rbar hR
    rw [solution_aux_reserve_c] at hlow
    -- `G^T(τ) ≤ G^R(r)`
    have hG : G1 P .thresholding τ ≤ G1 P .reserve r := by
      rcases hror with h | h
      · rw [h]; exact hτB
      · by_cases hrB' : G1 P .reserve r = P.B
        · rw [hrB']; exact hτB
        · have hlt : G1 P .reserve r < P.B := lt_of_le_of_ne hrB hrB'
          rw [← h] at hlow
          have e := hTc (by linarith) τ hτ
          subst e
          exact hlow
    -- `I^R(r) ≤ I^T(τ)`
    have hI : itemsSold P .reserve (sym r) ≤ itemsSold P .thresholding (sym τ) := by
      by_cases hτc : τ = P.c
      · subst hτc
        rw [hIT _ hc.le, hIR r (hc.le.trans hr1)]
        have := solution_aux_cdf_mono P _ _ hr1
        have hT0 : (0 : ℝ) ≤ P.T := Nat.cast_nonneg _
        nlinarith
      · have hτB' : G1 P .thresholding τ = P.B := by
          rcases hτor with h | h
          · exact h
          · exact absurd h hτc
        by_contra hlt
        push Not at hlt
        have := lemma_B_2 P r τ hr1 hτ1 hlt
        linarith
    rw [solution_aux_profit_eq, solution_aux_profit_eq]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
