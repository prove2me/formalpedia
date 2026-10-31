-- Prove2me | solution 1 for EndogBudgetAds.Equilibrium.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T16:29:50.123901+00:00
-- url     : https://prove2.me/submissions/b751b291-14eb-4b12-a2c2-061256a5fcd4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_EndogBudgetAds_Equilibrium_Model
import Theorems.Thm_EndogBudgetAds_Equilibrium_lemma_5
import Theorems.Thm_EndogBudgetAds_Equilibrium_lemma_16
import Theorems.Thm_EndogBudgetAds_Equilibrium_lemma_17
open MeasureTheory

namespace EndogThm1Aux
open EndogBudgetAds.Equilibrium ProbabilityTheory

/-! ### Exponential distribution facts -/

lemma integrable_expMeasure_id {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : ℝ => x) (expMeasure r) := by
  unfold expMeasure gammaMeasure
  have hmeas : Measurable (gammaPDF 1 r) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 r)
  rw [integrable_withDensity_iff_integrable_smul' hmeas
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have hg : Integrable (Set.indicator (Set.Ioi (0:ℝ)) (fun x => 2 * Real.exp ((-(r/2)) * x)))
      volume := by
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul 2
  refine hg.mono' ?_ ?_
  · exact ((hmeas.ennreal_toReal).mul measurable_id).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    simp only [smul_eq_mul]
    rcases lt_or_ge 0 x with hx | hx
    · rw [Set.indicator_of_mem (by exact hx)]
      have h1 : (gammaPDF 1 r x).toReal = r * Real.exp (-(r * x)) := by
        have := exponentialPDF_of_nonneg (r := r) hx.le
        unfold exponentialPDF exponentialPDFReal at this
        unfold gammaPDF
        rw [ENNReal.toReal_ofReal (by
          unfold gammaPDFReal; rw [if_pos hx.le]; positivity)]
        unfold gammaPDFReal; rw [if_pos hx.le]; simp
      rw [h1, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h2 := Real.add_one_le_exp (r * x / 2)
      have h3 : Real.exp (-(r * x)) = Real.exp ((-(r/2)) * x) * Real.exp ((-(r/2)) * x) := by
        rw [← Real.exp_add]; ring_nf
      have h4 : Real.exp ((-(r/2)) * x) * Real.exp (r * x / 2) = 1 := by
        rw [← Real.exp_add]; ring_nf; simp
      have h5 : 0 < Real.exp ((-(r/2)) * x) := Real.exp_pos _
      rw [h3]
      nlinarith [mul_pos h5 h5, mul_pos hr hx]
    · rw [Set.indicator_of_notMem (by simp; exact hx)]
      have : gammaPDF 1 r x = 0 ∨ x = 0 := by
        rcases eq_or_lt_of_le hx with h | h
        · right; exact h
        · left; exact exponentialPDF_of_neg h
      rcases this with h | h
      · simp [h]
      · simp [h]

lemma ae_nonneg_expMeasure (r : ℝ) : ∀ᵐ x ∂(expMeasure r), 0 ≤ x := by
  unfold expMeasure gammaMeasure
  have hmeas : Measurable (gammaPDF 1 r) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 r)
  rw [ae_withDensity_iff hmeas]
  refine Filter.Eventually.of_forall fun x hx => ?_
  by_contra h
  exact hx (exponentialPDF_of_neg (not_le.mp h))

/-! ### The valuation law -/

lemma isProb_row (M : Market) (hM : M.Standing) (l : Fin M.m) :
    IsProbabilityMeasure (Measure.pi fun _ : Fin M.n => expMeasure (M.lam l)) := by
  haveI : IsProbabilityMeasure (expMeasure (M.lam l)) :=
    isProbabilityMeasure_expMeasure (hM.lam_pos l)
  infer_instance

lemma isProb_valLaw (M : Market) (hM : M.Standing) : IsProbabilityMeasure (valLaw M) := by
  haveI := isProb_row M hM
  unfold valLaw; infer_instance

lemma coord_integrable (M : Market) (hM : M.Standing) (l : Fin M.m) (i : Fin M.n) :
    Integrable (fun V : Valuations M => V l i) (valLaw M) := by
  haveI : ∀ l, IsProbabilityMeasure (expMeasure (M.lam l)) :=
    fun l => isProbabilityMeasure_expMeasure (hM.lam_pos l)
  haveI := isProb_row M hM
  have h1 : Integrable (fun v : Fin M.n → ℝ => v i)
      (Measure.pi fun _ : Fin M.n => expMeasure (M.lam l)) :=
    (measurePreserving_eval (fun _ : Fin M.n => expMeasure (M.lam l)) i).integrable_comp_of_integrable
      (g := fun x : ℝ => x) (integrable_expMeasure_id (hM.lam_pos l))
  exact (measurePreserving_eval (fun l => Measure.pi fun _ : Fin M.n => expMeasure (M.lam l))
    l).integrable_comp_of_integrable (g := fun v : Fin M.n → ℝ => v i) h1

lemma ae_nonneg_valLaw (M : Market) (hM : M.Standing) :
    ∀ᵐ V ∂(valLaw M), ∀ l i, 0 ≤ V l i := by
  haveI : ∀ l, IsProbabilityMeasure (expMeasure (M.lam l)) :=
    fun l => isProbabilityMeasure_expMeasure (hM.lam_pos l)
  have := isProb_row M hM
  rw [ae_all_iff]; intro l; rw [ae_all_iff]; intro i
  have h1 : ∀ᵐ v ∂(Measure.pi fun _ : Fin M.n => expMeasure (M.lam l)), 0 ≤ v i :=
    (measurePreserving_eval _ i).quasiMeasurePreserving.ae (ae_nonneg_expMeasure _)
  exact (measurePreserving_eval (fun l => Measure.pi fun _ : Fin M.n => expMeasure (M.lam l))
    l).quasiMeasurePreserving.ae h1

lemma sum_abs_integrable (M : Market) (hM : M.Standing) :
    Integrable (fun V : Valuations M => ∑ l, ∑ i, |V l i|) (valLaw M) :=
  integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun i _ =>
    (coord_integrable M hM l i).abs

/-! ### Deterministic facts about `top2`, `pay`, `PsiBar` -/

lemma top2_abs_le {m : ℕ} (x : Fin m → ℝ) : |top2 x| ≤ ∑ l, |x l| := by
  unfold top2
  split_ifs with h
  · obtain ⟨p, hp, hpeq⟩ := Finset.exists_mem_eq_sup' h (fun p => min (x p.1) (x p.2))
    rw [hpeq]
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    calc |min (x p.1) (x p.2)| ≤ |x p.1| + |x p.2| := by
          rcases min_choice (x p.1) (x p.2) with h' | h' <;> rw [h'] <;>
            linarith [abs_nonneg (x p.1), abs_nonneg (x p.2)]
      _ = ∑ l ∈ {p.1, p.2}, |x l| := (Finset.sum_pair (f := fun l => |x l|) hne).symm
      _ ≤ ∑ l, |x l| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => abs_nonneg _)
  · simp only [abs_zero]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma top2_nonneg_of {m : ℕ} (x : Fin m → ℝ) (k l : Fin m) (hlk : l ≠ k) (hl : 0 ≤ x l)
    (hk : 0 ≤ x k) : 0 ≤ top2 x := by
  unfold top2
  have hmem : (l, k) ∈ (Finset.univ.filter fun p : Fin m × Fin m => p.1 ≠ p.2) := by
    simp [hlk]
  rw [dif_pos ⟨_, hmem⟩]
  exact le_trans (le_min hl hk) (Finset.le_sup' (fun p => min (x p.1) (x p.2)) hmem)

lemma PsiBar_nonneg (M : Market) (k : Fin M.m) (V : Valuations M) (l0 : Fin M.m)
    (hl0 : l0 ≠ k) (hV : ∀ l, l ≠ k → ∀ i, 0 ≤ W M V l i) : 0 ≤ PsiBar M k V := by
  unfold PsiBar
  refine Finset.sum_nonneg fun i _ => ?_
  split_ifs with h
  · exact top2_nonneg_of _ k l0 hl0 (hV l0 hl0 i)
      (le_of_lt (lt_of_le_of_lt (hV l0 hl0 i) (h l0 hl0)))
  · exact le_rfl

lemma pay_abs_le {m n : ℕ} (b : Fin m → Fin n → ℝ) (i : Fin n) (k : Fin m) :
    |pay b i k| ≤ ∑ l ∈ Finset.univ.erase k, |b l i| := by
  have hsingle : ∀ l, l ≠ k → |b l i| ≤ ∑ l ∈ Finset.univ.erase k, |b l i| := fun l hl =>
    Finset.single_le_sum (f := fun l => |b l i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ _⟩)
  unfold pay
  split_ifs with h
  · refine abs_le.mpr ⟨?_, ?_⟩
    · have hc : h.choose ≠ k := fun hk => by
        have := h.choose_spec; rw [hk] at this; exact lt_irrefl _ this
      have hmem : h.choose ∈ (Finset.univ.filter fun l => l ≠ k ∧ b l i ≤ b k i) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hc, le_of_lt h.choose_spec⟩
      apply Finset.le_sup'_of_le _ hmem
      have := hsingle _ hc
      linarith [neg_abs_le (b h.choose i)]
    · apply Finset.sup'_le
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      exact le_trans (le_abs_self _) (hsingle l hl.1)
  · simp only [abs_zero]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma measurable_finset_sup'' {δ ι : Type*} [MeasurableSpace δ] {s : Finset ι}
    (hs : s.Nonempty) {f : ι → δ → ℝ} (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x => s.sup' hs (fun n => f n x)) := by
  have := Finset.measurable_sup' hs (fun n _ => hf n)
  convert this using 1
  ext x
  rw [Finset.sup'_apply]

lemma pay_eq {m n : ℕ} (b : Fin m → Fin n → ℝ) (i : Fin n) (k : Fin m) :
    pay b i k = if (∃ l, b l i < b k i) then
      Finset.univ.sup' ⟨k, Finset.mem_univ _⟩ (fun l =>
        if l ≠ k ∧ b l i ≤ b k i then b l i else -(∑ l', |b l' i|)) else 0 := by
  unfold pay
  split_ifs with h
  · have hc : h.choose ≠ k := fun hk => by
      have := h.choose_spec; rw [hk] at this; exact lt_irrefl _ this
    have hmem : h.choose ∈ (Finset.univ.filter fun l => l ≠ k ∧ b l i ≤ b k i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hc, le_of_lt h.choose_spec⟩
    apply le_antisymm
    · apply Finset.sup'_le
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      apply Finset.le_sup'_of_le _ (Finset.mem_univ l)
      rw [if_pos hl]
    · apply Finset.sup'_le
      intro l _
      split_ifs with hl
      · apply Finset.le_sup'_of_le _ (by simpa using hl : l ∈ _)
        exact le_rfl
      · apply Finset.le_sup'_of_le _ hmem
        have : |b h.choose i| ≤ ∑ l', |b l' i| :=
          Finset.single_le_sum (f := fun l => |b l i|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ _)
        linarith [neg_abs_le (b h.choose i)]
  · rfl

lemma measurable_pay {m n : ℕ} (i : Fin n) (k : Fin m) :
    Measurable (fun b : Fin m → Fin n → ℝ => pay b i k) := by
  simp_rw [pay_eq]
  refine Measurable.ite ?_ ?_ measurable_const
  · simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun l => measurableSet_lt (by fun_prop) (by fun_prop)
  · refine measurable_finset_sup'' _ fun l => ?_
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    simp only [Set.ofPred_and]
    exact (MeasurableSet.const _).inter (measurableSet_le (by fun_prop) (by fun_prop))

lemma measurable_top2 {m : ℕ} : Measurable (fun x : Fin m → ℝ => top2 x) := by
  by_cases h : ((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 ≠ p.2)).Nonempty
  · simp only [top2, dif_pos h]
    exact measurable_finset_sup'' h fun p => by fun_prop
  · simp only [top2, dif_neg h]; exact measurable_const

lemma measurableSet_isTop {m : ℕ} (k : Fin m) : MeasurableSet {x : Fin m → ℝ | EndogBudgetAds.Equilibrium.IsTop x k} := by
  unfold EndogBudgetAds.Equilibrium.IsTop; simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ =>
    measurableSet_lt (by fun_prop) (by fun_prop)

lemma measurable_W (M : Market) (l : Fin M.m) (i : Fin M.n) :
    Measurable (fun V : Valuations M => W M V l i) := by
  unfold W; fun_prop

lemma measurable_PsiBar (M : Market) (k : Fin M.m) :
    Measurable (fun V : Valuations M => PsiBar M k V) := by
  unfold PsiBar
  refine Finset.measurable_sum _ fun i _ => ?_
  have hmap : Measurable (fun V : Valuations M => fun l => W M V l i) :=
    measurable_pi_lambda _ fun l => measurable_W M l i
  refine Measurable.ite ?_ (measurable_top2.comp hmap) measurable_const
  exact hmap (measurableSet_isTop k)

/-! ### Measurability of outcomes -/

def ProfMeas {M : Market} (σ : Fin M.m → Strategy M.n) : Prop :=
  ∀ k, Measurable (σ k).budget ∧ Measurable (σ k).bid

lemma measurable_bidsOf {M : Market} {σ : Fin M.m → Strategy M.n} (h : ProfMeas σ) :
    Measurable (fun V : Valuations M => bidsOf σ V) :=
  measurable_pi_lambda _ fun k => (h k).2.comp (measurable_pi_apply k)

lemma measurable_budgetsOf {M : Market} {σ : Fin M.m → Strategy M.n} (h : ProfMeas σ) :
    Measurable (fun V : Valuations M => budgetsOf σ V) :=
  measurable_pi_lambda _ fun k => (h k).1.comp (measurable_pi_apply k)

lemma measurable_alloc_apply {M : Market} {alloc : AllocRule M} (halloc : IsAllocRule M alloc)
    {σ : Fin M.m → Strategy M.n} (h : ProfMeas σ) (i : Fin M.n) (j : Fin M.m) :
    Measurable (fun V : Valuations M => alloc (budgetsOf σ V) (bidsOf σ V) i j) := by
  have h1 : Measurable (fun V : Valuations M => alloc (budgetsOf σ V) (bidsOf σ V)) :=
    halloc.1.comp ((measurable_budgetsOf h).prodMk (measurable_bidsOf h))
  exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp h1)

lemma measurable_pay_of {M : Market} {σ : Fin M.m → Strategy M.n} (h : ProfMeas σ)
    (i : Fin M.n) (j : Fin M.m) :
    Measurable (fun V : Valuations M => pay (bidsOf σ V) i j) :=
  (measurable_pay i j).comp (measurable_bidsOf h)

lemma measurable_spend {M : Market} {alloc : AllocRule M} (halloc : IsAllocRule M alloc)
    {σ : Fin M.m → Strategy M.n} (h : ProfMeas σ) (j : Fin M.m) :
    Measurable (fun V => spend M alloc σ j V) := by
  unfold spend
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_pay_of h i j).mul (measurable_alloc_apply halloc h i j)

lemma measurable_ownBudget {M : Market} {σ : Fin M.m → Strategy M.n} (h : ProfMeas σ)
    (j : Fin M.m) : Measurable (fun V : Valuations M => budgetsOf σ V j) :=
  (h j).1.comp (measurable_pi_apply j)

lemma measurable_payoff {M : Market} {alloc : AllocRule M} (halloc : IsAllocRule M alloc)
    {σ : Fin M.m → Strategy M.n} (h : ProfMeas σ) (j : Fin M.m) :
    Measurable (fun V => payoff M alloc σ j V) := by
  unfold payoff
  refine Measurable.sub ?_ ((measurable_ownBudget h j).const_mul _)
  exact Finset.measurable_sum _ fun i _ =>
    ((by fun_prop : Measurable (fun V : Valuations M => V j i)).sub
      (measurable_pay_of h i j)).mul (measurable_alloc_apply halloc h i j)

lemma measurable_modProfit {M : Market} {alloc : AllocRule M} (halloc : IsAllocRule M alloc)
    {σ : Fin M.m → Strategy M.n} (h : ProfMeas σ) (j : Fin M.m) :
    Measurable (fun V => modProfit M alloc σ j V) := by
  unfold modProfit
  exact (measurable_payoff halloc h j).add
    (((measurable_ownBudget h j).sub (measurable_spend halloc h j)).const_mul _)

lemma profMeas_deviate {M : Market} {σ : Fin M.m → Strategy M.n} (hσ : ProfMeas σ)
    (j : Fin M.m) (σj : Strategy M.n) (hj : Measurable σj.budget ∧ Measurable σj.bid) :
    ProfMeas (deviate σ j σj) := by
  intro k
  by_cases hk : k = j
  · subst hk; simp only [deviate, Function.update_self]; exact hj
  · simp only [deviate, Function.update_of_ne hk]; exact hσ k

/-! ### The budget `B*` -/

lemma measurable_Bstar (M : Market) (hM : M.Standing) (j : Fin M.m) :
    Measurable (Bstar M j) := by
  have := isProb_valLaw M hM
  have hf : Measurable (fun p : (Fin M.n → ℝ) × Valuations M =>
      PsiBar M j (Function.update p.2 j p.1)) :=
    (measurable_PsiBar M j).comp (measurable_update'.comp (measurable_snd.prodMk measurable_fst))
  have h2 := (hf.stronglyMeasurable.integral_prod_right' (ν := valLaw M)).measurable
  unfold Bstar
  exact h2.mul_const _

lemma profMeas_sigmaStar (M : Market) (hM : M.Standing) : ProfMeas (sigmaStar M) := by
  intro k
  refine ⟨measurable_Bstar M hM k, ?_⟩
  show Measurable (fun v : Fin M.n → ℝ => fun i => v i / (1 + M.r k))
  fun_prop

lemma vt_pos (M : Market) (hM : M.Standing) : 0 < vt M :=
  div_pos (lt_of_lt_of_le hM.θmin_pos hM.θmin_le_θmax) hM.θmin_pos

lemma one_le_vt (M : Market) (hM : M.Standing) : 1 ≤ vt M := by
  unfold vt; rw [le_div_iff₀ hM.θmin_pos]; linarith [hM.θmin_le_θmax]

lemma beta_nonneg (M : Market) (hM : M.Standing) : 0 ≤ beta M := by
  unfold EndogBudgetAds.Equilibrium.beta
  have := vt_pos M hM
  positivity

lemma exists_other (M : Market) (hm : 2 ≤ M.m) (j : Fin M.m) : ∃ l, l ≠ j := by
  haveI : Nontrivial (Fin M.m) := Fin.nontrivial_iff_two_le.mpr hm
  exact exists_ne j

lemma W_nonneg (M : Market) (hM : M.Standing) (V : Valuations M) (l : Fin M.m) (i : Fin M.n)
    (h : 0 ≤ V l i) : 0 ≤ W M V l i := by
  unfold W; have := hM.r_nonneg l; positivity

lemma Bstar_nonneg (M : Market) (hM : M.Standing) (hm : 2 ≤ M.m) (j : Fin M.m)
    (v : Fin M.n → ℝ) : 0 ≤ Bstar M j v := by
  unfold Bstar
  obtain ⟨l0, hl0⟩ := exists_other M hm j
  refine mul_nonneg ?_ (by linarith [beta_nonneg M hM])
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_nonneg_valLaw M hM] with V hV
  refine PsiBar_nonneg M j _ l0 hl0 fun l hl i => ?_
  apply W_nonneg M hM
  rw [Function.update_of_ne hl]; exact hV l i

lemma PsiBar_abs_le (M : Market) (hM : M.Standing) (k : Fin M.m) (V : Valuations M) :
    |PsiBar M k V| ≤ ∑ l, ∑ i, |V l i| := by
  unfold PsiBar
  rw [Finset.sum_comm]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
  split_ifs
  · refine le_trans (top2_abs_le _) (Finset.sum_le_sum fun l _ => ?_)
    unfold W
    rw [abs_div, abs_of_pos (by linarith [hM.r_nonneg l] : (0:ℝ) < 1 + M.r l)]
    exact div_le_self (abs_nonneg _) (by linarith [hM.r_nonneg l])
  · simp only [abs_zero]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma integrable_PsiBar (M : Market) (hM : M.Standing) (k : Fin M.m) :
    Integrable (fun V => PsiBar M k V) (valLaw M) :=
  (sum_abs_integrable M hM).mono' (measurable_PsiBar M k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun V => by
      rw [Real.norm_eq_abs]; exact PsiBar_abs_le M hM k V)

/-- Resampling all coordinates but `j` preserves the law. -/
lemma measurePreserving_resample (M : Market) (hM : M.Standing) (j : Fin M.m) :
    MeasurePreserving (fun p : Valuations M × Valuations M => Function.update p.2 j (p.1 j))
      ((valLaw M).prod (valLaw M)) (valLaw M) := by
  haveI := isProb_row M hM
  have hHm : Measurable (fun p : Valuations M × Valuations M =>
      Function.update p.2 j (p.1 j)) :=
    measurable_update'.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))
  refine ⟨hHm, ?_⟩
  set ν : Fin M.m → Measure (Fin M.n → ℝ) := fun l =>
    Measure.pi fun _ : Fin M.n => expMeasure (M.lam l) with hν
  have hval : valLaw M = Measure.pi ν := rfl
  have key : ∀ (t : Set (Fin M.n → ℝ)) (s' : ∀ _ : Fin M.m, Set (Fin M.n → ℝ)),
      ∏ l, ν l (Function.update s' j t l) = ν j t * ∏ l ∈ Finset.univ.erase j, ν l (s' l) := by
    intro t s'
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  symm
  rw [hval]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hHm (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : Valuations M × Valuations M => Function.update p.2 j (p.1 j)) ⁻¹'
      (Set.univ.pi s) = (Set.univ.pi (Function.update (fun _ => Set.univ) j (s j))) ×ˢ
        (Set.univ.pi (Function.update s j Set.univ)) := by
    ext ⟨V, V'⟩
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ_pi]
    constructor
    · intro h
      refine ⟨fun l => ?_, fun l => ?_⟩
      · by_cases hl : l = j
        · subst hl; simpa using h l
        · rw [Function.update_of_ne hl]; exact Set.mem_univ _
      · by_cases hl : l = j
        · subst hl; rw [Function.update_self]; exact Set.mem_univ _
        · have := h l; rw [Function.update_of_ne hl] at this ⊢; exact this
    · rintro ⟨h1, h2⟩ l
      by_cases hl : l = j
      · subst hl; have := h1 l; rw [Function.update_self] at this
        rw [Function.update_self]; exact this
      · have := h2 l; rw [Function.update_of_ne hl] at this ⊢; exact this
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, key, key]
  have h1 : ∀ l, ν l Set.univ = 1 := fun l => measure_univ
  simp only [h1, Finset.prod_const_one, mul_one, one_mul]
  exact Finset.mul_prod_erase Finset.univ (fun l => ν l (s l)) (Finset.mem_univ j)

lemma Bstar_tower (M : Market) (hM : M.Standing) (j : Fin M.m) :
    Integrable (fun V : Valuations M => Bstar M j (V j)) (valLaw M) ∧
    ∫ V, Bstar M j (V j) ∂(valLaw M) = (∫ V, PsiBar M j V ∂(valLaw M)) * (1 + beta M) := by
  have := isProb_valLaw M hM
  have hH := measurePreserving_resample M hM j
  have hf := integrable_PsiBar M hM j
  have hint : Integrable ((fun V => PsiBar M j V) ∘
      (fun p : Valuations M × Valuations M => Function.update p.2 j (p.1 j)))
      ((valLaw M).prod (valLaw M)) := hH.integrable_comp_of_integrable hf
  have hmap := integral_map (μ := (valLaw M).prod (valLaw M)) hH.measurable.aemeasurable
    (f := fun V => PsiBar M j V) (by rw [hH.map_eq]; exact hf.aestronglyMeasurable)
  rw [hH.map_eq] at hmap
  have hprod := integral_prod _ hint
  unfold Bstar
  refine ⟨hint.integral_prod_left.mul_const _, ?_⟩
  rw [integral_mul_const, hmap]
  congr 1
  exact hprod.symm

/-! ### Real-number estimates -/

lemma final_arith (Ms P S Pi Dm r β a ϑ L x γ : ℝ) (hr : 0 ≤ r) (hP : 0 ≤ P) (hϑ : 1 ≤ ϑ)
    (ha : 0 < a) (hL : 0 < L) (hx : x = ϑ ^ 2 * L / a) (hβ : β = 2 * ϑ / a)
    (hx5 : x ≤ 1 / 5) (hγ : γ ≤ x / 3)
    (hPi : Pi = Ms - r * (P * (1 + β) - S)) (hS : P * (1 - 1 / a) ≤ S)
    (h17 : 9 * (1 + r) / (10 * ϑ * L) * P ≤ Ms) (hMs : 0 ≤ Ms) (hD : Dm ≤ Ms * (1 + γ)) :
    Dm ≤ Pi * (1 + 11 * x) ∧ 0 ≤ Pi * (1 + 11 * x) := by
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have h1 : P * (1 + β) - S ≤ P * (3 * ϑ / a) := by
    have e : P * (1 + β) - P * (1 - 1 / a) = P * ((2 * ϑ + 1) / a) := by
      rw [hβ]; field_simp; ring
    have : P * ((2 * ϑ + 1) / a) ≤ P * (3 * ϑ / a) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) ha.le) hP
    linarith
  have hc : 0 < 10 * ϑ * L / 9 := by positivity
  have h2 : (1 + r) * P ≤ Ms * (10 * ϑ * L / 9) := by
    have e : (1 + r) * P = (9 * (1 + r) / (10 * ϑ * L) * P) * (10 * ϑ * L / 9) := by
      field_simp
    rw [e]; exact mul_le_mul_of_nonneg_right h17 hc.le
  have h3 : r * (P * (1 + β) - S) ≤ Ms * (10 / 3) * x := by
    have hq : 0 ≤ 3 * ϑ / a := by positivity
    calc r * (P * (1 + β) - S) ≤ r * (P * (3 * ϑ / a)) := mul_le_mul_of_nonneg_left h1 hr
      _ ≤ (1 + r) * P * (3 * ϑ / a) := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (by nlinarith) hq
      _ ≤ Ms * (10 * ϑ * L / 9) * (3 * ϑ / a) := mul_le_mul_of_nonneg_right h2 hq
      _ = Ms * (10 / 3) * x := by rw [hx]; field_simp; ring
  have hPi' : Ms * (1 - 10 / 3 * x) ≤ Pi := by rw [hPi]; nlinarith
  have hpos : 0 ≤ 1 + 11 * x := by linarith
  have h4 : Ms * (1 - 10 / 3 * x) * (1 + 11 * x) ≤ Pi * (1 + 11 * x) :=
    mul_le_mul_of_nonneg_right hPi' hpos
  have h5 : (1 + x / 3) ≤ (1 - 10 / 3 * x) * (1 + 11 * x) := by nlinarith
  have h6 : Ms * (1 + γ) ≤ Ms * (1 - 10 / 3 * x) * (1 + 11 * x) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by linarith) hMs
  refine ⟨by linarith, ?_⟩
  have : 0 ≤ Ms * (1 - 10 / 3 * x) * (1 + 11 * x) :=
    mul_nonneg (mul_nonneg hMs (by linarith)) hpos
  linarith

lemma exp_three_gt : (20 : ℝ) < Real.exp 3 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have h0 : (0:ℝ) ≤ 2.7182818283 := by norm_num
  calc (20:ℝ) < 2.7182818283 ^ 3 := by norm_num
    _ < Real.exp 1 ^ 3 := by gcongr

/-- `x = ϑ² log m / m^{1/ϑ} ≤ 1/5` and `3ϑ/m^{3ϑ/2} ≤ x/3`. -/
lemma size_bounds (ϑ m : ℝ) (hϑ : 1 ≤ ϑ) (hm : Real.exp (3 * ϑ + 5 * ϑ * Real.log ϑ + 1) ≤ m) :
    ϑ ^ 2 * Real.log m / m ^ (1 / ϑ) ≤ 1 / 5 ∧
      3 * ϑ / m ^ (3 * ϑ / 2) ≤ (ϑ ^ 2 * Real.log m / m ^ (1 / ϑ)) / 3 := by
  have hϑ0 : 0 < ϑ := by linarith
  have hlogϑ : 0 ≤ Real.log ϑ := Real.log_nonneg hϑ
  have hm0 : 0 < m := lt_of_lt_of_le (Real.exp_pos _) hm
  set L := Real.log m with hLdef
  have hL : 3 * ϑ + 5 * ϑ * Real.log ϑ + 1 ≤ L := (Real.le_log_iff_exp_le hm0).mpr hm
  have hL4 : 4 ≤ L := by nlinarith
  have ha : m ^ (1 / ϑ) = Real.exp (L / ϑ) := by
    rw [Real.rpow_def_of_pos hm0]; congr 1; ring
  have hb : m ^ (3 * ϑ / 2) = Real.exp (L / ϑ) * Real.exp (3 * ϑ * L / 2 - L / ϑ) := by
    rw [Real.rpow_def_of_pos hm0, ← Real.exp_add]; congr 1; ring
  rw [ha, hb]
  set t := L / ϑ with htdef
  have hLt : L = ϑ * t := by rw [htdef]; field_simp
  set t0 := 3 + 5 * Real.log ϑ + 1 / ϑ with ht0def
  have ht0 : t0 ≤ t := by
    rw [htdef, le_div_iff₀ hϑ0, ht0def]
    have : 1 / ϑ * ϑ = 1 := by field_simp
    nlinarith
  have hinv : 1 / ϑ ≤ 1 := by rw [div_le_one hϑ0]; exact hϑ
  have hinv0 : 0 < 1 / ϑ := by positivity
  have ht01 : 1 ≤ t0 := by rw [ht0def]; linarith
  constructor
  · -- t / exp t ≤ t0 / exp t0
    have hexp : Real.exp t0 * (1 + (t - t0)) ≤ Real.exp t := by
      have := Real.add_one_le_exp (t - t0)
      have e : Real.exp t = Real.exp t0 * Real.exp (t - t0) := by
        rw [← Real.exp_add]; ring_nf
      rw [e]; exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    have htt : t ≤ t0 * (1 + (t - t0)) := by nlinarith
    -- exp t0 ≥ 20 ϑ^5
    have hexp0 : 20 * ϑ ^ 5 ≤ Real.exp t0 := by
      have e1 : Real.exp (5 * Real.log ϑ) = ϑ ^ 5 := by
        rw [show (5:ℝ) * Real.log ϑ = ((5:ℕ):ℝ) * Real.log ϑ by norm_num, Real.exp_nat_mul,
          Real.exp_log hϑ0]
      have e2 : Real.exp t0 = Real.exp 3 * Real.exp (5 * Real.log ϑ) * Real.exp (1 / ϑ) := by
        rw [← Real.exp_add, ← Real.exp_add]
      rw [e2, e1]
      have h3 := exp_three_gt
      have h4 : 1 ≤ Real.exp (1 / ϑ) := Real.one_le_exp hinv0.le
      have h5 : 0 < ϑ ^ 5 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h4 (mul_pos (Real.exp_pos 3) h5).le]
    have hlog1 : Real.log ϑ ≤ ϑ - 1 := Real.log_le_sub_one_of_pos hϑ0
    have ht0le : t0 ≤ 5 * ϑ - 1 := by rw [ht0def]; linarith
    -- combine
    have hexpt : 0 < Real.exp t := Real.exp_pos _
    rw [div_le_iff₀ hexpt, hLt]
    -- goal: ϑ^2 * (ϑ * t) ≤ 1/5 * exp t
    have k1 : t * Real.exp t0 ≤ t0 * Real.exp t := by
      calc t * Real.exp t0 ≤ t0 * (1 + (t - t0)) * Real.exp t0 :=
            mul_le_mul_of_nonneg_right htt (Real.exp_pos _).le
        _ = t0 * (Real.exp t0 * (1 + (t - t0))) := by ring
        _ ≤ t0 * Real.exp t := mul_le_mul_of_nonneg_left hexp (by linarith)
    have ht_pos : 0 < t := by linarith
    have k2 : t * (20 * ϑ ^ 5) ≤ t0 * Real.exp t :=
      le_trans (mul_le_mul_of_nonneg_left hexp0 ht_pos.le) k1
    have k3 : t0 ≤ 4 * ϑ ^ 2 := by nlinarith
    have k4 : t * (20 * ϑ ^ 5) ≤ 4 * ϑ ^ 2 * Real.exp t :=
      le_trans k2 (mul_le_mul_of_nonneg_right k3 hexpt.le)
    have k5 : 0 < ϑ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left k4 k5.le]
  · have hd : 2 ≤ 3 * ϑ * L / 2 - L / ϑ := by
      have : L / ϑ ≤ L := div_le_self (by linarith) hϑ
      nlinarith
    have he : 3 ≤ Real.exp (3 * ϑ * L / 2 - L / ϑ) := by
      have := Real.add_one_le_exp (3 * ϑ * L / 2 - L / ϑ); linarith
    have hea : 0 < Real.exp t := Real.exp_pos _
    rw [div_le_iff₀ (by positivity), div_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have hϑL : 4 ≤ ϑ * L := by nlinarith
    have : 9 ≤ ϑ * L * Real.exp (3 * ϑ * L / 2 - L / ϑ) := by nlinarith
    have hpos : 0 < ϑ * Real.exp t := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hpos.le]

/-! ### Integrability of outcomes -/

lemma feas_of {M : Market} {alloc : AllocRule M} (halloc : IsAllocRule M alloc)
    {σ : Fin M.m → Strategy M.n} (hB : ∀ k v, 0 ≤ (σ k).budget v) (V : Valuations M) :
    AllocFeasible M (budgetsOf σ V) (bidsOf σ V) (alloc (budgetsOf σ V) (bidsOf σ V)) :=
  (halloc.2 _ _ (fun k => hB k (V k))).1

lemma Y_le_one {M : Market} {B : Fin M.m → ℝ} {b : Fin M.m → Fin M.n → ℝ}
    {Y : Fin M.n → Fin M.m → ℝ} (h : AllocFeasible M B b Y) (i : Fin M.n) (j : Fin M.m) :
    Y i j ≤ 1 :=
  le_trans (Finset.single_le_sum (f := fun j => Y i j) (fun j _ => h.1 i j)
    (Finset.mem_univ j)) (h.2.2 i)

lemma W_abs_le (M : Market) (hM : M.Standing) (V : Valuations M) (l : Fin M.m) (i : Fin M.n) :
    |W M V l i| ≤ |V l i| := by
  unfold W
  rw [abs_div, abs_of_pos (by linarith [hM.r_nonneg l] : (0:ℝ) < 1 + M.r l)]
  exact div_le_self (abs_nonneg _) (by linarith [hM.r_nonneg l])

lemma bids_other {M : Market} {σ : Fin M.m → Strategy M.n} {j : Fin M.m}
    (hO : ∀ l, l ≠ j → σ l = sigmaStar M l) (V : Valuations M) (l : Fin M.m) (hl : l ≠ j)
    (i : Fin M.n) : bidsOf σ V l i = W M V l i := by
  simp only [bidsOf, hO l hl]; rfl

lemma spend_abs_le (M : Market) (hM : M.Standing) {alloc : AllocRule M}
    (halloc : IsAllocRule M alloc) {σ : Fin M.m → Strategy M.n}
    (hB : ∀ k v, 0 ≤ (σ k).budget v) {j : Fin M.m} (hO : ∀ l, l ≠ j → σ l = sigmaStar M l)
    (V : Valuations M) : |spend M alloc σ j V| ≤ ∑ l, ∑ i, |V l i| := by
  have hF := feas_of halloc hB V
  unfold spend
  rw [Finset.sum_comm]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have hY0 := hF.1 i j
  have hY1 := Y_le_one hF i j
  have hp : |pay (bidsOf σ V) i j| ≤ ∑ l, |V l i| := by
    refine le_trans (pay_abs_le _ i j) ?_
    calc ∑ l ∈ Finset.univ.erase j, |bidsOf σ V l i|
          = ∑ l ∈ Finset.univ.erase j, |W M V l i| :=
            Finset.sum_congr rfl (fun l hl => by
              rw [bids_other hO V l (Finset.ne_of_mem_erase hl) i])
      _ ≤ ∑ l ∈ Finset.univ.erase j, |V l i| :=
            Finset.sum_le_sum fun l _ => W_abs_le M hM V l i
      _ ≤ ∑ l, |V l i| :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun _ _ _ => abs_nonneg _)
  rw [abs_of_nonneg hY0]
  nlinarith [abs_nonneg (pay (bidsOf σ V) i j)]

lemma gross_abs_le {M : Market} {alloc : AllocRule M} (halloc : IsAllocRule M alloc)
    {σ : Fin M.m → Strategy M.n} (hB : ∀ k v, 0 ≤ (σ k).budget v) (j : Fin M.m)
    (V : Valuations M) :
    |∑ i, V j i * alloc (budgetsOf σ V) (bidsOf σ V) i j| ≤ ∑ l, ∑ i, |V l i| := by
  have hF := feas_of halloc hB V
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_
    (Finset.single_le_sum (f := fun l => ∑ i, |V l i|)
      (fun l _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)))
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul, abs_of_nonneg (hF.1 i j)]
  have := Y_le_one hF i j
  nlinarith [abs_nonneg (V j i)]

lemma modProfit_eq (M : Market) (alloc : AllocRule M) (σ : Fin M.m → Strategy M.n)
    (j : Fin M.m) (V : Valuations M) :
    modProfit M alloc σ j V = (∑ i, V j i * alloc (budgetsOf σ V) (bidsOf σ V) i j) -
      (1 + M.r j) * spend M alloc σ j V := by
  unfold modProfit payoff spend
  have : ∑ i, (V j i - pay (bidsOf σ V) i j) * alloc (budgetsOf σ V) (bidsOf σ V) i j =
      ∑ i, V j i * alloc (budgetsOf σ V) (bidsOf σ V) i j -
        ∑ i, pay (bidsOf σ V) i j * alloc (budgetsOf σ V) (bidsOf σ V) i j := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]; ring

lemma integrable_spend (M : Market) (hM : M.Standing) {alloc : AllocRule M}
    (halloc : IsAllocRule M alloc) {σ : Fin M.m → Strategy M.n} (hσ : ProfMeas σ)
    (hB : ∀ k v, 0 ≤ (σ k).budget v) (j : Fin M.m) (hO : ∀ l, l ≠ j → σ l = sigmaStar M l) :
    Integrable (fun V => spend M alloc σ j V) (valLaw M) :=
  (sum_abs_integrable M hM).mono' (measurable_spend halloc hσ j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun V => by
      rw [Real.norm_eq_abs]; exact spend_abs_le M hM halloc hB hO V)

lemma integrable_modProfit (M : Market) (hM : M.Standing) {alloc : AllocRule M}
    (halloc : IsAllocRule M alloc) {σ : Fin M.m → Strategy M.n} (hσ : ProfMeas σ)
    (hB : ∀ k v, 0 ≤ (σ k).budget v) (j : Fin M.m) (hO : ∀ l, l ≠ j → σ l = sigmaStar M l) :
    Integrable (fun V => modProfit M alloc σ j V) (valLaw M) := by
  have hA : Integrable (fun V : Valuations M =>
      ∑ i, V j i * alloc (budgetsOf σ V) (bidsOf σ V) i j) (valLaw M) := by
    have hmA : Measurable (fun V : Valuations M =>
        ∑ i, V j i * alloc (budgetsOf σ V) (bidsOf σ V) i j) :=
      Finset.measurable_sum _ fun i _ =>
        (by fun_prop : Measurable (fun V : Valuations M => V j i)).mul
          (measurable_alloc_apply halloc hσ i j)
    exact (sum_abs_integrable M hM).mono' hmA.aestronglyMeasurable
      (Filter.Eventually.of_forall fun V => by
        rw [Real.norm_eq_abs]; exact gross_abs_le halloc hB j V)
  have e : (fun V => modProfit M alloc σ j V) = fun V =>
      (∑ i, V j i * alloc (budgetsOf σ V) (bidsOf σ V) i j) -
        (1 + M.r j) * spend M alloc σ j V := funext fun V => modProfit_eq M alloc σ j V
  rw [e]
  exact hA.sub ((integrable_spend M hM halloc hσ hB j hO).const_mul _)

lemma payoff_le_mod (M : Market) (hM : M.Standing) {alloc : AllocRule M}
    (halloc : IsAllocRule M alloc) {σ : Fin M.m → Strategy M.n}
    (hB : ∀ k v, 0 ≤ (σ k).budget v) (j : Fin M.m) (V : Valuations M) :
    payoff M alloc σ j V ≤ modProfit M alloc σ j V := by
  have hF := feas_of halloc hB V
  have h1 : spend M alloc σ j V ≤ budgetsOf σ V j := hF.2.1 j
  have h2 := mul_nonneg (hM.r_nonneg j) (sub_nonneg.mpr h1)
  unfold modProfit; linarith

end EndogThm1Aux

open EndogBudgetAds.Equilibrium EndogThm1Aux in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Market, M.Standing →
      ∀ alloc : AllocRule M, IsAllocRule M alloc →
      (2 * vt M) ^ vt M ≤ (M.m : ℝ) →
      Real.exp (3 * vt M + 5 * vt M * Real.log (vt M) + 1) ≤ (M.m : ℝ) →
      6 * vt M * (M.m : ℝ) ^ (2 * (vt M + 1 / vt M)) * Real.log M.m / C ≤ (M.n : ℝ) →
        (∀ (j : Fin M.m) (σj : Strategy M.n), σj.Admissible →
          ∫ V, payoff M alloc (deviate (sigmaStar M) j σj) j V ∂ valLaw M ≤
            (∫ V, payoff M alloc (sigmaStar M) j V ∂ valLaw M) *
              (1 + 11 * vt M ^ 2 * Real.log M.m / (M.m : ℝ) ^ (1 / vt M))) ∧
        IsEpsEquilibrium M alloc (sigmaStar M)
          (11 * vt M ^ 2 * Real.log M.m / (M.m : ℝ) ^ (1 / vt M)) := by
  obtain ⟨C5, hC5, h5⟩ := lemma_5
  obtain ⟨C16, hC16, h16⟩ := lemma_16
  obtain ⟨C17, hC17, h17⟩ := lemma_17
  have hCpos : 0 < min C5 (min C16 C17) := lt_min hC5 (lt_min hC16 hC17)
  refine ⟨min C5 (min C16 C17), hCpos, ?_⟩
  intro M hM alloc halloc hm1 hm2 hn
  have hϑ1 := one_le_vt M hM
  have hϑ0 := vt_pos M hM
  have hlogϑ : 0 ≤ Real.log (vt M) := Real.log_nonneg hϑ1
  have hm2' : Real.exp (3 * vt M + 1) ≤ (M.m : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by nlinarith)) hm2
  have hm4 : Real.exp 4 ≤ (M.m : ℝ) := le_trans (Real.exp_le_exp.mpr (by linarith)) hm2'
  have hm5 : (5 : ℝ) ≤ M.m := le_trans (by linarith [Real.add_one_le_exp 4]) hm4
  have hm0 : (0 : ℝ) < M.m := by linarith
  have hmNat : 2 ≤ M.m := by
    have : (2 : ℝ) ≤ M.m := by linarith
    exact_mod_cast this
  have hL : 3 * vt M + 1 ≤ Real.log M.m := (Real.le_log_iff_exp_le hm0).mpr hm2'
  have hL0 : 0 < Real.log M.m := by linarith
  have hN : 0 ≤ 6 * vt M * (M.m : ℝ) ^ (2 * (vt M + 1 / vt M)) * Real.log M.m :=
    mul_nonneg (by positivity) hL0.le
  have hnC : ∀ C', min C5 (min C16 C17) ≤ C' →
      6 * vt M * (M.m : ℝ) ^ (2 * (vt M + 1 / vt M)) * Real.log M.m / C' ≤ (M.n : ℝ) :=
    fun C' hC' => le_trans (div_le_div_of_nonneg_left hN hCpos hC') hn
  have hn5 := hnC C5 (min_le_left _ _)
  have hn16 := hnC C16 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hn17 := hnC C17 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hBs : ∀ k v, 0 ≤ ((sigmaStar M) k).budget v := fun k v => Bstar_nonneg M hM hmNat k v
  have hPs := profMeas_sigmaStar M hM
  have key : ∀ (j : Fin M.m) (σj : Strategy M.n), σj.Admissible →
      ∫ V, payoff M alloc (deviate (sigmaStar M) j σj) j V ∂ valLaw M ≤
        (∫ V, payoff M alloc (sigmaStar M) j V ∂ valLaw M) *
          (1 + 11 * vt M ^ 2 * Real.log M.m / (M.m : ℝ) ^ (1 / vt M)) := by
    intro j σj hσj
    obtain ⟨h17a, h17b⟩ := h17 M hM alloc halloc hm1 hm2' hn17 j
    have h16' := h16 M hM alloc halloc hm1 hm2' hn16 j
    have h5' := h5 M hM alloc halloc hm1 hm2' hn5 j σj hσj
    obtain ⟨hBint, hBeq⟩ := Bstar_tower M hM j
    have hOs : ∀ l, l ≠ j → sigmaStar M l = sigmaStar M l := fun _ _ => rfl
    have hModInt := integrable_modProfit M hM halloc hPs hBs j hOs
    have hSpInt := integrable_spend M hM halloc hPs hBs j hOs
    have hpe : (fun V => payoff M alloc (sigmaStar M) j V) = fun V =>
        modProfit M alloc (sigmaStar M) j V -
          M.r j * (Bstar M j (V j) - spend M alloc (sigmaStar M) j V) := by
      funext V
      have : modProfit M alloc (sigmaStar M) j V = payoff M alloc (sigmaStar M) j V +
          M.r j * (Bstar M j (V j) - spend M alloc (sigmaStar M) j V) := rfl
      linarith
    have hPi : ∫ V, payoff M alloc (sigmaStar M) j V ∂ valLaw M =
        (∫ V, modProfit M alloc (sigmaStar M) j V ∂ valLaw M) -
          M.r j * ((∫ V, PsiBar M j V ∂ valLaw M) * (1 + EndogBudgetAds.Equilibrium.beta M) -
            ∫ V, spend M alloc (sigmaStar M) j V ∂ valLaw M) := by
      have hI2 : Integrable (fun V : Valuations M =>
          M.r j * (Bstar M j (V j) - spend M alloc (sigmaStar M) j V)) (valLaw M) :=
        (hBint.sub hSpInt).const_mul _
      rw [hpe, integral_sub hModInt hI2, integral_const_mul,
        integral_sub hBint hSpInt, hBeq]
    have hMs : 0 ≤ ∫ V, modProfit M alloc (sigmaStar M) j V ∂ valLaw M := by
      refine le_trans (mul_nonneg ?_ (Finset.sum_nonneg fun i _ => measureReal_nonneg)) h17a
      have := hM.r_nonneg j
      have := lt_of_lt_of_le hM.θmin_pos hM.θmin_le_θmax
      positivity
    have hP : 0 ≤ ∫ V, PsiBar M j V ∂ valLaw M := by
      obtain ⟨l0, hl0⟩ := exists_other M hmNat j
      refine integral_nonneg_of_ae ?_
      filter_upwards [ae_nonneg_valLaw M hM] with V hV
      exact PsiBar_nonneg M j V l0 hl0 fun l _ i => W_nonneg M hM V l i (hV l i)
    obtain ⟨hx5, hγ⟩ := size_bounds (vt M) M.m hϑ1 hm2
    have fin := final_arith (∫ V, modProfit M alloc (sigmaStar M) j V ∂ valLaw M)
      (∫ V, PsiBar M j V ∂ valLaw M) (∫ V, spend M alloc (sigmaStar M) j V ∂ valLaw M)
      (∫ V, payoff M alloc (sigmaStar M) j V ∂ valLaw M)
      (∫ V, modProfit M alloc (deviate (sigmaStar M) j σj) j V ∂ valLaw M)
      (M.r j) (EndogBudgetAds.Equilibrium.beta M) ((M.m : ℝ) ^ (1 / vt M)) (vt M)
      (Real.log M.m) (vt M ^ 2 * Real.log M.m / (M.m : ℝ) ^ (1 / vt M))
      (3 * vt M / (M.m : ℝ) ^ (3 * vt M / 2))
      (hM.r_nonneg j) hP hϑ1 (Real.rpow_pos_of_pos hm0 _) hL0 rfl rfl hx5 hγ hPi h16'
      (le_trans h17b h17a) hMs h5'
    have e : 11 * vt M ^ 2 * Real.log M.m / (M.m : ℝ) ^ (1 / vt M) =
        11 * (vt M ^ 2 * Real.log M.m / (M.m : ℝ) ^ (1 / vt M)) := by ring
    rw [e]
    have hBd : ∀ k v, 0 ≤ ((deviate (sigmaStar M) j σj) k).budget v := by
      intro k v
      by_cases hk : k = j
      · subst hk; simp only [deviate, Function.update_self]; exact hσj.2.2 v
      · simp only [deviate, Function.update_of_ne hk]; exact hBs k v
    have hOd : ∀ l, l ≠ j → deviate (sigmaStar M) j σj l = sigmaStar M l :=
      fun l hl => Function.update_of_ne hl _ _
    have hPd := profMeas_deviate hPs j σj ⟨hσj.1, hσj.2.1⟩
    by_cases hint : Integrable (fun V => payoff M alloc (deviate (sigmaStar M) j σj) j V)
      (valLaw M)
    · have hmono : ∫ V, payoff M alloc (deviate (sigmaStar M) j σj) j V ∂ valLaw M ≤
          ∫ V, modProfit M alloc (deviate (sigmaStar M) j σj) j V ∂ valLaw M :=
        integral_mono hint (integrable_modProfit M hM halloc hPd hBd j hOd)
          (fun V => payoff_le_mod M hM halloc hBd j V)
      linarith [fin.1]
    · rw [integral_undef hint]; exact fin.2
  exact ⟨key, fun j σj hσj => key j σj hσj⟩
