-- Prove2me | solution 1 for ComplementsRev.Approx.proposition_5_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T15:25:52.14592+00:00
-- url     : https://prove2.me/submissions/8c436dd4-c7dd-484d-b832-7d98259fa88e

import Mathlib
import Definitions.Def_ComplementsRev_Approx_Setting

open ComplementsRev.Approx

namespace CRP57

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma mem_supp (P : Population ι) {w : Finset ι → ℝ} (hw : w ∈ P.profiles) (T : Finset ι) :
    w T ∈ P.supp T := Fintype.mem_piFinset.mp hw T

lemma w_nonneg (P : Population ι) {w : Finset ι → ℝ} (hw : w ∈ P.profiles) (T : Finset ι) :
    0 ≤ w T := P.supp_nonneg T (w T) (mem_supp P hw T)

lemma prob_nonneg (P : Population ι) {w : Finset ι → ℝ} (hw : w ∈ P.profiles) :
    0 ≤ P.prob w := by
  unfold Population.prob
  exact Finset.prod_nonneg (fun T _ => le_of_lt (P.f_pos T (w T) (mem_supp P hw T)))

lemma E_prod (P : Population ι) (h : Finset ι → ℝ → ℝ) :
    P.E (fun w => ∏ T, h T (w T)) = ∏ T, ∑ y ∈ P.supp T, P.f T y * h T y := by
  unfold Population.E Population.prob Population.profiles
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [← Finset.prod_mul_distrib]

lemma E_one (P : Population ι) : P.E (fun _ => 1) = 1 := by
  have := E_prod P (fun _ _ => 1)
  simp only [Finset.prod_const_one, mul_one] at this
  rw [this]
  exact Finset.prod_eq_one (fun T _ => P.f_sum T)

lemma E_marg (P : Population ι) (T0 : Finset ι) (h : ℝ → ℝ) :
    P.E (fun w => h (w T0)) = ∑ y ∈ P.supp T0, P.f T0 y * h y := by
  have := E_prod P (fun T y => if T = T0 then h y else 1)
  have e1 : (fun w : Finset ι → ℝ => ∏ T, (if T = T0 then h (w T) else 1)) =
      fun w => h (w T0) := by
    funext w
    rw [Finset.prod_ite_eq' Finset.univ T0 (fun T => h (w T))]
    simp
  have e2 : (∏ T, ∑ y ∈ P.supp T, P.f T y * (if T = T0 then h y else 1)) =
      ∑ y ∈ P.supp T0, P.f T0 y * h y := by
    have : ∀ T, (∑ y ∈ P.supp T, P.f T y * (if T = T0 then h y else 1)) =
        if T = T0 then ∑ y ∈ P.supp T0, P.f T0 y * h y else 1 := by
      intro T
      by_cases hT : T = T0
      · subst hT; simp
      · simp [hT, P.f_sum T]
    rw [Finset.prod_congr rfl (fun T _ => this T)]
    rw [Finset.prod_ite_eq' Finset.univ T0 (fun _ => ∑ y ∈ P.supp T0, P.f T0 y * h y)]
    simp
  rw [e1] at this
  rw [this, e2]

lemma E_sub (P : Population ι) (g h : (Finset ι → ℝ) → ℝ) :
    P.E (fun w => g w - h w) = P.E g - P.E h := by
  unfold Population.E
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun w _ => by ring)

lemma E_add (P : Population ι) (g h : (Finset ι → ℝ) → ℝ) :
    P.E g + P.E h = P.E (fun w => g w + h w) := by
  unfold Population.E
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => by ring)

lemma E_mono (P : Population ι) (g h : (Finset ι → ℝ) → ℝ)
    (hgh : ∀ w ∈ P.profiles, g w ≤ h w) : P.E g ≤ P.E h := by
  unfold Population.E
  exact Finset.sum_le_sum (fun w hw => mul_le_mul_of_nonneg_left (hgh w hw) (prob_nonneg P hw))

lemma Pr_mono (P : Population ι) (A B : (Finset ι → ℝ) → Prop)
    (hAB : ∀ w ∈ P.profiles, A w → B w) : P.Pr A ≤ P.Pr B := by
  unfold Population.Pr
  refine E_mono P _ _ (fun w hw => ?_)
  by_cases ha : A w
  · simp [ha, hAB w hw ha]
  · by_cases hb : B w <;> simp [ha, hb]

lemma Pr_congr (P : Population ι) (A B : (Finset ι → ℝ) → Prop)
    (hAB : ∀ w ∈ P.profiles, (A w ↔ B w)) : P.Pr A = P.Pr B :=
  le_antisymm (Pr_mono P A B (fun w hw h => (hAB w hw).mp h))
    (Pr_mono P B A (fun w hw h => (hAB w hw).mpr h))

lemma Pr_marg (P : Population ι) (T : Finset ι) (t : ℝ) :
    P.Pr (fun w => t < w T) = ∑ y ∈ P.supp T, P.f T y * (if t < y then 1 else 0) := by
  unfold Population.Pr
  exact E_marg P T (fun y => if t < y then 1 else 0)

/-- Lemma 5.9 / Corollary 5.9 core: probability some hyperedge exceeds t. -/
lemma Pr_exists_ge (P : Population ι) (t : ℝ) :
    1 - Real.exp (-(∑ T : Finset ι, P.Pr (fun w => t < w T))) ≤
      P.Pr (fun w => ∃ T, t < w T) := by
  -- complement
  have hc : P.Pr (fun w => ∃ T, t < w T) = 1 - P.Pr (fun w => ∀ T, w T ≤ t) := by
    unfold Population.Pr
    rw [eq_sub_iff_add_eq, E_add]
    rw [← E_one P]
    refine congrArg P.E (funext fun w => ?_)
    by_cases h : ∃ T, t < w T
    · have : ¬ ∀ T, w T ≤ t := by
        rintro hall; obtain ⟨T, hT⟩ := h; exact absurd (hall T) (not_le.mpr hT)
      simp [h, this, E_one]
    · have : ∀ T, w T ≤ t := by
        intro T; by_contra hn; exact h ⟨T, lt_of_not_ge hn⟩
      simp [h, this, E_one]
  have hall : P.Pr (fun w => ∀ T, w T ≤ t) =
      ∏ T, ∑ y ∈ P.supp T, P.f T y * (if y ≤ t then 1 else 0) := by
    unfold Population.Pr
    rw [← E_prod P (fun _ y => if y ≤ t then 1 else 0)]
    congr 1
    funext w
    rw [Finset.prod_boole]
    simp
  have hq : ∀ T, (∑ y ∈ P.supp T, P.f T y * (if y ≤ t then 1 else 0)) =
      1 - P.Pr (fun w => t < w T) := by
    intro T
    rw [Pr_marg]
    have hs : (∑ y ∈ P.supp T, P.f T y * (if y ≤ t then 1 else 0)) +
        (∑ y ∈ P.supp T, P.f T y * (if t < y then 1 else 0)) = ∑ y ∈ P.supp T, P.f T y := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases hy : y ≤ t
      · simp [hy, not_lt.mpr hy]
      · simp [hy, lt_of_not_ge hy]
    rw [P.f_sum T] at hs
    linarith
  have hq0 : ∀ T, 0 ≤ 1 - P.Pr (fun w => t < w T) := by
    intro T
    rw [← hq T]
    refine Finset.sum_nonneg (fun y hy => mul_nonneg (le_of_lt (P.f_pos T y hy)) ?_)
    split_ifs <;> norm_num
  have hprod : (∏ T : Finset ι, (1 - P.Pr (fun w => t < w T))) ≤
      Real.exp (-(∑ T : Finset ι, P.Pr (fun w => t < w T))) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod (fun T _ => hq0 T) (fun T _ => ?_)
    have := Real.add_one_le_exp (-(P.Pr (fun w => t < w T)))
    linarith
  rw [hc, hall, Finset.prod_congr rfl (fun T _ => hq T)]
  linarith

lemma val_ge (P : Population ι) {w : Finset ι → ℝ} (hw : w ∈ P.profiles) {T : Finset ι}
    (hT : T ∈ P.C) : w T ≤ val P w Finset.univ := by
  unfold val
  have hmem : T ∈ feasible P Finset.univ :=
    Finset.mem_filter.mpr ⟨hT, Finset.subset_univ T⟩
  refine le_trans ?_ (Finset.le_sup' (fun T => ∑ U ∈ T.powerset, w U) hmem)
  exact Finset.single_le_sum (f := fun U => w U) (fun U _ => w_nonneg P hw U)
    (Finset.mem_powerset_self T)

lemma brev_bdd (P : Population ι) :
    BddAbove (Set.range (fun p : ℝ => p * P.Pr (fun w => p ≤ val P w Finset.univ))) := by
  refine ⟨∑ w ∈ P.profiles, P.prob w * |val P w Finset.univ|, ?_⟩
  rintro _ ⟨p, rfl⟩
  simp only
  unfold Population.Pr Population.E
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun w hw => ?_)
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (prob_nonneg P hw)
  by_cases h : p ≤ val P w Finset.univ
  · simp only [h, if_true, mul_one]; exact le_trans h (le_abs_self _)
  · simp only [h, if_false, mul_zero]; exact abs_nonneg _

lemma brev_ge (P : Population ι) (p : ℝ) :
    p * P.Pr (fun w => p ≤ val P w Finset.univ) ≤ BREV P :=
  le_csSup (brev_bdd P) ⟨p, rfl⟩

lemma brev_nonneg (P : Population ι) : 0 ≤ BREV P := by
  have := brev_ge P 0
  simpa using this

/-- Corollary 5.9 (general form). -/

lemma E_sum (P : Population ι) {α : Type*} (s : Finset α) (g : α → (Finset ι → ℝ) → ℝ) :
    P.E (fun w => ∑ a ∈ s, g a w) = ∑ a ∈ s, P.E (g a) := by
  unfold Population.E
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

lemma update_mem (P : Population ι) {w : Finset ι → ℝ} (hw : w ∈ P.profiles) (T : Finset ι)
    {y : ℝ} (hy : y ∈ P.supp T) : Function.update w T y ∈ P.profiles := by
  unfold Population.profiles
  rw [Fintype.mem_piFinset]
  intro U
  by_cases hU : U = T
  · subst hU; simpa using hy
  · rw [Function.update_of_ne hU]; exact mem_supp P hw U

lemma prob_update (P : Population ι) (w : Finset ι → ℝ) (T : Finset ι) (y : ℝ) :
    P.prob (Function.update w T y) * P.f T (w T) = P.prob w * P.f T y := by
  unfold Population.prob
  have h1 : (∏ U : Finset ι, P.f U (Function.update w T y U)) =
      P.f T y * ∏ U ∈ Finset.univ \ {T}, P.f U (w U) := by
    have : (fun U => P.f U (Function.update w T y U)) =
        Function.update (fun U => P.f U (w U)) T (P.f T y) := by
      funext U
      exact Function.apply_update (fun U => P.f U) w T y U
    rw [this, Finset.prod_update_of_mem (Finset.mem_univ T)]
  have h2 : (∏ U : Finset ι, P.f U (w U)) =
      P.f T (w T) * ∏ U ∈ Finset.univ \ {T}, P.f U (w U) := by
    exact Finset.prod_eq_mul_prod_diff_singleton T _ (fun h => absurd (Finset.mem_univ T) h)
  rw [h1, h2]; ring

/-- Independence of coordinate `T` from the others. -/
lemma E_indep (P : Population ι) (T : Finset ι) (F : ℝ → (Finset ι → ℝ) → ℝ)
    (hF : ∀ y z w, F y (Function.update w T z) = F y w) :
    P.E (fun w => F (w T) w) = ∑ y ∈ P.supp T, P.f T y * P.E (F y) := by
  unfold Population.E
  -- RHS as a double sum over profiles × supp T
  have hR : (∑ y ∈ P.supp T, P.f T y * ∑ w ∈ P.profiles, P.prob w * F y w) =
      ∑ p ∈ P.profiles ×ˢ P.supp T, P.prob p.1 * P.f T p.2 * F p.2 p.1 := by
    rw [Finset.sum_product_right]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w _ => by ring)
  have hL : (∑ w ∈ P.profiles, P.prob w * F (w T) w) =
      ∑ p ∈ P.profiles ×ˢ P.supp T, P.prob p.1 * P.f T p.2 * F (p.1 T) p.1 := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    dsimp only
    rw [← Finset.sum_mul, ← Finset.mul_sum, P.f_sum T]
    ring
  rw [hL, hR]
  refine Finset.sum_nbij' (fun p => (Function.update p.1 T p.2, p.1 T))
    (fun p => (Function.update p.1 T p.2, p.1 T)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    exact Finset.mem_product.mpr ⟨update_mem P h1 T h2, mem_supp P h1 T⟩
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    exact Finset.mem_product.mpr ⟨update_mem P h1 T h2, mem_supp P h1 T⟩
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    dsimp only
    rw [hF, prob_update]

end CRP57

open CRP57 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Population ι) (rk : Finset ι → ℕ)
    (hrk : Function.Injective rk) (t : ℝ) :
    TAIL P rk t ≤
      (∑ T : Finset ι, P.Pr (fun w => t < w T)) * BREV P := by
  classical
  have hB0 := brev_nonneg P
  unfold TAIL
  rw [E_sum, Finset.sum_mul]
  refine Finset.sum_le_sum (fun T _ => ?_)
  set F : ℝ → (Finset ι → ℝ) → ℝ := fun y w =>
    y * (if t < y then 1 else 0) * (if (∃ T', T' ≠ T ∧ y ≤ w T') then 1 else 0) with hFdef
  have hFinv : ∀ y z w, F y (Function.update w T z) = F y w := by
    intro y z w
    have key : (∃ T', T' ≠ T ∧ y ≤ Function.update w T z T') ↔ (∃ T', T' ≠ T ∧ y ≤ w T') :=
      ⟨fun ⟨T', h1, h2⟩ => ⟨T', h1, by rwa [Function.update_of_ne h1] at h2⟩,
       fun ⟨T', h1, h2⟩ => ⟨T', h1, by rwa [Function.update_of_ne h1]⟩⟩
    simp only [hFdef, key]
  have hpt : ∀ w ∈ P.profiles,
      (if t < w T ∧ ¬ InRegion rk w T then w T else 0) ≤ F (w T) w := by
    intro w hw
    have hw0 := w_nonneg P hw T
    have hRnn : 0 ≤ F (w T) w := by
      simp only [hFdef]
      refine mul_nonneg (mul_nonneg hw0 ?_) ?_ <;> split_ifs <;> norm_num
    by_cases hc : t < w T ∧ ¬ InRegion rk w T
    · rw [if_pos hc]
      by_cases hT : T.Nonempty
      · have hex : ∃ T', T' ≠ T ∧ w T ≤ w T' := by
          by_contra hn
          apply hc.2
          refine ⟨hT, fun T' _ hne => Or.inl ?_⟩
          by_contra hle
          exact hn ⟨T', hne, le_of_not_gt hle⟩
        simp only [hFdef, if_pos hc.1, if_pos hex]
        simp
      · have hT0 : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
        have : w T = 0 := by
          have h := mem_supp P hw T
          rw [hT0, P.zero_empty] at h
          rw [hT0]; exact Finset.mem_singleton.mp h
        rw [this]
        rw [this] at hRnn
        exact hRnn
    · rw [if_neg hc]; exact hRnn
  have hEF : ∀ y ∈ P.supp T, P.E (F y) ≤ (if t < y then 1 else 0) * BREV P := by
    intro y hy
    have hy0 := P.supp_nonneg T y hy
    have hE : P.E (F y) = y * (if t < y then 1 else 0) *
        P.Pr (fun w => ∃ T', T' ≠ T ∧ y ≤ w T') := by
      unfold Population.Pr Population.E
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      simp only [hFdef]; split_ifs <;> ring
    rw [hE]
    by_cases hty : t < y
    · simp only [if_pos hty, mul_one, one_mul]
      rcases eq_or_lt_of_le hy0 with h0 | hpos
      · rw [← h0]; simp [hB0]
      · refine le_trans (mul_le_mul_of_nonneg_left ?_ hy0) (brev_ge P y)
        refine Pr_mono P _ _ (fun w hw => ?_)
        rintro ⟨T', _, hT'⟩
        have hTC : T' ∈ P.C := by
          by_contra hn
          have h0 : w T' ∈ ({0} : Finset ℝ) := by
            rw [← P.zero_off_C T' hn]; exact mem_supp P hw T'
          rw [Finset.mem_singleton.mp h0] at hT'
          linarith
        exact le_trans hT' (val_ge P hw hTC)
    · simp [hty]
  calc P.E (fun w => if t < w T ∧ ¬ InRegion rk w T then w T else 0)
      ≤ P.E (fun w => F (w T) w) := E_mono P _ _ hpt
    _ = ∑ y ∈ P.supp T, P.f T y * P.E (F y) := E_indep P T F hFinv
    _ ≤ ∑ y ∈ P.supp T, P.f T y * ((if t < y then 1 else 0) * BREV P) :=
        Finset.sum_le_sum (fun y hy =>
          mul_le_mul_of_nonneg_left (hEF y hy) (le_of_lt (P.f_pos T y hy)))
    _ = P.Pr (fun w => t < w T) * BREV P := by
        rw [Pr_marg, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun y _ => by ring)
