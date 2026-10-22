-- Prove2me | solution 1 for ComplementsRev.Approx.proposition_5_10
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T15:20:13.183047+00:00
-- url     : https://prove2.me/submissions/266d2c48-75f1-4588-acd4-e70d71dc9f7f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ComplementsRev_Approx_Setting
import Theorems.Thm_ComplementsRev_Approx_lemma_5_1
import Theorems.Thm_ComplementsRev_Approx_proposition_5_5
import Theorems.Thm_ComplementsRev_Approx_proposition_5_7

open ComplementsRev.Approx

namespace CRP510

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
lemma brev_cutoff (P : Population ι) (t : ℝ) (ht : 0 ≤ t) :
    t * (1 - Real.exp (-(∑ T : Finset ι, P.Pr (fun w => t < w T)))) ≤ BREV P := by
  refine le_trans ?_ (brev_ge P t)
  refine mul_le_mul_of_nonneg_left (le_trans (Pr_exists_ge P t) ?_) ht
  refine Pr_mono P _ _ (fun w hw => ?_)
  rintro ⟨T, hT⟩
  have hTC : T ∈ P.C := by
    by_contra hn
    have h0 : w T ∈ ({0} : Finset ℝ) := by
      rw [← P.zero_off_C T hn]; exact mem_supp P hw T
    rw [Finset.mem_singleton.mp h0] at hT
    linarith
  exact le_trans (le_of_lt hT) (val_ge P hw hTC)

lemma brev_exists (P : Population ι) (t : ℝ) (ht : 0 ≤ t) :
    t * P.Pr (fun w => ∃ T, t < w T) ≤ BREV P := by
  refine le_trans ?_ (brev_ge P t)
  refine mul_le_mul_of_nonneg_left ?_ ht
  refine Pr_mono P _ _ (fun w hw => ?_)
  rintro ⟨T, hT⟩
  have hTC : T ∈ P.C := by
    by_contra hn
    have h0 : w T ∈ ({0} : Finset ℝ) := by
      rw [← P.zero_off_C T hn]; exact mem_supp P hw T
    rw [Finset.mem_singleton.mp h0] at hT
    linarith
  exact le_trans (le_of_lt hT) (val_ge P hw hTC)

lemma exists_cutoff (P : Population ι) (k : ℝ) (hk : 0 ≤ k) :
    ∃ t : ℝ, 0 ≤ t ∧ (∑ T : Finset ι, P.Pr (fun w => t < w T)) ≤ k ∧
      t * (1 - Real.exp (-k)) ≤ BREV P := by
  classical
  set g : ℝ → ℝ := fun t => ∑ T : Finset ι, P.Pr (fun w => t < w T) with hg
  set Y : Finset ℝ := insert 0 (Finset.univ.biUnion P.supp) with hY
  have hsuppY : ∀ T, ∀ y ∈ P.supp T, y ∈ Y := by
    intro T y hy
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨T, Finset.mem_univ _, hy⟩)
  have h0Y : (0 : ℝ) ∈ Y := Finset.mem_insert_self _ _
  set M := Y.max' ⟨0, h0Y⟩ with hM
  have hM0 : 0 ≤ M := Y.le_max' 0 h0Y
  have hgM : g M = 0 := by
    simp only [hg]
    refine Finset.sum_eq_zero (fun T _ => ?_)
    rw [Pr_marg]
    refine Finset.sum_eq_zero (fun y hy => ?_)
    have : y ≤ M := Y.le_max' y (hsuppY T y hy)
    simp [not_lt.mpr this]
  set G := Y.filter (fun c => 0 ≤ c ∧ g c ≤ k) with hG
  have hMG : M ∈ G := Finset.mem_filter.mpr ⟨Y.max'_mem _, hM0, by rw [hgM]; exact hk⟩
  set ts := G.min' ⟨M, hMG⟩ with hts
  have htsG : ts ∈ G := G.min'_mem _
  obtain ⟨_, hts0, htsk⟩ := Finset.mem_filter.mp htsG
  have hkey : ∀ s, 0 ≤ s → s < ts → s * (1 - Real.exp (-k)) ≤ BREV P := by
    intro s hs0 hsts
    have h0f : (0 : ℝ) ∈ Y.filter (· ≤ s) := Finset.mem_filter.mpr ⟨h0Y, hs0⟩
    set c := (Y.filter (· ≤ s)).max' ⟨0, h0f⟩ with hc
    have hcmem := (Y.filter (· ≤ s)).max'_mem ⟨0, h0f⟩
    rw [← hc] at hcmem
    obtain ⟨hcY, hcs⟩ := Finset.mem_filter.mp hcmem
    have hc0 : 0 ≤ c := (Y.filter (· ≤ s)).le_max' 0 h0f
    have hgc : k < g c := by
      by_contra hn
      have hcG : c ∈ G := Finset.mem_filter.mpr ⟨hcY, hc0, le_of_not_gt hn⟩
      have := G.min'_le c hcG
      rw [← hts] at this
      linarith
    have hiff : ∀ w ∈ P.profiles, ((∃ T, c < w T) ↔ (∃ T, s < w T)) := by
      intro w hw
      constructor
      · rintro ⟨T, hT⟩
        refine ⟨T, ?_⟩
        by_contra hn
        have hle : w T ≤ s := le_of_not_gt hn
        have : w T ≤ c := (Y.filter (· ≤ s)).le_max' (w T)
          (Finset.mem_filter.mpr ⟨hsuppY T _ (mem_supp P hw T), hle⟩)
        linarith
      · rintro ⟨T, hT⟩; exact ⟨T, lt_of_le_of_lt hcs hT⟩
    have hPr := Pr_congr P _ _ hiff
    have h1 := Pr_exists_ge P c
    have h2 : Real.exp (-(g c)) ≤ Real.exp (-k) := Real.exp_le_exp.mpr (by linarith)
    have h3 := brev_exists P s hs0
    rw [← hPr] at h3
    have h4 : 1 - Real.exp (-k) ≤ P.Pr (fun w => ∃ T, c < w T) := by
      simp only [hg] at h2
      linarith
    exact le_trans (mul_le_mul_of_nonneg_left h4 hs0) h3
  refine ⟨ts, hts0, htsk, ?_⟩
  by_contra hcon
  push_neg at hcon
  have ha : 0 < 1 - Real.exp (-k) ∨ 1 - Real.exp (-k) ≤ 0 := lt_or_ge _ _
  rcases ha with ha | ha
  · have hB0 := brev_nonneg P
    have : BREV P / (1 - Real.exp (-k)) < ts := by
      rw [div_lt_iff₀ ha]; exact hcon
    obtain ⟨s, hs1, hs2⟩ := exists_between this
    have hs0 : 0 ≤ s := le_trans (div_nonneg hB0 ha.le) hs1.le
    have := hkey s hs0 hs2
    rw [div_lt_iff₀ ha] at hs1
    linarith
  · have : ts * (1 - Real.exp (-k)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hts0 ha
    linarith [brev_nonneg P]

lemma const_bound : 2 + 1 / Real.log 2 ≤ 4 * (1 - Real.exp (-2)) := by
  have hl := Real.log_two_gt_d9
  have he := Real.exp_one_gt_d9
  have hl0 : 0 < Real.log 2 := by linarith
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have he2 : 7.389 < Real.exp 2 := by rw [h2]; nlinarith
  have hinv : Real.exp (-2) = 1 / Real.exp 2 := by rw [Real.exp_neg]; ring
  have hE : Real.exp (-2) < 1 / 7.389 := by
    rw [hinv]; exact one_div_lt_one_div_of_lt (by norm_num) he2
  have hL : 1 / Real.log 2 < 1 / 0.6931471803 := one_div_lt_one_div_of_lt (by norm_num) hl
  have : (2:ℝ) + 1 / 0.6931471803 ≤ 4 * (1 - 1 / 7.389) := by norm_num
  linarith

end CRP510

open CRP510 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Population ι) (rk : Finset ι → ℕ)
    (hrk : Function.Injective rk) :
    NONFAV P rk ≤ 12 * BREV P := by
  obtain ⟨t, ht0, hg, hB⟩ := exists_cutoff P 2 (by norm_num)
  have h1 := lemma_5_1 P rk hrk t
  have h2 := proposition_5_5 P t ht0
  have h3 := proposition_5_7 P rk hrk t
  have hB0 := brev_nonneg P
  have h4 : (∑ T : Finset ι, P.Pr (fun w => t < w T)) * BREV P ≤ 2 * BREV P :=
    mul_le_mul_of_nonneg_right hg hB0
  have h5 : t * (2 + 1 / Real.log 2) ≤ t * (4 * (1 - Real.exp (-2))) :=
    mul_le_mul_of_nonneg_left const_bound ht0
  nlinarith
