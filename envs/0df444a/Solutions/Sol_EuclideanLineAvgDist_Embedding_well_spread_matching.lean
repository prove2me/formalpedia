-- Prove2me | solution 1 for EuclideanLineAvgDist.Embedding.well_spread_matching
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:59:50.435535+00:00
-- url     : https://prove2.me/submissions/814583ee-4421-46fb-bae1-c50335d9948a

import Mathlib
import Definitions.Def_EuclideanLineAvgDist_Embedding_Basic
import Definitions.Def_EuclideanLineAvgDist_Embedding_Projection
import Definitions.Def_EuclideanLineAvgDist_Embedding_Markov
import Theorems.Thm_EuclideanLineAvgDist_Embedding_gaussian_transition_bound

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Gaussian1

open EuclideanLineAvgDist.Embedding

/-- The law of `⟨γ, v⟩` for `γ ∼ N(0, I)` is `N(0, ‖v‖²)`. -/
lemma map_inner_stdGaussian (k : ℕ) (v : Eucl k) :
    (stdGaussian (Eucl k)).map (fun g => inner ℝ g v) = gaussianReal 0 (‖v‖₊ ^ 2) := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian (Eucl k)) (innerSL ℝ v)
  have e1 : ((innerSL ℝ v : Eucl k → ℝ)) = fun g => inner ℝ g v := by
    funext g; simp [real_inner_comm]
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian] at h
  simp only [innerSL_apply_norm] at h
  have : (‖v‖ ^ 2).toNNReal = ‖v‖₊ ^ 2 := by
    rw [← NNReal.coe_inj]; simp
  rw [this] at h
  rw [← h, e1]

end EuclideanLineAvgDist.Dev.Gaussian1
end

section
open scoped BigOperators ENNReal Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Well1

open EuclideanLineAvgDist.Embedding

noncomputable section


variable {k : ℕ} (X : Finset (Eucl k)) (tie : X → ℕ) (g : Eucl k)

lemma prec_trans {x y z : X} (h1 : Precedes X tie g x y) (h2 : Precedes X tie g y z) :
    Precedes X tie g x z := by
  unfold Precedes at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (h1.trans h2)
  · exact Or.inl (h2 ▸ h1)
  · exact Or.inl (h1 ▸ h2)
  · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩

lemma prec_irrefl (x : X) : ¬ Precedes X tie g x x := by
  unfold Precedes
  rintro (h | ⟨_, h⟩) <;> exact lt_irrefl _ h

lemma prec_total (hT : Function.Injective tie) {x y : X} (h : x ≠ y) :
    Precedes X tie g x y ∨ Precedes X tie g y x := by
  unfold Precedes
  have ht : tie x ≠ tie y := fun e => h (hT e)
  rcases lt_trichotomy (inner ℝ (x : Eucl k) g) (inner ℝ (y : Eucl k) g) with h1 | h1 | h1
  · exact Or.inl (Or.inl h1)
  · rcases lt_or_gt_of_ne ht with h2 | h2
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · exact Or.inr (Or.inr ⟨h1.symm, h2⟩)
  · exact Or.inr (Or.inl h1)

lemma prec_inner_le {x y : X} (h : Precedes X tie g x y) :
    inner ℝ (x : Eucl k) g ≤ inner ℝ (y : Eucl k) g := by
  rcases h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

lemma projRank_lt_of_prec {x y : X} (h : Precedes X tie g x y) :
    projRank X tie g x < projRank X tie g y := by
  unfold projRank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨x, ?_, ?_⟩
    · simpa using h
    · simpa using prec_irrefl X tie g x
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact prec_trans X tie g hz h

lemma projRank_lt_card (x : X) : projRank X tie g x < X.card := by
  unfold projRank
  have : (Finset.univ.filter (fun y : X => Precedes X tie g y x)).card < (Finset.univ : Finset X).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
    exact ⟨x, by simp, by simpa using prec_irrefl X tie g x⟩
  simpa using this

lemma projRank_injective (hT : Function.Injective tie) : Function.Injective (projRank X tie g) := by
  intro x y hxy
  by_contra h
  rcases prec_total X tie g hT h with h1 | h1
  · exact absurd hxy (projRank_lt_of_prec X tie g h1).ne
  · exact absurd hxy (projRank_lt_of_prec X tie g h1).ne'

lemma image_projRank (hT : Function.Injective tie) :
    (Finset.univ : Finset X).image (projRank X tie g) = Finset.range X.card := by
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hi
    exact Finset.mem_range.2 (projRank_lt_card X tie g x)
  · rw [Finset.card_image_of_injective _ (projRank_injective X tie g hT)]
    simp

lemma extremeCount_ge (n : ℕ) : (n : ℝ) / 64 ≤ extremeCount n := Nat.le_ceil _

lemma extremeCount_lt (n : ℕ) : (extremeCount n : ℝ) < (n : ℝ) / 64 + 1 := Nat.ceil_lt_add_one (by positivity)

lemma two_mul_extremeCount_le {n : ℕ} (hn : 64 < n) : 2 * extremeCount n ≤ n := by
  have h := extremeCount_lt n
  have hn' : (64 : ℝ) < n := by exact_mod_cast hn
  have : (2 * extremeCount n : ℝ) ≤ n := by linarith
  exact_mod_cast this

lemma four_mul_extremeCount_lt {n : ℕ} (hn : 64 < n) : 4 * (extremeCount n : ℝ) < n / 8 := by
  have h := extremeCount_lt n
  have hn' : (64 : ℝ) < n := by exact_mod_cast hn
  linarith

lemma card_lowSet (hT : Function.Injective tie) (hn : 64 < X.card) :
    (lowSet X tie g).card = extremeCount X.card := by
  have hm := two_mul_extremeCount_le hn
  have : (lowSet X tie g).image (projRank X tie g) = Finset.range (extremeCount X.card) := by
    ext i
    simp only [Finset.mem_image, lowSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hi
      have : i ∈ (Finset.univ : Finset X).image (projRank X tie g) := by
        rw [image_projRank X tie g hT]; simp; omega
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 this
      exact ⟨x, hi, rfl⟩
  rw [← Finset.card_image_of_injective _ (projRank_injective X tie g hT), this]
  simp

lemma card_highSet (hT : Function.Injective tie) (hn : 64 < X.card) :
    (highSet X tie g).card = extremeCount X.card := by
  have hm := two_mul_extremeCount_le hn
  have : (highSet X tie g).image (projRank X tie g) = Finset.Ico (X.card - extremeCount X.card) X.card := by
    ext i
    simp only [Finset.mem_image, highSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ico]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨hx, projRank_lt_card X tie g x⟩
    · intro hi
      have : i ∈ (Finset.univ : Finset X).image (projRank X tie g) := by
        rw [image_projRank X tie g hT]; simp; omega
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 this
      exact ⟨x, hi.1, rfl⟩
  rw [← Finset.card_image_of_injective _ (projRank_injective X tie g hT), this]
  simp
  omega

lemma disjoint_low_high (hn : 64 < X.card) : Disjoint (lowSet X tie g) (highSet X tie g) := by
  have hm := two_mul_extremeCount_le hn
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [lowSet, highSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  omega

/-- Points outside both extreme sets lie between every low and every high point. -/
lemma inner_low_le {x a : X} (hT : Function.Injective tie) (hn : 64 < X.card)
    (ha : a ∈ lowSet X tie g) (hx : x ∉ lowSet X tie g) :
    inner ℝ (a : Eucl k) g ≤ inner ℝ (x : Eucl k) g := by
  have hm := two_mul_extremeCount_le hn
  simp only [lowSet, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at ha hx
  have hne : a ≠ x := by rintro rfl; omega
  rcases prec_total X tie g hT hne with h | h
  · exact prec_inner_le X tie g h
  · have := projRank_lt_of_prec X tie g h; omega

lemma inner_le_high {x b : X} (hT : Function.Injective tie) (hn : 64 < X.card)
    (hb : b ∈ highSet X tie g) (hx : x ∉ highSet X tie g) :
    inner ℝ (x : Eucl k) g ≤ inner ℝ (b : Eucl k) g := by
  simp only [highSet, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hb hx
  have hne : x ≠ b := by rintro rfl; omega
  rcases prec_total X tie g hT hne with h | h
  · exact prec_inner_le X tie g h
  · have := projRank_lt_of_prec X tie g h; omega

end

end EuclideanLineAvgDist.Dev.Well1
end

section
open scoped BigOperators ENNReal Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Well2

open EuclideanLineAvgDist.Embedding

noncomputable section

variable {k : ℕ} {X : Finset (Eucl k)}

/-- A minimum matching `L ≃ H` exists and the sets are disjoint. -/
def HasMin (L H : Finset X) : Prop := Disjoint L H ∧ ∃ M : L ≃ H, IsMinMatching M

/-- The chosen minimum matching. -/
def chosenM (L H : Finset X) (h : HasMin L H) : L ≃ H := Classical.choose h.2

lemma chosenM_min (L H : Finset X) (h : HasMin L H) : IsMinMatching (chosenM L H h) :=
  Classical.choose_spec h.2

/-- The partner of `x`. -/
def pt (L H : Finset X) (x : X) : X :=
  if h : HasMin L H then
    (if hx : x ∈ L then ((chosenM L H h ⟨x, hx⟩ : H) : X)
      else if hx : x ∈ H then (((chosenM L H h).symm ⟨x, hx⟩ : L) : X) else x)
  else x

lemma pt_of_not_hasMin {L H : Finset X} (h : ¬ HasMin L H) (x : X) : pt L H x = x := by
  simp [pt, h]

lemma pt_of_mem_low {L H : Finset X} (h : HasMin L H) {x : X} (hx : x ∈ L) :
    pt L H x = ((chosenM L H h ⟨x, hx⟩ : H) : X) := by
  simp [pt, h, hx]

lemma pt_of_mem_high {L H : Finset X} (h : HasMin L H) {x : X} (hx : x ∈ H) :
    pt L H x = (((chosenM L H h).symm ⟨x, hx⟩ : L) : X) := by
  have hxL : x ∉ L := fun h' => Finset.disjoint_left.1 h.1 h' hx
  simp [pt, h, hx, hxL]

lemma pt_of_not_mem {L H : Finset X} {x : X} (hL : x ∉ L) (hH : x ∉ H) : pt L H x = x := by
  by_cases h : HasMin L H
  · simp [pt, h, hL, hH]
  · exact pt_of_not_hasMin h x

lemma pt_mem_high {L H : Finset X} (h : HasMin L H) {x : X} (hx : x ∈ L) : pt L H x ∈ H := by
  rw [pt_of_mem_low h hx]; exact Subtype.mem _

lemma pt_mem_low {L H : Finset X} (h : HasMin L H) {x : X} (hx : x ∈ H) : pt L H x ∈ L := by
  rw [pt_of_mem_high h hx]; exact Subtype.mem _

lemma pt_pt (L H : Finset X) (x : X) : pt L H (pt L H x) = x := by
  by_cases h : HasMin L H
  · by_cases hxL : x ∈ L
    · have h1 := pt_mem_high h hxL
      rw [pt_of_mem_high h h1]
      simp only [pt_of_mem_low h hxL]
      simp
    · by_cases hxH : x ∈ H
      · have h1 := pt_mem_low h hxH
        rw [pt_of_mem_low h h1]
        simp only [pt_of_mem_high h hxH]
        simp
      · rw [pt_of_not_mem hxL hxH, pt_of_not_mem hxL hxH]
  · rw [pt_of_not_hasMin h, pt_of_not_hasMin h]

/-- `minMatchingCost` is the cost of the chosen matching. -/
lemma minMatchingCost_eq (L H : Finset X) (h : HasMin L H) :
    minMatchingCost L H = matchingCost (chosenM L H h) := by
  unfold minMatchingCost
  apply le_antisymm
  · exact ciInf_le ⟨0, by rintro _ ⟨M, rfl⟩; exact Finset.sum_nonneg (fun _ _ => dist_nonneg)⟩ _
  · have : Nonempty (L ≃ H) := ⟨chosenM L H h⟩
    exact le_ciInf (fun M => chosenM_min L H h M)

lemma sum_dist_pt (L H : Finset X) (h : HasMin L H) :
    ∑ x : X, dist x (pt L H x) = 2 * minMatchingCost L H := by
  rw [minMatchingCost_eq L H h]
  set M := chosenM L H h with hM
  have hsplit : ∑ x : X, dist x (pt L H x) = ∑ x ∈ L, dist x (pt L H x) + ∑ x ∈ H, dist x (pt L H x) := by
    have hsub : L ∪ H ⊆ (Finset.univ : Finset X) := Finset.subset_univ _
    rw [← Finset.sum_union h.1]
    symm
    apply Finset.sum_subset hsub
    intro x _ hx
    have : pt L H x = x := pt_of_not_mem (fun h' => hx (Finset.mem_union_left _ h'))
      (fun h' => hx (Finset.mem_union_right _ h'))
    simp [this]
  have hL : ∑ x ∈ L, dist x (pt L H x) = matchingCost M := by
    unfold matchingCost
    rw [← Finset.sum_coe_sort L]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [pt_of_mem_low h a.2]
  have hH : ∑ x ∈ H, dist x (pt L H x) = matchingCost M := by
    unfold matchingCost
    rw [← Finset.sum_coe_sort H]
    rw [← Equiv.sum_comp M (fun b : H => dist (b : X) (pt L H b))]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [pt_of_mem_high h (M a).2, ← hM]
    simp [dist_comm]
  rw [hsplit, hL, hH]; ring

/-- The weight `1/(1+d/s)`. -/
def wt (s : ℝ) (x y : X) : ℝ := 1 / (1 + dist x y / s)

lemma wt_pos {s : ℝ} (hs : 0 < s) (x y : X) : 0 < wt s x y := by
  unfold wt; have := dist_nonneg (x := x) (y := y); positivity

lemma wt_le_one {s : ℝ} (hs : 0 < s) (x y : X) : wt s x y ≤ 1 := by
  unfold wt
  have : 0 ≤ dist x y / s := by have := dist_nonneg (x := x) (y := y); positivity
  rw [div_le_one (by linarith)]; linarith

lemma wt_symm (s : ℝ) (x y : X) : wt s x y = wt s y x := by unfold wt; rw [dist_comm]

/-- The transition matrix. -/
def Kmat (s : ℝ) (L H : Finset X) (x y : X) : ℝ :=
  (if y = pt L H x ∧ x ≠ y then wt s x y else 0) +
    (if x = y then 1 - (if pt L H x ≠ x then wt s x (pt L H x) else 0) else 0)

lemma Kmat_symm (s : ℝ) (L H : Finset X) (x y : X) : Kmat s L H x y = Kmat s L H y x := by
  unfold Kmat
  by_cases hxy : x = y
  · subst hxy; rfl
  · have : (y = pt L H x) ↔ (x = pt L H y) := by
      constructor
      · intro h; rw [h, pt_pt]
      · intro h; rw [h, pt_pt]
    simp only [hxy, Ne.symm hxy, ne_eq, not_false_eq_true, and_true, if_false, add_zero, this,
      wt_symm s x y]

lemma Kmat_nonneg {s : ℝ} (hs : 0 < s) (L H : Finset X) (x y : X) : 0 ≤ Kmat s L H x y := by
  unfold Kmat
  have h1 : 0 ≤ (if y = pt L H x ∧ x ≠ y then wt s x y else 0) := by
    split_ifs
    · exact (wt_pos hs x y).le
    · exact le_refl _
  have h2 : 0 ≤ (if x = y then 1 - (if pt L H x ≠ x then wt s x (pt L H x) else 0) else 0) := by
    split_ifs
    · linarith [wt_le_one hs x (pt L H x)]
    · linarith
    · exact le_refl _
  linarith

lemma Kmat_sum {s : ℝ} (L H : Finset X) (x : X) : ∑ y, Kmat s L H x y = 1 := by
  unfold Kmat
  rw [Finset.sum_add_distrib]
  have h1 : ∑ y : X, (if y = pt L H x ∧ x ≠ y then wt s x y else 0) =
      (if pt L H x ≠ x then wt s x (pt L H x) else 0) := by
    by_cases hp : pt L H x = x
    · simp only [hp, ne_eq, not_true_eq_false, and_false, if_false, Finset.sum_const_zero]
      apply Finset.sum_eq_zero
      intro y _
      rw [if_neg]
      rintro ⟨h1, h2⟩; exact h2 h1.symm
    · rw [if_pos hp, Finset.sum_eq_single (pt L H x)]
      · rw [if_pos ⟨rfl, fun h => hp h.symm⟩]
      · intro y _ hy; rw [if_neg]; rintro ⟨h1, _⟩; exact hy h1
      · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1, Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  ring

/-- Key identity: `∑_y K x y φ(x,y) = wt(x, pt x) φ(x, pt x)` when `φ x x = 0`. -/
lemma Kmat_sum_mul {s : ℝ} (L H : Finset X) (φ : X → X → ℝ) (hφ : ∀ x, φ x x = 0) (x : X) :
    ∑ y, Kmat s L H x y * φ x y = wt s x (pt L H x) * φ x (pt L H x) := by
  unfold Kmat
  simp_rw [add_mul, Finset.sum_add_distrib]
  have h2 : ∑ y : X, (if x = y then 1 - (if pt L H x ≠ x then wt s x (pt L H x) else 0) else 0) * φ x y = 0 := by
    apply Finset.sum_eq_zero
    intro y _
    by_cases hxy : x = y
    · subst hxy; simp [hφ]
    · simp [hxy]
  rw [h2, add_zero]
  by_cases hp : pt L H x = x
  · have h0 : φ x (pt L H x) = 0 := by rw [hp]; exact hφ x
    rw [h0, mul_zero]
    apply Finset.sum_eq_zero
    intro y _
    by_cases h : y = pt L H x ∧ x ≠ y
    · exact absurd (h.1.trans hp).symm h.2
    · simp [h]
  · rw [Finset.sum_eq_single (pt L H x)]
    · rw [if_pos ⟨rfl, fun h => hp h.symm⟩]
    · intro y _ hy; rw [if_neg]; · simp
      rintro ⟨h1, _⟩; exact hy h1
    · intro h; exact absurd (Finset.mem_univ _) h

end

end EuclideanLineAvgDist.Dev.Well2
end

section
open scoped BigOperators ENNReal Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Well3

open EuclideanLineAvgDist.Embedding

noncomputable section

variable {k : ℕ} (X : Finset (Eucl k)) (tie : X → ℕ)

lemma measurableSet_precedes (x y : X) : MeasurableSet {g : Eucl k | Precedes X tie g x y} := by
  have h1 : MeasurableSet {g : Eucl k | inner ℝ (x : Eucl k) g < inner ℝ (y : Eucl k) g} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  have h2 : MeasurableSet {g : Eucl k | inner ℝ (x : Eucl k) g = inner ℝ (y : Eucl k) g} :=
    measurableSet_eq_fun (by fun_prop) (by fun_prop)
  have : {g : Eucl k | Precedes X tie g x y} = {g | inner ℝ (x : Eucl k) g < inner ℝ (y : Eucl k) g} ∪
      ({g | inner ℝ (x : Eucl k) g = inner ℝ (y : Eucl k) g} ∩ {_g | tie x < tie y}) := by
    ext g; simp [Precedes]
  rw [this]
  exact h1.union (h2.inter (MeasurableSet.const _))

lemma measurable_projRank (x : X) : Measurable fun g : Eucl k => projRank X tie g x := by
  have : (fun g : Eucl k => projRank X tie g x) =
      fun g => ∑ y : X, if Precedes X tie g y x then 1 else 0 := by
    funext g; unfold projRank; rw [Finset.card_filter]
  rw [this]
  refine Finset.measurable_sum _ (fun y _ => ?_)
  exact Measurable.ite (measurableSet_precedes X tie y x) measurable_const measurable_const

lemma measurableSet_mem_low (x : X) : MeasurableSet {g : Eucl k | x ∈ lowSet X tie g} := by
  have : {g : Eucl k | x ∈ lowSet X tie g} = {g | projRank X tie g x < extremeCount X.card} := by
    ext g; simp [lowSet]
  rw [this]
  exact measurableSet_lt (measurable_projRank X tie x) measurable_const

lemma measurableSet_mem_high (x : X) : MeasurableSet {g : Eucl k | x ∈ highSet X tie g} := by
  have : {g : Eucl k | x ∈ highSet X tie g} = {g | X.card - extremeCount X.card ≤ projRank X tie g x} := by
    ext g; simp [highSet]
  rw [this]
  exact measurableSet_le measurable_const (measurable_projRank X tie x)

lemma measurableSet_orderData (p : Finset X × Finset X) :
    MeasurableSet {g : Eucl k | lowSet X tie g = p.1 ∧ highSet X tie g = p.2} := by
  have hL : ∀ x : X, MeasurableSet {g : Eucl k | x ∈ lowSet X tie g ↔ x ∈ p.1} := by
    intro x
    by_cases hx : x ∈ p.1
    · simpa [hx] using measurableSet_mem_low X tie x
    · have e : {g : Eucl k | x ∈ lowSet X tie g ↔ x ∈ p.1} = {g : Eucl k | x ∈ lowSet X tie g}ᶜ := by
        ext g; simp [hx]
      rw [e]; exact (measurableSet_mem_low X tie x).compl
  have hH : ∀ x : X, MeasurableSet {g : Eucl k | x ∈ highSet X tie g ↔ x ∈ p.2} := by
    intro x
    by_cases hx : x ∈ p.2
    · simpa [hx] using measurableSet_mem_high X tie x
    · have e : {g : Eucl k | x ∈ highSet X tie g ↔ x ∈ p.2} = {g : Eucl k | x ∈ highSet X tie g}ᶜ := by
        ext g; simp [hx]
      rw [e]; exact (measurableSet_mem_high X tie x).compl
  have : {g : Eucl k | lowSet X tie g = p.1 ∧ highSet X tie g = p.2} =
      (⋂ x : X, {g | x ∈ lowSet X tie g ↔ x ∈ p.1}) ∩ ⋂ x : X, {g | x ∈ highSet X tie g ↔ x ∈ p.2} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.ext_iff]
  rw [this]
  exact (MeasurableSet.iInter hL).inter (MeasurableSet.iInter hH)

/-- Anything depending on `g` only through the order data (low/high sets) and measurably otherwise
is measurable. -/
lemma measurable_orderData (F : Finset X → Finset X → Eucl k → ℝ) (hF : ∀ L H, Measurable (F L H)) :
    Measurable (fun g => F (lowSet X tie g) (highSet X tie g) g) := by
  have : (fun g => F (lowSet X tie g) (highSet X tie g) g) = fun g =>
      ∑ p : Finset X × Finset X,
        if (lowSet X tie g = p.1 ∧ highSet X tie g = p.2) then F p.1 p.2 g else 0 := by
    funext g
    rw [Finset.sum_eq_single (lowSet X tie g, highSet X tie g)]
    · simp
    · intro p _ hp
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hp (Prod.ext h1.symm h2.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [this]
  exact Finset.measurable_sum _ (fun p _ =>
    Measurable.ite (measurableSet_orderData X tie p) (hF _ _) measurable_const)

end

end EuclideanLineAvgDist.Dev.Well3
end

section
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Well4

open EuclideanLineAvgDist.Embedding

noncomputable section

lemma integrable_abs_inner {k : ℕ} (v : Eucl k) :
    Integrable (fun g : Eucl k => |inner ℝ g v|) (stdGaussian (Eucl k)) := by
  have h1 : Integrable (fun x : ℝ => |x|) (gaussianReal 0 (‖v‖₊ ^ 2)) := by
    have := (memLp_id_gaussianReal (μ := (0:ℝ)) (v := ‖v‖₊ ^ 2) 1).integrable le_rfl
    simpa using this.abs
  rw [← Gaussian1.map_inner_stdGaussian k v] at h1
  exact (integrable_map_measure (by fun_prop) (by fun_prop)).1 h1

/-- Anti-concentration: if `‖v‖ ≥ 2a > 0` then `Pr(|⟨γ,v⟩| ≥ a) ≥ 1/2`. -/
lemma prob_abs_inner_ge {k : ℕ} (v : Eucl k) {a : ℝ} (ha : 0 < a) (hv : 2 * a ≤ ‖v‖) :
    1 / 2 ≤ (stdGaussian (Eucl k)).real {g | a ≤ |inner ℝ g v|} := by
  have hvpos : 0 < ‖v‖ := by linarith
  have hmeas : MeasurableSet {g : Eucl k | |inner ℝ g v| < a} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hcompl : {g : Eucl k | a ≤ |inner ℝ g v|} = {g : Eucl k | |inner ℝ g v| < a}ᶜ := by
    ext g; simp
  -- measure of the small set
  have hsmall : (stdGaussian (Eucl k)).real {g | |inner ℝ g v| < a} ≤ 2 / 5 := by
    have hpre : (stdGaussian (Eucl k)) {g : Eucl k | |inner ℝ g v| < a} =
        (gaussianReal 0 (‖v‖₊ ^ 2)) (Set.Ioo (-a) a) := by
      rw [← Gaussian1.map_inner_stdGaussian k v, Measure.map_apply (by fun_prop) measurableSet_Ioo]
      congr 1
      ext g; simp [abs_lt]
    have hvar : (‖v‖₊ ^ 2 : ℝ≥0) ≠ 0 := by
      have : (‖v‖₊ : ℝ≥0) ≠ 0 := by simpa using hvpos.ne'
      exact pow_ne_zero 2 this
    have hle : (gaussianReal 0 (‖v‖₊ ^ 2)) (Set.Ioo (-a) a) ≤
        ENNReal.ofReal ((√(2 * Real.pi * ((‖v‖₊ ^ 2 : ℝ≥0) : ℝ)))⁻¹ * (2 * a)) := by
      rw [gaussianReal_of_var_ne_zero _ hvar, withDensity_apply _ measurableSet_Ioo]
      calc ∫⁻ x in Set.Ioo (-a) a, gaussianPDF 0 (‖v‖₊ ^ 2) x
          ≤ ∫⁻ x in Set.Ioo (-a) a, ENNReal.ofReal ((√(2 * Real.pi * ((‖v‖₊ ^ 2 : ℝ≥0) : ℝ)))⁻¹) := by
            apply lintegral_mono
            intro x
            unfold gaussianPDF gaussianPDFReal
            apply ENNReal.ofReal_le_ofReal
            have : Real.exp (-(x - ((0:ℝ))) ^ 2 / (2 * ((‖v‖₊ ^ 2 : ℝ≥0) : ℝ))) ≤ 1 := by
              apply Real.exp_le_one_iff.2
              have : 0 ≤ (x - (0:ℝ)) ^ 2 / (2 * ((‖v‖₊ ^ 2 : ℝ≥0) : ℝ)) := by positivity
              have e : -(x - (0:ℝ)) ^ 2 / (2 * ((‖v‖₊ ^ 2 : ℝ≥0) : ℝ)) =
                  -((x - (0:ℝ)) ^ 2 / (2 * ((‖v‖₊ ^ 2 : ℝ≥0) : ℝ))) := by ring
              linarith
            have hp : 0 ≤ (√(2 * Real.pi * ((‖v‖₊ ^ 2 : ℝ≥0) : ℝ)))⁻¹ := by positivity
            calc _ ≤ (√(2 * Real.pi * ((‖v‖₊ ^ 2 : ℝ≥0) : ℝ)))⁻¹ * 1 := by gcongr
              _ = _ := mul_one _
        _ = ENNReal.ofReal ((√(2 * Real.pi * ((‖v‖₊ ^ 2 : ℝ≥0) : ℝ)))⁻¹) * ENNReal.ofReal (2 * a) := by
            rw [setLIntegral_const, Real.volume_Ioo]; congr 2; ring_nf
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
    have hcoe : ((‖v‖₊ ^ 2 : ℝ≥0) : ℝ) = ‖v‖ ^ 2 := by simp
    rw [hcoe] at hle
    have hsq : √(2 * Real.pi * ‖v‖ ^ 2) = √(2 * Real.pi) * ‖v‖ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hvpos.le]
    rw [hsq] at hle
    have h2 : (5 / 2 : ℝ) < √(2 * Real.pi) := by
      rw [Real.lt_sqrt (by norm_num)]; nlinarith [Real.pi_gt_d2]
    have hnum : (√(2 * Real.pi) * ‖v‖)⁻¹ * (2 * a) ≤ 2 / 5 := by
      rw [inv_mul_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul h2.le hv (by positivity) (by positivity)]
    unfold Measure.real
    rw [hpre]
    calc ((gaussianReal 0 (‖v‖₊ ^ 2)) (Set.Ioo (-a) a)).toReal
        ≤ (ENNReal.ofReal ((√(2 * Real.pi) * ‖v‖)⁻¹ * (2 * a))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ ≤ 2 / 5 := by
          rw [ENNReal.toReal_ofReal (by positivity)]; exact hnum
  rw [hcompl, probReal_compl_eq_one_sub hmeas]
  linarith

end

end EuclideanLineAvgDist.Dev.Well4
end

section
open scoped BigOperators ENNReal Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Well5

open EuclideanLineAvgDist.Embedding EuclideanLineAvgDist.Dev.Well2

noncomputable section

variable {k : ℕ} {X : Finset (Eucl k)}

/-- The displacement `pt x - x`. -/
def diff (L H : Finset X) (x : X) : Eucl k := ((pt L H x : X) : Eucl k) - (x : Eucl k)

/-- `T = ∑_x wt(x, pt x) |⟨g, pt x - x⟩|`. -/
def Tf (s : ℝ) (L H : Finset X) (g : Eucl k) : ℝ :=
  ∑ x : X, wt s x (pt L H x) * |inner ℝ g (diff L H x)|

/-- `V = ∑_x d(x, pt x)`. -/
def Vf (L H : Finset X) : ℝ := ∑ x : X, dist x (pt L H x)

/-- `N = ∑_{x ∈ L ∪ H} √|⟨g, pt x - x⟩|`. -/
def Nf (L H : Finset X) (g : Eucl k) : ℝ := ∑ x ∈ L ∪ H, √|inner ℝ g (diff L H x)|

/-- `U = ∑_{x ∈ L ∪ H} (1 + d(x, pt x)/s)`. -/
def Uf (s : ℝ) (L H : Finset X) : ℝ := ∑ x ∈ L ∪ H, (1 + dist x (pt L H x) / s)

/-- Number of pairs with large projected gap. -/
def Gf (Δ : ℝ) (g : Eucl k) : ℝ :=
  ∑ p : X × X, if Δ / 8 ≤ |inner ℝ g ((p.1 : Eucl k) - (p.2 : Eucl k))| then (1 : ℝ) else 0

/-- Number of such pairs avoiding `L ∪ H`. -/
def Ef (Δ : ℝ) (L H : Finset X) (g : Eucl k) : ℝ :=
  ∑ p : X × X, if (p.1 ∉ L ∪ H ∧ p.2 ∉ L ∪ H) then
      (if Δ / 8 ≤ |inner ℝ g ((p.1 : Eucl k) - (p.2 : Eucl k))| then (1 : ℝ) else 0) else 0

lemma norm_diff (L H : Finset X) (x : X) : ‖diff L H x‖ = dist x (pt L H x) := by
  unfold diff
  rw [dist_comm, Subtype.dist_eq, dist_eq_norm]

/-! ### Measurability of the order-data quantities -/

lemma measurable_Tf (s : ℝ) (L H : Finset X) : Measurable (Tf s L H) := by
  unfold Tf
  refine Finset.measurable_sum _ (fun x _ => ?_)
  fun_prop

lemma measurable_Nf (L H : Finset X) : Measurable (Nf L H) := by
  unfold Nf
  refine Finset.measurable_sum _ (fun x _ => ?_)
  fun_prop

lemma measurable_Ef (Δ : ℝ) (L H : Finset X) : Measurable (Ef Δ L H) := by
  unfold Ef
  refine Finset.measurable_sum _ (fun p _ => ?_)
  by_cases h : (p.1 ∉ L ∪ H ∧ p.2 ∉ L ∪ H)
  · simp only [if_pos h]
    exact Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_const measurable_const
  · simp only [if_neg h]
    exact measurable_const

end

end EuclideanLineAvgDist.Dev.Well5
end

section
open scoped BigOperators ENNReal Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Well6

open EuclideanLineAvgDist.Embedding EuclideanLineAvgDist.Dev.Well2 EuclideanLineAvgDist.Dev.Well5

noncomputable section

variable {k : ℕ} (X : Finset (Eucl k)) (tie : X → ℕ)

lemma hasMin_lowHigh (hT : Function.Injective tie) (hn : 64 < X.card) (g : Eucl k) :
    HasMin (lowSet X tie g) (highSet X tie g) := by
  refine ⟨Dev.Well1.disjoint_low_high X tie g hn, ?_⟩
  have hc : Fintype.card (lowSet X tie g) = Fintype.card (highSet X tie g) := by
    simp [Dev.Well1.card_lowSet X tie g hT hn, Dev.Well1.card_highSet X tie g hT hn]
  obtain ⟨e⟩ := Fintype.card_eq.1 hc
  have : Nonempty ((lowSet X tie g) ≃ (highSet X tie g)) := ⟨e⟩
  obtain ⟨M, hM⟩ := Finite.exists_min (fun M : (lowSet X tie g) ≃ (highSet X tie g) => matchingCost M)
  exact ⟨M, hM⟩

variable {X}

lemma sum_K_proj (s : ℝ) (L H : Finset X) (g : Eucl k) :
    ∑ x : X, ∑ y : X, Kmat s L H x y * |inner ℝ g ((y : Eucl k) - (x : Eucl k))| = Tf s L H g := by
  unfold Tf
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Kmat_sum_mul L H (fun x y => |inner ℝ g ((y : Eucl k) - (x : Eucl k))|) (by intro x; simp)]
  rfl

lemma sum_K_sq_le {s : ℝ} (hs : 0 < s) (L H : Finset X) :
    ∑ x : X, ∑ y : X, Kmat s L H x y * ‖(y : Eucl k) - (x : Eucl k)‖ ^ 2 ≤ s * Vf L H := by
  unfold Vf
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun x _ => ?_)
  rw [Kmat_sum_mul L H (fun x y => ‖(y : Eucl k) - (x : Eucl k)‖ ^ 2) (by intro x; simp)]
  have hd : ‖((pt L H x : X) : Eucl k) - (x : Eucl k)‖ = dist x (pt L H x) := norm_diff L H x
  show wt s x (pt L H x) * ‖((pt L H x : X) : Eucl k) - (x : Eucl k)‖ ^ 2 ≤ s * dist x (pt L H x)
  rw [hd]
  unfold wt
  have h0 : 0 ≤ dist x (pt L H x) := dist_nonneg
  set d := dist x (pt L H x)
  rw [one_div, inv_mul_le_iff₀ (by positivity)]
  have : s * d * (1 + d / s) = s * d + d ^ 2 := by field_simp
  nlinarith

lemma Vf_eq (L H : Finset X) (h : HasMin L H) : Vf L H = 2 * minMatchingCost L H := sum_dist_pt L H h

lemma Uf_eq (s : ℝ) (L H : Finset X) : Uf s L H = ((L ∪ H).card : ℝ) + Vf L H / s := by
  unfold Uf Vf
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_div]
  simp only [nsmul_eq_mul, mul_one]
  congr 2
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _ hx
  have : pt L H x = x := pt_of_not_mem (fun h' => hx (Finset.mem_union_left _ h'))
      (fun h' => hx (Finset.mem_union_right _ h'))
  simp [this]

lemma Tf_nonneg {s : ℝ} (hs : 0 < s) (L H : Finset X) (g : Eucl k) : 0 ≤ Tf s L H g :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (wt_pos hs _ _).le (abs_nonneg _))

lemma Nf_nonneg (L H : Finset X) (g : Eucl k) : 0 ≤ Nf L H g :=
  Finset.sum_nonneg (fun x _ => Real.sqrt_nonneg _)

/-- AM-GM bound for `N`. -/
lemma Nf_amgm {s : ℝ} (hs : 0 < s) (L H : Finset X) (g : Eucl k) {l : ℝ} (hl : 0 < l) :
    Nf L H g ≤ (l * Tf s L H g + Uf s L H / l) / 2 := by
  have hT : ∑ x ∈ L ∪ H, wt s x (pt L H x) * |inner ℝ g (diff L H x)| ≤ Tf s L H g := by
    unfold Tf
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x _ _ => mul_nonneg (wt_pos hs _ _).le (abs_nonneg _))
  have key : Nf L H g ≤ (l * ∑ x ∈ L ∪ H, wt s x (pt L H x) * |inner ℝ g (diff L H x)| + Uf s L H / l) / 2 := by
    unfold Nf Uf
    rw [Finset.mul_sum, Finset.sum_div (a := l), ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_le_sum (fun x _ => ?_)
    set u := √|inner ℝ g (diff L H x)| with hu
    have hu2 : u ^ 2 = |inner ℝ g (diff L H x)| := Real.sq_sqrt (abs_nonneg _)
    have hw := wt_pos hs x (pt L H x)
    set w := wt s x (pt L H x) with hw'
    have hinv : (1 + dist x (pt L H x) / s) = 1 / w := by
      rw [hw']; unfold wt; rw [one_div_one_div]
    rw [hinv, ← hu2]
    have hlw : 0 < l * w := mul_pos hl hw
    have : 0 ≤ l * w * (u - 1 / (l * w)) ^ 2 := by positivity
    have e : l * w * (u - 1 / (l * w)) ^ 2 = l * w * u ^ 2 - 2 * u + 1 / (l * w) := by
      field_simp; ring
    have e2 : 1 / w / l = 1 / (l * w) := by field_simp
    rw [e2]
    nlinarith
  have : 0 ≤ l := hl.le
  nlinarith

end

end EuclideanLineAvgDist.Dev.Well6
end

section
open scoped BigOperators ENNReal Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Well7

open EuclideanLineAvgDist.Embedding EuclideanLineAvgDist.Dev.Well2 EuclideanLineAvgDist.Dev.Well5
  EuclideanLineAvgDist.Dev.Well6

noncomputable section

section EfLemmas

variable {k : ℕ} {X : Finset (Eucl k)}

lemma Ef_le_sq (Δ : ℝ) (L H : Finset X) (g : Eucl k) : Ef Δ L H g ≤ (X.card : ℝ) ^ 2 := by
  unfold Ef
  calc _ ≤ ∑ _p : X × X, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        split_ifs <;> simp
    _ = (X.card : ℝ) ^ 2 := by simp [Fintype.card_prod, sq]

lemma Ef_nonneg (Δ : ℝ) (L H : Finset X) (g : Eucl k) : 0 ≤ Ef Δ L H g := by
  unfold Ef
  refine Finset.sum_nonneg (fun p _ => ?_)
  split_ifs <;> simp

lemma sum_mem_ind (M : Finset X) : ∑ x : X, (if x ∈ M then (1 : ℝ) else 0) = M.card := by
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

lemma Ef_ge (Δ : ℝ) (L H : Finset X) (g : Eucl k) :
    Gf (X := X) Δ g - 2 * (L ∪ H).card * (X.card : ℝ) ≤ Ef Δ L H g := by
  have h1 : ∑ p : X × X, (if p.1 ∈ L ∪ H then (1 : ℝ) else 0) = (L ∪ H).card * (X.card : ℝ) := by
    rw [Fintype.sum_prod_type]
    have : ∀ x : X, ∑ y : X, (if (x, y).1 ∈ L ∪ H then (1 : ℝ) else 0) =
        (X.card : ℝ) * (if x ∈ L ∪ H then 1 else 0) := by
      intro x
      change ∑ _y : X, (if x ∈ L ∪ H then (1 : ℝ) else 0) = _
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    simp_rw [this]
    rw [← Finset.mul_sum, sum_mem_ind]; ring
  have h2 : ∑ p : X × X, (if p.2 ∈ L ∪ H then (1 : ℝ) else 0) = (X.card : ℝ) * (L ∪ H).card := by
    rw [Fintype.sum_prod_type]
    have : ∀ x : X, ∑ y : X, (if (x, y).2 ∈ L ∪ H then (1 : ℝ) else 0) = ((L ∪ H).card : ℝ) :=
      fun x => sum_mem_ind _
    simp_rw [this]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  have hle : Gf (X := X) Δ g ≤ Ef Δ L H g + ∑ p : X × X, ((if p.1 ∈ L ∪ H then (1 : ℝ) else 0) +
      (if p.2 ∈ L ∪ H then (1 : ℝ) else 0)) := by
    unfold Gf Ef
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun p _ => ?_)
    by_cases h1 : p.1 ∈ L ∪ H
    · simp only [h1, if_true]
      split_ifs <;> simp <;> nlinarith [apply_ite (fun _ : Prop => (0:ℝ)) ]
    · by_cases h2 : p.2 ∈ L ∪ H
      · simp only [h2, if_true]
        split_ifs <;> simp
      · simp only [h1, h2, not_false_eq_true, and_self, if_true, if_false]
        split_ifs <;> simp
  rw [Finset.sum_add_distrib, h1, h2] at hle
  linarith

end EfLemmas

variable {k : ℕ} (X : Finset (Eucl k)) (tie : X → ℕ)

lemma inner_between (hT : Function.Injective tie) (hn : 64 < X.card) (g : Eucl k) {a b x : X}
    (ha : a ∈ lowSet X tie g) (hb : b ∈ highSet X tie g) (hx : x ∉ lowSet X tie g ∪ highSet X tie g) :
    inner ℝ g (a : Eucl k) ≤ inner ℝ g (x : Eucl k) ∧ inner ℝ g (x : Eucl k) ≤ inner ℝ g (b : Eucl k) := by
  have hxL : x ∉ lowSet X tie g := fun h => hx (Finset.mem_union_left _ h)
  have hxH : x ∉ highSet X tie g := fun h => hx (Finset.mem_union_right _ h)
  have h1 := Dev.Well1.inner_low_le X tie g hT hn ha hxL
  have h2 := Dev.Well1.inner_le_high X tie g hT hn hb hxH
  rw [real_inner_comm g, real_inner_comm g] at *
  exact ⟨by rwa [real_inner_comm, real_inner_comm g] at h1, by rwa [real_inner_comm, real_inner_comm g] at h2⟩

lemma gap_le (hT : Function.Injective tie) (hn : 64 < X.card) (g : Eucl k) {z x0 y0 : X}
    (hz : z ∈ lowSet X tie g ∪ highSet X tie g)
    (hx0 : x0 ∉ lowSet X tie g ∪ highSet X tie g) (hy0 : y0 ∉ lowSet X tie g ∪ highSet X tie g) :
    |inner ℝ g ((x0 : Eucl k) - (y0 : Eucl k))| ≤
      |inner ℝ g (diff (lowSet X tie g) (highSet X tie g) z)| := by
  have hm := hasMin_lowHigh X tie hT hn g
  have key : ∀ {a b : X}, a ∈ lowSet X tie g → b ∈ highSet X tie g →
      |inner ℝ g ((x0 : Eucl k) - (y0 : Eucl k))| ≤ |inner ℝ g ((b : Eucl k) - (a : Eucl k))| := by
    intro a b ha hb
    obtain ⟨h1, h2⟩ := inner_between X tie hT hn g ha hb hx0
    obtain ⟨h3, h4⟩ := inner_between X tie hT hn g ha hb hy0
    have hb0 : 0 ≤ inner ℝ g ((b : Eucl k) - (a : Eucl k)) := by
      rw [inner_sub_right]; linarith
    calc |inner ℝ g ((x0 : Eucl k) - (y0 : Eucl k))| ≤ inner ℝ g ((b : Eucl k) - (a : Eucl k)) := by
          rw [inner_sub_right, inner_sub_right]
          exact abs_le.2 ⟨by linarith, by linarith⟩
      _ = _ := (abs_of_nonneg hb0).symm
  rcases Finset.mem_union.1 hz with hz | hz
  · have := key hz (pt_mem_high hm hz)
    unfold diff; exact this
  · have := key (pt_mem_low hm hz) hz
    have e : |inner ℝ g ((z : Eucl k) - ((pt (lowSet X tie g) (highSet X tie g) z : X) : Eucl k))| =
        |inner ℝ g (((pt (lowSet X tie g) (highSet X tie g) z : X) : Eucl k) - (z : Eucl k))| := by
      rw [← abs_neg, ← inner_neg_right, neg_sub]
    unfold diff
    rw [← e]; exact this

lemma card_union_lowHigh (hT : Function.Injective tie) (hn : 64 < X.card) (g : Eucl k) :
    ((lowSet X tie g ∪ highSet X tie g).card : ℝ) = 2 * (extremeCount X.card : ℝ) := by
  rw [Finset.card_union_of_disjoint (Dev.Well1.disjoint_low_high X tie g hn),
    Dev.Well1.card_lowSet X tie g hT hn, Dev.Well1.card_highSet X tie g hT hn]
  push_cast; ring

lemma Nf_lower (hT : Function.Injective tie) (hn : 64 < X.card) (Δ : ℝ) (g : Eucl k) :
    2 * (extremeCount X.card : ℝ) * √(Δ / 8) * Ef Δ (lowSet X tie g) (highSet X tie g) g /
        (X.card : ℝ) ^ 2 ≤ Nf (lowSet X tie g) (highSet X tie g) g := by
  have hnpos : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast (by omega : 0 < X.card)
  have hE0 := Ef_nonneg Δ (lowSet X tie g) (highSet X tie g) g
  have hE1 := Ef_le_sq Δ (lowSet X tie g) (highSet X tie g) g
  by_cases hE : Ef Δ (lowSet X tie g) (highSet X tie g) g = 0
  · rw [hE]; simp; exact Nf_nonneg _ _ _
  · have hex : ∃ p : X × X, p.1 ∉ lowSet X tie g ∪ highSet X tie g ∧
        p.2 ∉ lowSet X tie g ∪ highSet X tie g ∧
        Δ / 8 ≤ |inner ℝ g ((p.1 : Eucl k) - (p.2 : Eucl k))| := by
      unfold Ef at hE
      obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hE
      refine ⟨p, ?_⟩
      by_cases h : (p.1 ∉ lowSet X tie g ∪ highSet X tie g ∧ p.2 ∉ lowSet X tie g ∪ highSet X tie g)
      · rw [if_pos h] at hp
        by_cases h2 : Δ / 8 ≤ |inner ℝ g ((p.1 : Eucl k) - (p.2 : Eucl k))|
        · exact ⟨h.1, h.2, h2⟩
        · rw [if_neg h2] at hp; exact absurd rfl hp
      · rw [if_neg h] at hp; exact absurd rfl hp
    obtain ⟨p, h1, h2, h3⟩ := hex
    have hN : (lowSet X tie g ∪ highSet X tie g).card * √(Δ / 8) ≤ Nf (lowSet X tie g) (highSet X tie g) g := by
      unfold Nf
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum (fun z hz => ?_)
      apply Real.sqrt_le_sqrt
      exact h3.trans (gap_le X tie hT hn g hz h1 h2)
    rw [card_union_lowHigh X tie hT hn g] at hN
    calc _ ≤ 2 * (extremeCount X.card : ℝ) * √(Δ / 8) * (X.card : ℝ) ^ 2 / (X.card : ℝ) ^ 2 := by
          gcongr
      _ = 2 * (extremeCount X.card : ℝ) * √(Δ / 8) := by field_simp
      _ ≤ _ := hN

end

end EuclideanLineAvgDist.Dev.Well7
end

section
open scoped BigOperators ENNReal Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Well8

open EuclideanLineAvgDist.Embedding EuclideanLineAvgDist.Dev.Well2 EuclideanLineAvgDist.Dev.Well5
  EuclideanLineAvgDist.Dev.Well6 EuclideanLineAvgDist.Dev.Well7

noncomputable section

variable {k : ℕ} {X : Finset (Eucl k)}

lemma integrable_ite_one {p : Eucl k → Prop} (hp : MeasurableSet {g | p g}) :
    Integrable (fun g : Eucl k => if p g then (1 : ℝ) else 0) (stdGaussian (Eucl k)) := by
  have : (fun g : Eucl k => if p g then (1 : ℝ) else 0) = Set.indicator {g | p g} (fun _ => (1 : ℝ)) := by
    funext g; simp [Set.indicator]
  rw [this]
  exact (integrable_const (1 : ℝ)).indicator hp

lemma integral_ite_one {p : Eucl k → Prop} (hp : MeasurableSet {g | p g}) :
    ∫ g, (if p g then (1 : ℝ) else 0) ∂(stdGaussian (Eucl k)) = (stdGaussian (Eucl k)).real {g | p g} := by
  have : (fun g : Eucl k => if p g then (1 : ℝ) else 0) = Set.indicator {g | p g} (fun _ => (1 : ℝ)) := by
    funext g; simp [Set.indicator]
  rw [this, integral_indicator hp]
  simp

lemma measurableSet_gap (Δ : ℝ) (x y : X) :
    MeasurableSet {g : Eucl k | Δ / 8 ≤ |inner ℝ g ((x : Eucl k) - (y : Eucl k))|} :=
  measurableSet_le measurable_const (by fun_prop)

lemma integrable_Gf (Δ : ℝ) : Integrable (Gf (X := X) Δ) (stdGaussian (Eucl k)) := by
  unfold Gf
  refine integrable_finset_sum _ (fun p _ => ?_)
  exact integrable_ite_one (measurableSet_gap Δ p.1 p.2)

lemma integral_Gf (Δ : ℝ) : ∫ g, Gf (X := X) Δ g ∂(stdGaussian (Eucl k)) =
    ∑ x : X, ∑ y : X, (stdGaussian (Eucl k)).real
      {g : Eucl k | Δ / 8 ≤ |inner ℝ g ((x : Eucl k) - (y : Eucl k))|} := by
  unfold Gf
  rw [integral_finset_sum _ (fun p _ => integrable_ite_one (measurableSet_gap Δ p.1 p.2)),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  exact integral_ite_one (measurableSet_gap Δ x y)

lemma integral_Gf_ge {Δ : ℝ} (hΔ : 0 < Δ)
    (hball : ∀ x : X, ((ball x (Δ / 4)).card : ℝ) < (X.card : ℝ) / 64) :
    (63 / 128 : ℝ) * (X.card : ℝ) ^ 2 ≤ ∫ g, Gf (X := X) Δ g ∂(stdGaussian (Eucl k)) := by
  rw [integral_Gf]
  have hx : ∀ x : X, (1 / 2 : ℝ) * ((X.card : ℝ) - (X.card : ℝ) / 64) ≤
      ∑ y : X, (stdGaussian (Eucl k)).real
        {g : Eucl k | Δ / 8 ≤ |inner ℝ g ((x : Eucl k) - (y : Eucl k))|} := by
    intro x
    have h1 : ∀ y : X, (1 / 2 : ℝ) * (1 - (if dist x y < Δ / 4 then (1 : ℝ) else 0)) ≤
        (stdGaussian (Eucl k)).real
          {g : Eucl k | Δ / 8 ≤ |inner ℝ g ((x : Eucl k) - (y : Eucl k))|} := by
      intro y
      by_cases h : dist x y < Δ / 4
      · rw [if_pos h]; simp [measureReal_nonneg]
      · rw [if_neg h]
        apply le_trans (by norm_num) (Dev.Well4.prob_abs_inner_ge ((x : Eucl k) - (y : Eucl k))
          (by linarith : 0 < Δ / 8) ?_)
        rw [Subtype.dist_eq, dist_eq_norm] at h
        linarith [not_lt.1 h]
    calc _ ≤ ∑ y : X, (1 / 2 : ℝ) * (1 - (if dist x y < Δ / 4 then (1 : ℝ) else 0)) := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_coe, nsmul_eq_mul, mul_one]
          have hb : ∑ y : X, (if dist x y < Δ / 4 then (1 : ℝ) else 0) = ((ball x (Δ / 4)).card : ℝ) := by
            rw [Finset.sum_boole]; rfl
          rw [hb]
          have := hball x
          linarith
      _ ≤ _ := Finset.sum_le_sum (fun y _ => h1 y)
  calc (63 / 128 : ℝ) * (X.card : ℝ) ^ 2 = ∑ _x : X, (1 / 2 : ℝ) * ((X.card : ℝ) - (X.card : ℝ) / 64) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]; ring
    _ ≤ _ := Finset.sum_le_sum (fun x _ => hx x)

end

end EuclideanLineAvgDist.Dev.Well8
end

section
open scoped BigOperators ENNReal Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Well9

open EuclideanLineAvgDist.Embedding EuclideanLineAvgDist.Dev.Well2 EuclideanLineAvgDist.Dev.Well5
  EuclideanLineAvgDist.Dev.Well6 EuclideanLineAvgDist.Dev.Well7 EuclideanLineAvgDist.Dev.Well8

noncomputable section

variable {k : ℕ} (X : Finset (Eucl k)) (tie : X → ℕ)

/-- The quantities along the order data. -/
def Tg (s : ℝ) (g : Eucl k) : ℝ := Tf s (lowSet X tie g) (highSet X tie g) g
def Ng (g : Eucl k) : ℝ := Nf (lowSet X tie g) (highSet X tie g) g
def Ug (s : ℝ) (g : Eucl k) : ℝ := Uf s (lowSet X tie g) (highSet X tie g)
def Eg (Δ : ℝ) (g : Eucl k) : ℝ := Ef Δ (lowSet X tie g) (highSet X tie g) g
def Vg (g : Eucl k) : ℝ := Vf (lowSet X tie g) (highSet X tie g)
def mm (g : Eucl k) : ℝ := minMatchingCost (lowSet X tie g) (highSet X tie g)

/-- The sum of all projected gaps (an integrable dominating function). -/
def Bf (g : Eucl k) : ℝ := ∑ x : X, ∑ y : X, |inner ℝ g ((y : Eucl k) - (x : Eucl k))|

lemma measurable_Tg (s : ℝ) : Measurable (Tg X tie s) :=
  Dev.Well3.measurable_orderData X tie (fun L H => Tf s L H) (fun L H => measurable_Tf s L H)
lemma measurable_Ng : Measurable (Ng X tie) :=
  Dev.Well3.measurable_orderData X tie (fun L H => Nf L H) (fun L H => measurable_Nf L H)
lemma measurable_Eg (Δ : ℝ) : Measurable (Eg X tie Δ) :=
  Dev.Well3.measurable_orderData X tie (fun L H => Ef Δ L H) (fun L H => measurable_Ef Δ L H)
lemma measurable_mm : Measurable (mm X tie) :=
  Dev.Well3.measurable_orderData X tie (fun L H _ => minMatchingCost L H) (fun L H => measurable_const)

lemma integrable_Bf : Integrable (Bf X) (stdGaussian (Eucl k)) := by
  unfold Bf
  exact integrable_finset_sum _ (fun x _ => integrable_finset_sum _ (fun y _ =>
    Dev.Well4.integrable_abs_inner _))

lemma Tg_le_Bf {s : ℝ} (hs : 0 < s) (g : Eucl k) : Tg X tie s g ≤ Bf X g := by
  unfold Tg Tf Bf
  refine Finset.sum_le_sum (fun x _ => ?_)
  calc wt s x (pt (lowSet X tie g) (highSet X tie g) x) * |inner ℝ g (diff (lowSet X tie g) (highSet X tie g) x)|
      ≤ 1 * |inner ℝ g (diff (lowSet X tie g) (highSet X tie g) x)| :=
        mul_le_mul_of_nonneg_right (wt_le_one hs _ _) (abs_nonneg _)
    _ ≤ _ := by
        rw [one_mul]
        exact Finset.single_le_sum (f := fun y : X => |inner ℝ g ((y : Eucl k) - (x : Eucl k))|)
          (fun y _ => abs_nonneg _) (Finset.mem_univ (pt (lowSet X tie g) (highSet X tie g) x))

lemma integrable_Tg {s : ℝ} (hs : 0 < s) : Integrable (Tg X tie s) (stdGaussian (Eucl k)) := by
  refine Integrable.mono' (integrable_Bf X) (measurable_Tg X tie s).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun g => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ Tg X tie s g from Tf_nonneg hs _ _ g)]
  exact Tg_le_Bf X tie hs g

lemma integrable_Eg (Δ : ℝ) : Integrable (Eg X tie Δ) (stdGaussian (Eucl k)) := by
  refine Integrable.mono' (integrable_const ((X.card : ℝ) ^ 2)) (measurable_Eg X tie Δ).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun g => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ Eg X tie Δ g from Ef_nonneg _ _ _ g)]
  exact Ef_le_sq _ _ _ g

variable (hT : Function.Injective tie) (hn : 64 < X.card)
include hT hn

lemma Vg_eq (g : Eucl k) : Vg X tie g = 2 * mm X tie g :=
  Vf_eq _ _ (hasMin_lowHigh X tie hT hn g)

lemma integrable_Vg (hI : Integrable (mm X tie) (stdGaussian (Eucl k))) :
    Integrable (Vg X tie) (stdGaussian (Eucl k)) := by
  have : Vg X tie = fun g => 2 * mm X tie g := funext (Vg_eq X tie hT hn)
  rw [this]; exact hI.const_mul 2

lemma Ug_eq {s : ℝ} (g : Eucl k) :
    Ug X tie s g = 2 * (extremeCount X.card : ℝ) + Vg X tie g / s := by
  unfold Ug Vg
  rw [Uf_eq, card_union_lowHigh X tie hT hn g]

lemma integrable_Ug {s : ℝ} (hI : Integrable (mm X tie) (stdGaussian (Eucl k))) :
    Integrable (Ug X tie s) (stdGaussian (Eucl k)) := by
  have : Ug X tie s = fun g => 2 * (extremeCount X.card : ℝ) + Vg X tie g / s :=
    funext (Ug_eq X tie hT hn)
  rw [this]
  exact (integrable_const _).add ((integrable_Vg X tie hT hn hI).div_const s)

lemma integrable_Ng {s : ℝ} (hs : 0 < s) (hI : Integrable (mm X tie) (stdGaussian (Eucl k))) :
    Integrable (Ng X tie) (stdGaussian (Eucl k)) := by
  have hb : Integrable (fun g => (1 * Tg X tie s g + Ug X tie s g / 1) / 2) (stdGaussian (Eucl k)) :=
    (((integrable_Tg X tie hs).const_mul 1).add ((integrable_Ug X tie hT hn hI).div_const 1)).div_const 2
  refine Integrable.mono' hb (measurable_Ng X tie).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun g => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ Ng X tie g from Nf_nonneg _ _ g)]
  exact Nf_amgm hs _ _ g one_pos

end

end EuclideanLineAvgDist.Dev.Well9
end

section
open scoped BigOperators ENNReal Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Well10

open EuclideanLineAvgDist.Embedding EuclideanLineAvgDist.Dev.Well2 EuclideanLineAvgDist.Dev.Well5
  EuclideanLineAvgDist.Dev.Well6 EuclideanLineAvgDist.Dev.Well7 EuclideanLineAvgDist.Dev.Well8
  EuclideanLineAvgDist.Dev.Well9

noncomputable section

variable {k : ℕ} (X : Finset (Eucl k)) (tie : X → ℕ) (hT : Function.Injective tie) (hn : 64 < X.card)
include hT hn

lemma integral_Eg_ge {Δ : ℝ} (hΔ : 0 < Δ)
    (hball : ∀ x : X, ((ball x (Δ / 4)).card : ℝ) < (X.card : ℝ) / 64) :
    (X.card : ℝ) ^ 2 / 4 ≤ ∫ g, Eg X tie Δ g ∂(stdGaussian (Eucl k)) := by
  have hm := Dev.Well1.four_mul_extremeCount_lt hn
  have hnpos : (64 : ℝ) < X.card := by exact_mod_cast hn
  have hG := integral_Gf_ge (X := X) hΔ hball
  have hle : ∫ g, (Gf (X := X) Δ g - 2 * (2 * (extremeCount X.card : ℝ)) * (X.card : ℝ)) ∂(stdGaussian (Eucl k))
      ≤ ∫ g, Eg X tie Δ g ∂(stdGaussian (Eucl k)) := by
    refine integral_mono ((integrable_Gf Δ).sub (integrable_const _)) (integrable_Eg X tie Δ) (fun g => ?_)
    have := Ef_ge Δ (lowSet X tie g) (highSet X tie g) g
    rw [card_union_lowHigh X tie hT hn g] at this
    exact this
  rw [integral_sub (integrable_Gf Δ) (integrable_const _), integral_const] at hle
  simp only [probReal_univ, one_smul] at hle
  nlinarith

lemma integral_Ng_ge {Δ : ℝ} (hΔ : 0 < Δ)
    (hball : ∀ x : X, ((ball x (Δ / 4)).card : ℝ) < (X.card : ℝ) / 64) {s : ℝ} (hs : 0 < s)
    (hI : Integrable (mm X tie) (stdGaussian (Eucl k))) :
    (extremeCount X.card : ℝ) / 2 * √(Δ / 8) ≤ ∫ g, Ng X tie g ∂(stdGaussian (Eucl k)) := by
  have hnpos : (64 : ℝ) < X.card := by exact_mod_cast hn
  have hE := integral_Eg_ge X tie hT hn hΔ hball
  set c : ℝ := 2 * (extremeCount X.card : ℝ) * √(Δ / 8) / (X.card : ℝ) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hle : ∫ g, c * Eg X tie Δ g ∂(stdGaussian (Eucl k)) ≤ ∫ g, Ng X tie g ∂(stdGaussian (Eucl k)) := by
    refine integral_mono ((integrable_Eg X tie Δ).const_mul c) (integrable_Ng X tie hT hn hs hI) (fun g => ?_)
    have := Nf_lower X tie hT hn Δ g
    show c * Ef Δ (lowSet X tie g) (highSet X tie g) g ≤ _
    rw [hc]
    calc _ = 2 * (extremeCount X.card : ℝ) * √(Δ / 8) * Ef Δ (lowSet X tie g) (highSet X tie g) g /
        (X.card : ℝ) ^ 2 := by ring
      _ ≤ _ := this
  rw [integral_const_mul] at hle
  have : (extremeCount X.card : ℝ) / 2 * √(Δ / 8) = c * ((X.card : ℝ) ^ 2 / 4) := by
    rw [hc]; field_simp; ring
  rw [this]
  exact (mul_le_mul_of_nonneg_left hE hc0).trans hle

lemma integral_Ug_le {s : ℝ} (hs : 0 < s) (hI : Integrable (mm X tie) (stdGaussian (Eucl k)))
    (hS : ∫ g, mm X tie g ∂(stdGaussian (Eucl k)) ≤ (extremeCount X.card : ℝ) * s) :
    ∫ g, Ug X tie s g ∂(stdGaussian (Eucl k)) ≤ 4 * (extremeCount X.card : ℝ) := by
  have h1 : (fun g => Ug X tie s g) = fun g => 2 * (extremeCount X.card : ℝ) + 2 * mm X tie g / s := by
    funext g; rw [Ug_eq X tie hT hn g, Vg_eq X tie hT hn g]
  rw [h1, integral_add (integrable_const _) ((hI.const_mul 2).div_const s), integral_const,
    integral_div, integral_const_mul]
  simp only [probReal_univ, one_smul]
  have : 2 * (∫ g, mm X tie g ∂(stdGaussian (Eucl k))) / s ≤ 2 * (extremeCount X.card : ℝ) := by
    rw [div_le_iff₀ hs]; nlinarith
  linarith

lemma tau_lower {Δ : ℝ} (hΔ : 0 < Δ)
    (hball : ∀ x : X, ((ball x (Δ / 4)).card : ℝ) < (X.card : ℝ) / 64) {s : ℝ} (hs : 0 < s)
    (hI : Integrable (mm X tie) (stdGaussian (Eucl k)))
    (hS : ∫ g, mm X tie g ∂(stdGaussian (Eucl k)) ≤ (extremeCount X.card : ℝ) * s) :
    Δ * (X.card : ℝ) / 8192 ≤ ∫ g, Tg X tie s g ∂(stdGaussian (Eucl k)) := by
  have hnpos : (64 : ℝ) < X.card := by exact_mod_cast hn
  have hm1 := Dev.Well1.extremeCount_ge X.card
  have hmpos : 0 < (extremeCount X.card : ℝ) := by linarith
  set m : ℝ := (extremeCount X.card : ℝ) with hmdef
  set ν := ∫ g, Ng X tie g ∂(stdGaussian (Eucl k)) with hν
  set τ := ∫ g, Tg X tie s g ∂(stdGaussian (Eucl k)) with hτ
  have hν0 := integral_Ng_ge X tie hT hn hΔ hball hs hI
  have hU := integral_Ug_le X tie hT hn hs hI hS
  have hνpos : 0 < ν := lt_of_lt_of_le (by positivity) hν0
  have hsq : (m / 2 * √(Δ / 8)) ^ 2 = m ^ 2 * Δ / 32 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hν2 : m ^ 2 * Δ / 32 ≤ ν ^ 2 := by
    rw [← hsq]; exact pow_le_pow_left₀ (by positivity) hν0 2
  -- AM-GM integrated
  set l : ℝ := 4 * m / ν with hl
  have hlpos : 0 < l := by positivity
  have hint : ν ≤ ∫ g, (l * Tg X tie s g + Ug X tie s g / l) / 2 ∂(stdGaussian (Eucl k)) := by
    refine integral_mono (integrable_Ng X tie hT hn hs hI) ?_ (fun g => Nf_amgm hs _ _ g hlpos)
    exact (((integrable_Tg X tie hs).const_mul l).add
      ((integrable_Ug X tie hT hn hI).div_const l)).div_const 2
  rw [integral_div, integral_add ((integrable_Tg X tie hs).const_mul l)
    ((integrable_Ug X tie hT hn hI).div_const l), integral_const_mul, integral_div] at hint
  have h4 : (∫ g, Ug X tie s g ∂(stdGaussian (Eucl k))) / l ≤ ν := by
    rw [div_le_iff₀ hlpos]
    have : ν * l = 4 * m := by rw [hl]; field_simp
    linarith
  have h5 : ν ≤ l * τ := by linarith
  have h6 : ν ^ 2 ≤ 4 * m * τ := by
    rw [hl] at h5
    have : 4 * m / ν * τ * ν = 4 * m * τ := by field_simp
    nlinarith
  have : m * Δ / 128 ≤ τ := by
    have : m ^ 2 * Δ / 32 ≤ 4 * m * τ := hν2.trans h6
    have h7 : m * (m * Δ / 128) ≤ m * τ := by nlinarith
    exact le_of_mul_le_mul_left h7 hmpos
  nlinarith

end

end EuclideanLineAvgDist.Dev.Well10
end

section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Well11

open EuclideanLineAvgDist.Embedding EuclideanLineAvgDist.Dev.Well2 EuclideanLineAvgDist.Dev.Well5
  EuclideanLineAvgDist.Dev.Well6 EuclideanLineAvgDist.Dev.Well7 EuclideanLineAvgDist.Dev.Well8
  EuclideanLineAvgDist.Dev.Well9 EuclideanLineAvgDist.Dev.Well10

noncomputable section

open scoped Classical

lemma one_lt_log_of_gt {n : ℝ} (hn : 64 < n) : 1 < Real.log n := by
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  exact lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num; linarith)

/-- Final real-number algebra. -/
lemma final_algebra {C Δ S n L r : ℝ} (hC : 0 < C) (hn : 0 < n) (hΔ : 0 < Δ) (hS : 0 ≤ S)
    (hr : 0 < r) (hL : L = 1 / r)
    (h : (Δ / 8192) ^ 2 ≤ C * (128 * (S / n) ^ 2) * L) :
    1 / (8192 * √(128 * C)) * n * Δ * √r ≤ S := by
  have hc2 : (1 / (8192 * √(128 * C))) ^ 2 = 1 / (8192 ^ 2 * (128 * C)) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  have hsq : (1 / (8192 * √(128 * C)) * n * Δ * √r) ^ 2 ≤ S ^ 2 := by
    have e : (1 / (8192 * √(128 * C)) * n * Δ * √r) ^ 2 =
        (1 / (8192 ^ 2 * (128 * C))) * n ^ 2 * Δ ^ 2 * r := by
      rw [mul_pow, mul_pow, mul_pow, hc2, Real.sq_sqrt hr.le]
    rw [e]
    have h1 : Δ ^ 2 * r ≤ 8192 ^ 2 * (128 * C) * (S / n) ^ 2 := by
      have := mul_le_mul_of_nonneg_right h hr.le
      rw [hL] at this
      have e2 : C * (128 * (S / n) ^ 2) * (1 / r) * r = C * (128 * (S / n) ^ 2) := by field_simp
      rw [e2] at this
      have e3 : (Δ / 8192) ^ 2 * r = Δ ^ 2 * r / 8192 ^ 2 := by ring
      rw [e3, div_le_iff₀ (by positivity)] at this
      nlinarith
    have h2 : (1 / (8192 ^ 2 * (128 * C))) * n ^ 2 * Δ ^ 2 * r =
        (1 / (8192 ^ 2 * (128 * C))) * n ^ 2 * (Δ ^ 2 * r) := by ring
    rw [h2]
    calc _ ≤ (1 / (8192 ^ 2 * (128 * C))) * n ^ 2 * (8192 ^ 2 * (128 * C) * (S / n) ^ 2) := by gcongr
      _ = S ^ 2 := by field_simp
  exact (pow_le_pow_iff_left₀ (by positivity) hS (by norm_num : (2 : ℕ) ≠ 0)).1 hsq

end

end EuclideanLineAvgDist.Dev.Well11
end

section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist

open EuclideanLineAvgDist.Embedding
open EuclideanLineAvgDist.Dev.Well2 EuclideanLineAvgDist.Dev.Well5 EuclideanLineAvgDist.Dev.Well6
  EuclideanLineAvgDist.Dev.Well9 EuclideanLineAvgDist.Dev.Well10 EuclideanLineAvgDist.Dev.Well11

theorem chk_well_spread_matching :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (X : Finset (Eucl k)) (tie : X → ℕ), Function.Injective tie →
      (∀ x : X, ((ball x (avgDist X / 4)).card : ℝ) < (X.card : ℝ) / 64) →
        ENNReal.ofReal (c * (X.card : ℝ) * avgDist X *
            Real.sqrt (Real.log (Real.log (X.card : ℝ)) / Real.log (X.card : ℝ)))
          ≤ expectedExtremeMatching X tie := by
  classical
  obtain ⟨C, hC, hlem⟩ := Embedding.gaussian_transition_bound
  refine ⟨1 / (8192 * √(128 * C)), by positivity, ?_⟩
  intro k X tie hT hball
  set Δ := avgDist X with hΔdef
  by_cases hΔ : Δ ≤ 0
  · have : 1 / (8192 * √(128 * C)) * (X.card : ℝ) * Δ *
        Real.sqrt (Real.log (Real.log (X.card : ℝ)) / Real.log (X.card : ℝ)) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ (Real.sqrt_nonneg _)
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hΔ
    rw [ENNReal.ofReal_of_nonpos this]; exact zero_le
  push Not at hΔ
  -- X is large
  have hne : X.Nonempty := by
    rcases Finset.eq_empty_or_nonempty X with h | h
    · exfalso
      have : Δ = 0 := by subst h; simp [hΔdef, avgDist, distSum]
      linarith
    · exact h
  have hn : 64 < X.card := by
    by_contra hle
    push Not at hle
    obtain ⟨x, hx⟩ := hne
    have h1 := hball ⟨x, hx⟩
    have h2 : 1 ≤ (ball (⟨x, hx⟩ : X) (Δ / 4)).card := by
      apply Finset.card_pos.2
      refine ⟨⟨x, hx⟩, ?_⟩
      simp [ball, hΔ]
    have h3 : ((X.card : ℕ) : ℝ) ≤ 64 := by exact_mod_cast hle
    have : (1 : ℝ) ≤ ((ball (⟨x, hx⟩ : X) (Δ / 4)).card : ℝ) := by exact_mod_cast h2
    linarith
  have hnR : (64 : ℝ) < X.card := by exact_mod_cast hn
  -- the integrand
  have hmm_nonneg : ∀ g, 0 ≤ mm X tie g := by
    intro g
    unfold mm minMatchingCost
    exact Real.iInf_nonneg (fun M => Finset.sum_nonneg (fun _ _ => dist_nonneg))
  by_cases hfin : expectedExtremeMatching X tie = ⊤
  · rw [hfin]; exact le_top
  have hlint : expectedExtremeMatching X tie = ∫⁻ g, ENNReal.ofReal (mm X tie g) ∂(stdGaussian (Eucl k)) := rfl
  have hI : Integrable (mm X tie) (stdGaussian (Eucl k)) := by
    refine ⟨(measurable_mm X tie).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hmm_nonneg)]
    rw [hlint] at hfin
    exact lt_top_iff_ne_top.2 hfin
  set S := ∫ g, mm X tie g ∂(stdGaussian (Eucl k)) with hSdef
  have hS0 : 0 ≤ S := integral_nonneg hmm_nonneg
  have hSeq : ENNReal.ofReal S = expectedExtremeMatching X tie := by
    rw [hlint, hSdef]
    exact ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall hmm_nonneg)
  rw [← hSeq]
  apply ENNReal.ofReal_le_ofReal
  -- choose the scale
  set n : ℝ := (X.card : ℝ) with hndef
  set m : ℝ := (extremeCount X.card : ℝ) with hmdef
  have hm1 : n / 64 ≤ m := Dev.Well1.extremeCount_ge X.card
  obtain ⟨s, hs, hSs, hsS⟩ : ∃ s : ℝ, 0 < s ∧ S ≤ m * s ∧ s * S ≤ 64 * S ^ 2 / n := by
    by_cases h0 : S = 0
    · exact ⟨1, one_pos, by rw [h0]; positivity, by rw [h0]; simp⟩
    · have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm h0)
      refine ⟨64 * S / n, by positivity, ?_, ?_⟩
      · have : m * (64 * S / n) ≥ n / 64 * (64 * S / n) := by gcongr
        have e : n / 64 * (64 * S / n) = S := by field_simp
        linarith
      · apply le_of_eq; field_simp
  -- lower bound on projectionMean
  have hτ := tau_lower X tie hT hn hΔ hball hs hI hSs
  set K : Eucl k → X → X → ℝ := fun g => Kmat s (lowSet X tie g) (highSet X tie g) with hKdef
  have hK : IsGaussianTransitionFamily X K := by
    refine ⟨fun g x y => Kmat_symm s _ _ x y, fun g x y => Kmat_nonneg hs _ _ x y,
      fun g x => Kmat_sum _ _ x, fun x y => ?_⟩
    exact Dev.Well3.measurable_orderData X tie (fun L H _ => Kmat s L H x y) (fun L H => measurable_const)
  have hproj : projectionMean X K = (1 / n) * ∫ g, Tg X tie s g ∂(stdGaussian (Eucl k)) := by
    unfold projectionMean
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show 1 / n * ∑ x : X, ∑ y : X, Kmat s (lowSet X tie g) (highSet X tie g) x y *
      |inner ℝ g ((y : Eucl k) - (x : Eucl k))| = 1 / n * Tg X tie s g
    rw [sum_K_proj]; rfl
  have hsq : squaredStepMean X K ≤ (1 / n) * (s * (2 * S)) := by
    have hint : Integrable (fun g => (1 / n) * (s * Vg X tie g)) (stdGaussian (Eucl k)) :=
      ((integrable_Vg X tie hT hn hI).const_mul s).const_mul (1 / n)
    have hle : squaredStepMean X K ≤ ∫ g, (1 / n) * (s * Vg X tie g) ∂(stdGaussian (Eucl k)) := by
      unfold squaredStepMean
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => ?_) hint
        (Filter.Eventually.of_forall fun g => ?_)
      · apply mul_nonneg (by positivity)
        exact Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ =>
          mul_nonneg (Kmat_nonneg hs _ _ x y) (sq_nonneg _)))
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_K_sq_le hs _ _
    refine hle.trans (le_of_eq ?_)
    have : (fun g => (1 / n) * (s * Vg X tie g)) = fun g => (1 / n) * (s * (2 * mm X tie g)) := by
      funext g; rw [Vg_eq X tie hT hn g]
    rw [this, integral_const_mul, integral_const_mul, integral_const_mul]
  -- Lemma 2.1
  have hmain := hlem k X K hK
  have hL : logRate X.card =
      1 / (Real.log (Real.log n) / Real.log n) := by
    unfold logRate
    have : max 3 (X.card : ℝ) = n := max_eq_right (by linarith)
    rw [this]; rw [one_div_div]
  have hlog1 := one_lt_log_of_gt hnR
  have hr : 0 < Real.log (Real.log n) / Real.log n :=
    div_pos (Real.log_pos hlog1) (by linarith)
  have hLnn : 0 ≤ logRate X.card := by rw [hL]; positivity
  have hQ : squaredStepMean X K ≤ 128 * (S / n) ^ 2 := by
    refine hsq.trans ?_
    have : (1 / n) * (s * (2 * S)) = 2 * (s * S) / n := by ring
    rw [this, div_le_iff₀ (by positivity)]
    have e : 128 * (S / n) ^ 2 * n = 128 * S ^ 2 / n := by field_simp
    rw [e]
    have : 2 * (s * S) ≤ 2 * (64 * S ^ 2 / n) := by linarith
    calc 2 * (s * S) ≤ 2 * (64 * S ^ 2 / n) := this
      _ = 128 * S ^ 2 / n := by ring
  have hτ' : Δ / 8192 ≤ projectionMean X K := by
    rw [hproj]
    have : Δ / 8192 = (1 / n) * (Δ * n / 8192) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hτ (by positivity)
  have hpos : 0 ≤ Δ / 8192 := by positivity
  have h1 : (Δ / 8192) ^ 2 ≤ C * (128 * (S / n) ^ 2) * logRate X.card := by
    calc (Δ / 8192) ^ 2 ≤ projectionMean X K ^ 2 := pow_le_pow_left₀ hpos hτ' 2
      _ ≤ C * squaredStepMean X K * logRate X.card := hmain
      _ ≤ C * (128 * (S / n) ^ 2) * logRate X.card := by gcongr
  exact final_algebra hC (by linarith) hΔ hS0 hr hL h1

end EuclideanLineAvgDist
end

theorem solution : type_of% @EuclideanLineAvgDist.chk_well_spread_matching := @EuclideanLineAvgDist.chk_well_spread_matching
