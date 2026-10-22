-- Prove2me | solution 1 for ComplementsRev.Approx.proposition_4_1
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-21T16:09:47.364968+00:00
-- url     : https://prove2.me/submissions/85a0f4c2-fd40-4732-9bd2-9f19fc842974

import Mathlib
import Definitions.Def_ComplementsRev_Approx_Setting

open ComplementsRev.Approx

namespace CRGen

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

lemma mem_supp (P : Population κ) {w : Finset κ → ℝ} (hw : w ∈ P.profiles) (T : Finset κ) :
    w T ∈ P.supp T := Fintype.mem_piFinset.mp hw T

lemma w_nonneg (P : Population κ) {w : Finset κ → ℝ} (hw : w ∈ P.profiles) (T : Finset κ) :
    0 ≤ w T := P.supp_nonneg T (w T) (mem_supp P hw T)

lemma prob_nonneg (P : Population κ) {w : Finset κ → ℝ} (hw : w ∈ P.profiles) :
    0 ≤ P.prob w := by
  unfold Population.prob
  exact Finset.prod_nonneg (fun T _ => le_of_lt (P.f_pos T (w T) (mem_supp P hw T)))

lemma E_prod (P : Population κ) (h : Finset κ → ℝ → ℝ) :
    P.E (fun w => ∏ T, h T (w T)) = ∏ T, ∑ y ∈ P.supp T, P.f T y * h T y := by
  unfold Population.E Population.prob Population.profiles
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [← Finset.prod_mul_distrib]

lemma E_one (P : Population κ) : P.E (fun _ => 1) = 1 := by
  have := E_prod P (fun _ _ => 1)
  simp only [Finset.prod_const_one, mul_one] at this
  rw [this]
  exact Finset.prod_eq_one (fun T _ => P.f_sum T)

lemma E_marg (P : Population κ) (T0 : Finset κ) (h : ℝ → ℝ) :
    P.E (fun w => h (w T0)) = ∑ y ∈ P.supp T0, P.f T0 y * h y := by
  have := E_prod P (fun T y => if T = T0 then h y else 1)
  have e1 : (fun w : Finset κ → ℝ => ∏ T, (if T = T0 then h (w T) else 1)) =
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

lemma E_sub (P : Population κ) (g h : (Finset κ → ℝ) → ℝ) :
    P.E (fun w => g w - h w) = P.E g - P.E h := by
  unfold Population.E
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun w _ => by ring)

lemma E_add (P : Population κ) (g h : (Finset κ → ℝ) → ℝ) :
    P.E g + P.E h = P.E (fun w => g w + h w) := by
  unfold Population.E
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => by ring)

lemma E_mono (P : Population κ) (g h : (Finset κ → ℝ) → ℝ)
    (hgh : ∀ w ∈ P.profiles, g w ≤ h w) : P.E g ≤ P.E h := by
  unfold Population.E
  exact Finset.sum_le_sum (fun w hw => mul_le_mul_of_nonneg_left (hgh w hw) (prob_nonneg P hw))

lemma Pr_mono (P : Population κ) (A B : (Finset κ → ℝ) → Prop)
    (hAB : ∀ w ∈ P.profiles, A w → B w) : P.Pr A ≤ P.Pr B := by
  unfold Population.Pr
  refine E_mono P _ _ (fun w hw => ?_)
  by_cases ha : A w
  · simp [ha, hAB w hw ha]
  · by_cases hb : B w <;> simp [ha, hb]

lemma Pr_congr (P : Population κ) (A B : (Finset κ → ℝ) → Prop)
    (hAB : ∀ w ∈ P.profiles, (A w ↔ B w)) : P.Pr A = P.Pr B :=
  le_antisymm (Pr_mono P A B (fun w hw h => (hAB w hw).mp h))
    (Pr_mono P B A (fun w hw h => (hAB w hw).mpr h))

lemma Pr_marg (P : Population κ) (T : Finset κ) (t : ℝ) :
    P.Pr (fun w => t < w T) = ∑ y ∈ P.supp T, P.f T y * (if t < y then 1 else 0) := by
  unfold Population.Pr
  exact E_marg P T (fun y => if t < y then 1 else 0)

/-- Lemma 5.9 / Corollary 5.9 core: probability some hyperedge exceeds t. -/
lemma Pr_exists_ge (P : Population κ) (t : ℝ) :
    1 - Real.exp (-(∑ T : Finset κ, P.Pr (fun w => t < w T))) ≤
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
  have hprod : (∏ T : Finset κ, (1 - P.Pr (fun w => t < w T))) ≤
      Real.exp (-(∑ T : Finset κ, P.Pr (fun w => t < w T))) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod (fun T _ => hq0 T) (fun T _ => ?_)
    have := Real.add_one_le_exp (-(P.Pr (fun w => t < w T)))
    linarith
  rw [hc, hall, Finset.prod_congr rfl (fun T _ => hq T)]
  linarith

lemma val_ge (P : Population κ) {w : Finset κ → ℝ} (hw : w ∈ P.profiles) {T : Finset κ}
    (hT : T ∈ P.C) : w T ≤ val P w Finset.univ := by
  unfold val
  have hmem : T ∈ feasible P Finset.univ :=
    Finset.mem_filter.mpr ⟨hT, Finset.subset_univ T⟩
  refine le_trans ?_ (Finset.le_sup' (fun T => ∑ U ∈ T.powerset, w U) hmem)
  exact Finset.single_le_sum (f := fun U => w U) (fun U _ => w_nonneg P hw U)
    (Finset.mem_powerset_self T)

lemma brev_bdd (P : Population κ) :
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

lemma brev_ge (P : Population κ) (p : ℝ) :
    p * P.Pr (fun w => p ≤ val P w Finset.univ) ≤ BREV P :=
  le_csSup (brev_bdd P) ⟨p, rfl⟩

lemma brev_nonneg (P : Population κ) : 0 ≤ BREV P := by
  have := brev_ge P 0
  simpa using this

/-- Corollary 5.9 (general form). -/

lemma E_sum (P : Population κ) {α : Type*} (s : Finset α) (g : α → (Finset κ → ℝ) → ℝ) :
    P.E (fun w => ∑ a ∈ s, g a w) = ∑ a ∈ s, P.E (g a) := by
  unfold Population.E
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

lemma update_mem (P : Population κ) {w : Finset κ → ℝ} (hw : w ∈ P.profiles) (T : Finset κ)
    {y : ℝ} (hy : y ∈ P.supp T) : Function.update w T y ∈ P.profiles := by
  unfold Population.profiles
  rw [Fintype.mem_piFinset]
  intro U
  by_cases hU : U = T
  · subst hU; simpa using hy
  · rw [Function.update_of_ne hU]; exact mem_supp P hw U

lemma prob_update (P : Population κ) (w : Finset κ → ℝ) (T : Finset κ) (y : ℝ) :
    P.prob (Function.update w T y) * P.f T (w T) = P.prob w * P.f T y := by
  unfold Population.prob
  have h1 : (∏ U : Finset κ, P.f U (Function.update w T y U)) =
      P.f T y * ∏ U ∈ Finset.univ \ {T}, P.f U (w U) := by
    have : (fun U => P.f U (Function.update w T y U)) =
        Function.update (fun U => P.f U (w U)) T (P.f T y) := by
      funext U
      exact Function.apply_update (fun U => P.f U) w T y U
    rw [this, Finset.prod_update_of_mem (Finset.mem_univ T)]
  have h2 : (∏ U : Finset κ, P.f U (w U)) =
      P.f T (w T) * ∏ U ∈ Finset.univ \ {T}, P.f U (w U) := by
    exact Finset.prod_eq_mul_prod_diff_singleton T _ (fun h => absurd (Finset.mem_univ T) h)
  rw [h1, h2]; ring

/-- Independence of coordinate `T` from the others. -/
lemma E_indep (P : Population κ) (T : Finset κ) (F : ℝ → (Finset κ → ℝ) → ℝ)
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

end CRGen

namespace CRDis

universe u

irreducible_def n : ℕ := 80
irreducible_def M : ℕ := 4 ^ 100

abbrev ι := ULift.{u} (Fin n × Fin (M + 1))

noncomputable section

def H (k : Fin n) : ℝ := 4 ^ (k.val + 1)
def q (k : Fin n) : ℝ := (1 / 4) ^ (k.val + 1)
def δ (k : Fin n) : ℝ := 2 * H k / M
def r : ℝ := 4 / M

def blk (k : Fin n) : Finset ι.{u} := Finset.univ.filter (fun i => i.down.1 = k)
def noise (i : ι.{u}) : Prop := i.down.2 ≠ 0

instance (i : ι.{u}) : Decidable (noise i) := by unfold noise; infer_instance

lemma M_pos : (0 : ℝ) < M := by rw [M_def]; positivity
lemma one_lt_M : (1 : ℕ) < M + 1 := by rw [M_def]; omega

def a0 (k : Fin n) : ι.{u} := ⟨(k, 0)⟩
def a1 (k : Fin n) : ι.{u} := ⟨(k, ⟨1, one_lt_M⟩)⟩

lemma a0_mem (k : Fin n) : a0.{u} k ∈ blk.{u} k := by simp [blk, a0]
lemma a1_mem (k : Fin n) : a1.{u} k ∈ blk.{u} k := by simp [blk, a1]
lemma a0_ne_a1 (k : Fin n) : a0.{u} k ≠ a1.{u} k := by
  intro h
  have := congrArg (fun i : ι.{u} => (i.down.2 : ℕ)) h
  simp [a0, a1] at this

lemma blk_inj {k k' : Fin n} (h : blk.{u} k = blk.{u} k') : k = k' := by
  have := a0_mem.{u} k
  rw [h] at this
  simp [blk, a0] at this
  exact this

lemma blk_ne_single (k : Fin n) (i : ι.{u}) : blk.{u} k ≠ {i} := by
  intro h
  have h0 := a0_mem.{u} k
  have h1 := a1_mem.{u} k
  rw [h, Finset.mem_singleton] at h0 h1
  exact a0_ne_a1 k (h0.trans h1.symm)

lemma blk_nonempty (k : Fin n) : (blk.{u} k).Nonempty := ⟨_, a0_mem k⟩

def cls (T : Finset ι.{u}) : ℝ × ℝ :=
  if h : ∃ k, T = blk k then (H h.choose, q h.choose)
  else if h' : ∃ i : ι.{u}, noise i ∧ T = {i} then (δ h'.choose.down.1, r) else (0, 0)

lemma cls_blk (k : Fin n) : cls.{u} (blk k) = (H k, q k) := by
  have h : ∃ k', blk.{u} k = blk k' := ⟨k, rfl⟩
  unfold cls
  rw [dif_pos h]
  have := blk_inj h.choose_spec
  rw [← this]

lemma cls_noise (i : ι.{u}) (hi : noise i) : cls.{u} {i} = (δ i.down.1, r) := by
  have h1 : ¬ ∃ k, ({i} : Finset ι.{u}) = blk k := by
    rintro ⟨k, hk⟩; exact blk_ne_single k i hk.symm
  have h2 : ∃ j : ι.{u}, noise j ∧ ({i} : Finset ι.{u}) = {j} := ⟨i, hi, rfl⟩
  unfold cls
  rw [dif_neg h1, dif_pos h2]
  have := h2.choose_spec.2
  rw [Finset.singleton_inj] at this
  rw [← this]

lemma cls_other (T : Finset ι.{u}) (h1 : ∀ k, T ≠ blk k) (h2 : ∀ i, noise i → T ≠ {i}) :
    cls T = (0, 0) := by
  unfold cls
  rw [dif_neg (by rintro ⟨k, hk⟩; exact h1 k hk), dif_neg (by rintro ⟨i, hi, hT⟩; exact h2 i hi hT)]

lemma H_pos (k : Fin n) : 0 < H k := by unfold H; positivity
lemma q_pos (k : Fin n) : 0 < q k := by unfold q; positivity
lemma q_lt_one (k : Fin n) : q k < 1 := by
  unfold q
  exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
lemma Hq (k : Fin n) : H k * q k = 1 := by
  unfold H q; rw [← mul_pow]; norm_num
lemma δ_pos (k : Fin n) : 0 < δ k := by unfold δ; have := H_pos k; have := M_pos; positivity
lemma r_pos : 0 < r := by unfold r; have := M_pos; positivity
lemma r_lt_one : r < 1 := by
  unfold r
  rw [div_lt_one M_pos, M_def]; norm_num

lemma cls_cases (T : Finset ι.{u}) :
    (cls T).2 = 0 ∨ (0 < (cls T).1 ∧ 0 < (cls T).2 ∧ (cls T).2 < 1) := by
  by_cases h1 : ∃ k, T = blk k
  · obtain ⟨k, rfl⟩ := h1
    rw [cls_blk]; exact Or.inr ⟨H_pos k, q_pos k, q_lt_one k⟩
  · by_cases h2 : ∃ i, noise i ∧ T = {i}
    · obtain ⟨i, hi, rfl⟩ := h2
      rw [cls_noise i hi]; exact Or.inr ⟨δ_pos _, r_pos, r_lt_one⟩
    · left
      rw [cls_other T (fun k hk => h1 ⟨k, hk⟩) (fun i hi hT => h2 ⟨i, hi, hT⟩)]

def supp (T : Finset ι.{u}) : Finset ℝ :=
  if (cls T).2 = 0 then {0} else {0, (cls T).1}

def ff (T : Finset ι.{u}) (y : ℝ) : ℝ :=
  if (cls T).2 = 0 then (if y = 0 then 1 else 0)
  else (if y = (cls T).1 then (cls T).2 else if y = 0 then 1 - (cls T).2 else 0)

lemma cls_empty : cls.{u} (∅ : Finset ι.{u}) = (0, 0) := by
  refine cls_other _ (fun k hk => ?_) (fun i _ hT => ?_)
  · have := blk_nonempty.{u} k; rw [← hk] at this; simp at this
  · have := Finset.singleton_nonempty i; rw [← hT] at this; simp at this

def P : Population ι.{u} where
  C := Finset.univ
  C_down := fun _ _ _ _ => Finset.mem_univ _
  empty_mem := Finset.mem_univ _
  supp := supp
  f := ff
  supp_nonneg := by
    intro T y hy
    unfold supp at hy
    split_ifs at hy with h
    · simp at hy; rw [hy]
    · rcases cls_cases T with h' | ⟨h1, _, _⟩
      · exact absurd h' h
      · simp at hy; rcases hy with hy | hy <;> rw [hy]; exact h1.le
  f_pos := by
    intro T y hy
    unfold supp at hy; unfold ff
    by_cases h : (cls T).2 = 0
    · rw [if_pos h] at hy ⊢; simp at hy; simp [hy]
    · rw [if_neg h] at hy ⊢
      rcases cls_cases T with h' | ⟨h1, h2, h3⟩
      · exact absurd h' h
      simp at hy
      rcases hy with rfl | rfl
      · have : (0:ℝ) ≠ (cls T).1 := ne_of_lt h1
        simp [this]; linarith
      · simp; exact h2
  f_zero := by
    intro T y hy
    unfold supp at hy; unfold ff
    split_ifs at hy ⊢ with h h2 h3 <;> simp_all
  f_sum := by
    intro T
    unfold supp ff
    split_ifs with h
    · simp
    · rcases cls_cases T with h' | ⟨h1, _, _⟩
      · exact absurd h' h
      · have hne : (0 : ℝ) ≠ (cls T).1 := ne_of_lt h1
        rw [Finset.sum_pair hne]
        simp [hne.symm, hne]
  zero_off_C := fun T hT => absurd (Finset.mem_univ T) hT
  zero_empty := by
    show supp ∅ = {0}
    unfold supp; rw [cls_empty]; simp

lemma P_supp (T : Finset ι.{u}) : P.{u}.supp T = supp T := rfl
lemma P_f (T : Finset ι.{u}) (y : ℝ) : P.{u}.f T y = ff T y := rfl

lemma supp_blk (k : Fin n) : P.{u}.supp (blk k) = {0, H k} := by
  rw [P_supp]; unfold supp; rw [cls_blk]; simp [(q_pos k).ne']

lemma f_blk_H (k : Fin n) : P.{u}.f (blk k) (H k) = q k := by
  rw [P_f]; unfold ff; rw [cls_blk]; simp [(q_pos k).ne']

lemma f_blk_0 (k : Fin n) : P.{u}.f (blk k) 0 = 1 - q k := by
  rw [P_f]; unfold ff; rw [cls_blk]; simp [(q_pos k).ne', (H_pos k).ne]

lemma supp_noise (i : ι.{u}) (hi : noise i) : P.{u}.supp {i} = {0, δ i.down.1} := by
  rw [P_supp]; unfold supp; rw [cls_noise i hi]; simp [r_pos.ne']

lemma f_noise_δ (i : ι.{u}) (hi : noise i) : P.{u}.f {i} (δ i.down.1) = r := by
  rw [P_f]; unfold ff; rw [cls_noise i hi]; simp [r_pos.ne']

lemma f_noise_0 (i : ι.{u}) (hi : noise i) : P.{u}.f {i} 0 = 1 - r := by
  rw [P_f]; unfold ff; rw [cls_noise i hi]; simp [r_pos.ne', (δ_pos _).ne]

lemma supp_other (T : Finset ι.{u}) (h1 : ∀ k, T ≠ blk k) (h2 : ∀ i, noise i → T ≠ {i}) :
    P.{u}.supp T = {0} := by
  rw [P_supp]; unfold supp; rw [cls_other T h1 h2]; simp

lemma w_blk {w : Finset ι.{u} → ℝ} (hw : w ∈ P.{u}.profiles) (k : Fin n) :
    w (blk k) = 0 ∨ w (blk k) = H k := by
  have := CRGen.mem_supp P hw (blk k)
  rw [supp_blk] at this; simpa using this

lemma w_noise {w : Finset ι.{u} → ℝ} (hw : w ∈ P.{u}.profiles) (i : ι.{u}) (hi : noise i) :
    w {i} = 0 ∨ w {i} = δ i.down.1 := by
  have := CRGen.mem_supp P hw {i}
  rw [supp_noise i hi] at this; simpa using this

lemma w_other {w : Finset ι.{u} → ℝ} (hw : w ∈ P.{u}.profiles) (T : Finset ι.{u})
    (h1 : ∀ k, T ≠ blk k) (h2 : ∀ i, noise i → T ≠ {i}) : w T = 0 := by
  have := CRGen.mem_supp P hw T
  rw [supp_other T h1 h2] at this; simpa using this

lemma val_eq_sum {w : Finset ι.{u} → ℝ} (hw : w ∈ P.{u}.profiles) (S : Finset ι.{u}) :
    val P w S = ∑ U ∈ S.powerset, w U := by
  unfold val
  apply le_antisymm
  · refine Finset.sup'_le _ _ (fun T hT => ?_)
    have hTS : T ⊆ S := (Finset.mem_filter.mp hT).2
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.powerset_mono.mpr hTS)
      (fun U _ _ => CRGen.w_nonneg P hw U)
  · have hS : S ∈ feasible P S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl _⟩
    exact Finset.le_sup' (fun T => ∑ U ∈ T.powerset, w U) hS

lemma w_decomp {w : Finset ι.{u} → ℝ} (hw : w ∈ P.{u}.profiles) (U : Finset ι.{u}) :
    w U = (∑ k : Fin n, if U = blk k then w (blk k) else 0) +
      ∑ i : ι.{u}, if noise i ∧ U = {i} then w {i} else 0 := by
  by_cases h1 : ∃ k, U = blk k
  · obtain ⟨k0, rfl⟩ := h1
    have e1 : (∑ k : Fin n, if blk.{u} k0 = blk k then w (blk k) else 0) = w (blk k0) := by
      rw [Finset.sum_eq_single k0]
      · simp
      · intro k _ hk; rw [if_neg (fun h => hk (blk_inj h).symm)]
      · intro h; exact absurd (Finset.mem_univ _) h
    have e2 : (∑ i : ι.{u}, if noise i ∧ blk k0 = {i} then w {i} else 0) = 0 :=
      Finset.sum_eq_zero (fun i _ => if_neg (fun h => blk_ne_single k0 i h.2))
    rw [e1, e2, add_zero]
  · by_cases h2 : ∃ i, noise i ∧ U = {i}
    · obtain ⟨i0, hi0, rfl⟩ := h2
      have e1 : (∑ k : Fin n, if ({i0} : Finset ι.{u}) = blk k then w (blk k) else 0) = 0 :=
        Finset.sum_eq_zero (fun k _ => if_neg (fun h => blk_ne_single k i0 h.symm))
      have e2 : (∑ i : ι.{u}, if noise i ∧ ({i0} : Finset ι.{u}) = {i} then w {i} else 0) =
          w {i0} := by
        rw [Finset.sum_eq_single i0]
        · simp [hi0]
        · intro i _ hi
          rw [if_neg]
          rintro ⟨_, h⟩
          exact hi (Finset.singleton_inj.mp h).symm
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [e1, e2, zero_add]
    · have h1' : ∀ k, U ≠ blk k := fun k hk => h1 ⟨k, hk⟩
      have h2' : ∀ i, noise i → U ≠ {i} := fun i hi hU => h2 ⟨i, hi, hU⟩
      rw [w_other hw U h1' h2']
      rw [Finset.sum_eq_zero (fun k _ => if_neg (h1' k)),
        Finset.sum_eq_zero (fun i _ => if_neg (fun h => h2' i h.1 h.2))]
      simp

lemma val_formula {w : Finset ι.{u} → ℝ} (hw : w ∈ P.{u}.profiles) (S : Finset ι.{u}) :
    val P w S = (∑ k : Fin n, if blk k ⊆ S then w (blk k) else 0) +
      ∑ i : ι.{u}, if noise i ∧ i ∈ S then w {i} else 0 := by
  rw [val_eq_sum hw]
  rw [Finset.sum_congr rfl (fun U _ => w_decomp hw U), Finset.sum_add_distrib,
    Finset.sum_comm, Finset.sum_comm (s := S.powerset)]
  congr 1
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_ite_eq' S.powerset (blk k) (fun _ => w (blk k))]
    simp [Finset.mem_powerset]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : noise i
    · simp only [hi, true_and]
      rw [Finset.sum_ite_eq' S.powerset {i} (fun _ => w {i})]
      simp [Finset.mem_powerset]
    · simp [hi]

lemma f_other0 (T : Finset ι.{u}) (h1 : ∀ k, T ≠ blk k) (h2 : ∀ i, noise i → T ≠ {i}) :
    P.{u}.f T 0 = 1 := by
  rw [P_f]; unfold ff; rw [cls_other T h1 h2]; simp

lemma hasComp : HasComplementarity P.{u} 2 := by
  intro i
  have hsub : (Finset.univ.filter (fun T : Finset ι.{u} => i ∈ T ∧ P.f T 0 < 1)) ⊆
      {blk i.down.1, {i}} := by
    intro T hT
    obtain ⟨hiT, hf⟩ := (Finset.mem_filter.mp hT).2
    by_cases h1 : ∃ k, T = blk k
    · obtain ⟨k, rfl⟩ := h1
      have : i.down.1 = k := (Finset.mem_filter.mp hiT).2
      rw [this]; simp
    · by_cases h2 : ∃ j, noise j ∧ T = {j}
      · obtain ⟨j, _, rfl⟩ := h2
        rw [Finset.mem_singleton] at hiT
        rw [hiT]; simp
      · rw [f_other0 T (fun k hk => h1 ⟨k, hk⟩) (fun j hj hT => h2 ⟨j, hj, hT⟩)] at hf
        exact absurd hf (lt_irrefl _)
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

def BK (K : Finset (Fin n)) : Finset ι.{u} := Finset.univ.filter (fun i => i.down.1 ∈ K)

def price (k : Fin n) : ℝ := H k - 1

def uv (v : Finset ι.{u} → ℝ) (K : Finset (Fin n)) : ℝ := v (BK K) - ∑ k ∈ K, price k

lemma exists_opt (v : Finset ι.{u} → ℝ) :
    ∃ K ∈ (Finset.univ : Finset (Finset (Fin n))), ∀ K' ∈ (Finset.univ : Finset (Finset (Fin n))),
      uv v K' ≤ uv v K :=
  Finset.exists_max_image _ (uv v) Finset.univ_nonempty

def Kopt (v : Finset ι.{u} → ℝ) : Finset (Fin n) := (exists_opt v).choose

lemma Kopt_max (v : Finset ι.{u} → ℝ) (K : Finset (Fin n)) : uv v K ≤ uv v (Kopt v) :=
  (exists_opt v).choose_spec.2 K (Finset.mem_univ _)

def mech : Mech ι.{u} where
  X := fun v S => if S = BK (Kopt v) then 1 else 0
  p := fun v => ∑ k ∈ Kopt v, price k

lemma util_mech (v r : Finset ι.{u} → ℝ) : util v mech r = uv v (Kopt r) := by
  unfold util uv mech
  simp only
  rw [Finset.sum_congr rfl (fun S _ => by rw [ite_mul, one_mul, zero_mul])]
  rw [Finset.sum_ite_eq' Finset.univ (BK (Kopt r)) (fun S => v S)]
  simp

lemma val_empty {w : Finset ι.{u} → ℝ} (hw : w ∈ P.{u}.profiles) : val P w ∅ = 0 := by
  rw [val_eq_sum hw]
  simp only [Finset.powerset_empty, Finset.sum_singleton]
  have := CRGen.mem_supp P hw ∅
  rw [P.zero_empty] at this
  simpa using this

lemma BK_empty : BK.{u} ∅ = ∅ := by
  unfold BK; simp

lemma truthful : IsTruthful P.{u} mech := by
  refine ⟨fun v _ => ⟨fun S => ?_, ?_⟩, fun v _ r _ => ?_, fun v hv => ?_⟩
  · unfold mech; simp only; split_ifs <;> norm_num
  · unfold mech; simp only
    rw [Finset.sum_ite_eq' Finset.univ (BK (Kopt v)) (fun _ => (1:ℝ))]; simp
  · rw [util_mech, util_mech]; exact Kopt_max v _
  · rw [util_mech]
    refine le_trans ?_ (Kopt_max v ∅)
    unfold uv
    rw [BK_empty, Finset.sum_empty, sub_zero]
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    rw [val_empty hw]

lemma blk_sub_BK (k : Fin n) (K : Finset (Fin n)) : blk.{u} k ⊆ BK K ↔ k ∈ K := by
  constructor
  · intro h
    have := h (a0_mem k)
    unfold BK a0 at this; simpa using this
  · intro hk i hi
    unfold blk at hi; unfold BK
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [hi]; exact hk

lemma mem_BK (i : ι.{u}) (K : Finset (Fin n)) : i ∈ BK K ↔ i.down.1 ∈ K := by
  unfold BK; simp

lemma val_BK {w : Finset ι.{u} → ℝ} (hw : w ∈ P.{u}.profiles) (K : Finset (Fin n)) :
    val P w (BK K) = (∑ k : Fin n, if k ∈ K then w (blk k) else 0) +
      ∑ i : ι.{u}, if noise i ∧ i.down.1 ∈ K then w {i} else 0 := by
  rw [val_formula hw]
  congr 1
  · exact Finset.sum_congr rfl (fun k _ => by rw [if_congr (blk_sub_BK k K) rfl rfl])
  · exact Finset.sum_congr rfl (fun i _ => by
      rw [if_congr (and_congr_right_iff.mpr (fun _ => mem_BK i K)) rfl rfl])

lemma price_pos (k : Fin n) : 0 < price k := by
  unfold price H
  have : (4:ℝ) ≤ 4 ^ (k.val + 1) := by
    calc (4:ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ (k.val + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

lemma Kopt_contains {w : Finset ι.{u} → ℝ} (hw : w ∈ P.{u}.profiles) (k : Fin n)
    (hk : w (blk k) = H k) : k ∈ Kopt (val P w) := by
  by_contra hnot
  set K := Kopt (val P w) with hK
  have hmax := Kopt_max (val P w) (insert k K)
  rw [← hK] at hmax
  unfold uv at hmax
  rw [val_BK hw, val_BK hw, Finset.sum_insert hnot] at hmax
  have e1 : (∑ k' : Fin n, if k' ∈ insert k K then w (blk k') else 0) =
      w (blk k) + ∑ k' : Fin n, if k' ∈ K then w (blk k') else 0 := by
    have hs : w (blk k) = ∑ k' : Fin n, if k' = k then w (blk k') else 0 := by simp
    rw [hs, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k' _ => ?_)
    by_cases h1 : k' = k
    · subst h1; simp [hnot]
    · simp [Finset.mem_insert, h1]
  have e2 : (∑ i : ι.{u}, if noise i ∧ i.down.1 ∈ K then w {i} else 0) ≤
      ∑ i : ι.{u}, if noise i ∧ i.down.1 ∈ insert k K then w {i} else 0 := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    by_cases h : noise i ∧ i.down.1 ∈ K
    · rw [if_pos h, if_pos ⟨h.1, Finset.mem_insert_of_mem h.2⟩]
    · rw [if_neg h]; split_ifs
      · exact CRGen.w_nonneg P hw _
      · exact le_refl _
  rw [e1, hk] at hmax
  unfold price at hmax
  linarith

lemma geom_q (N : ℕ) : (∑ j ∈ Finset.range N, ((1:ℝ) / 4) ^ (j + 1)) = (1 - (1/4) ^ N) / 3 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; ring

lemma sum_q_le : (∑ k : Fin n, q k) ≤ 1 / 3 := by
  unfold q
  rw [Fin.sum_univ_eq_sum_range (fun j => ((1:ℝ) / 4) ^ (j + 1)) n, geom_q]
  have : (0:ℝ) ≤ (1/4) ^ n := by positivity
  linarith

lemma revenue_ge : (n : ℝ) - 1 / 3 ≤ revenue P.{u} mech := by
  unfold revenue
  have hpt : ∀ w ∈ P.{u}.profiles,
      (∑ k : Fin n, if w (blk k) = H k then price k else 0) ≤ mech.p (val P w) := by
    intro w hw
    unfold mech; simp only
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => (price_pos k).le)
    intro k hk
    exact Kopt_contains hw k (Finset.mem_filter.mp hk).2
  refine le_trans ?_ (CRGen.E_mono P _ _ hpt)
  rw [CRGen.E_sum]
  have hk : ∀ k : Fin n, P.{u}.E (fun w => if w (blk k) = H k then price k else 0) =
      1 - q k := by
    intro k
    rw [CRGen.E_marg P (blk k) (fun y => if y = H k then price k else 0), supp_blk,
      Finset.sum_pair (H_pos k).ne, f_blk_0, f_blk_H]
    simp only [if_neg (H_pos k).ne, mul_zero, zero_add, if_true]
    unfold price; have := Hq k; linear_combination this
  rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  linarith [sum_q_le]

lemma head_sum (N : ℕ) : ∀ t : ℝ, (∑ j ∈ Finset.range N,
    (if (4:ℝ) ^ (j + 1) < t then (4:ℝ) ^ (j + 1) else 0)) ≤ max 0 ((4 * t - 4) / 3) := by
  induction N with
  | zero => intro t; simp
  | succ N ih =>
    intro t
    rw [Finset.sum_range_succ']
    by_cases ht : t ≤ 4
    · have h0 : ∀ j ∈ Finset.range N,
          (if (4:ℝ) ^ (j + 1 + 1) < t then (4:ℝ) ^ (j + 1 + 1) else 0) = 0 := by
        intro j _
        rw [if_neg]
        push Not
        calc t ≤ 4 := ht
          _ = 4 ^ 1 := by norm_num
          _ ≤ 4 ^ (j + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      rw [Finset.sum_eq_zero h0, if_neg (by norm_num; linarith)]
      simp
    · push Not at ht
      have e : ∀ j ∈ Finset.range N,
          (if (4:ℝ) ^ (j + 1 + 1) < t then (4:ℝ) ^ (j + 1 + 1) else 0) =
            4 * (if (4:ℝ) ^ (j + 1) < t / 4 then (4:ℝ) ^ (j + 1) else 0) := by
        intro j _
        have : (4:ℝ) ^ (j + 1 + 1) = 4 * 4 ^ (j + 1) := by ring
        rw [this]
        by_cases h : (4:ℝ) ^ (j + 1) < t / 4
        · rw [if_pos h, if_pos (by linarith)]
        · rw [if_neg h, if_neg (by linarith)]; ring
      rw [Finset.sum_congr rfl e, ← Finset.mul_sum, if_pos (by norm_num; linarith)]
      have := ih (t / 4)
      have hm : max 0 ((4 * (t / 4) - 4) / 3) = (t - 4) / 3 := by
        rw [max_eq_right]; ring_nf; linarith
      rw [hm] at this
      have : (4:ℝ) * (t - 4) / 3 + 4 ^ (0 + 1) = (4 * t - 4) / 3 := by ring
      rw [le_max_iff]; right
      nlinarith

lemma tail_sum (N : ℕ) : ∀ u : ℝ, 0 < u → (∑ j ∈ Finset.range N,
    (if u ≤ (4:ℝ) ^ (j + 1) then ((1:ℝ) / 4) ^ (j + 1) else 0)) ≤ 4 / 3 / u := by
  induction N with
  | zero => intro u hu; simp; positivity
  | succ N ih =>
    intro u hu
    by_cases hu4 : u ≤ 4
    · have hle : (∑ j ∈ Finset.range (N + 1),
          (if u ≤ (4:ℝ) ^ (j + 1) then ((1:ℝ) / 4) ^ (j + 1) else 0)) ≤
          ∑ j ∈ Finset.range (N + 1), ((1:ℝ) / 4) ^ (j + 1) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        split_ifs
        · exact le_refl _
        · positivity
      rw [geom_q] at hle
      have h1 : (1 - ((1:ℝ)/4) ^ (N + 1)) / 3 ≤ 1 / 3 := by
        have : (0:ℝ) ≤ (1/4) ^ (N + 1) := by positivity
        linarith
      have h2 : (1:ℝ) / 3 ≤ 4 / 3 / u := by
        rw [div_div, le_div_iff₀ (by positivity)]; nlinarith
      linarith
    · push Not at hu4
      rw [Finset.sum_range_succ']
      have e : ∀ j ∈ Finset.range N,
          (if u ≤ (4:ℝ) ^ (j + 1 + 1) then ((1:ℝ) / 4) ^ (j + 1 + 1) else 0) =
            (1 / 4) * (if u / 4 ≤ (4:ℝ) ^ (j + 1) then ((1:ℝ) / 4) ^ (j + 1) else 0) := by
        intro j _
        have h4 : (4:ℝ) ^ (j + 1 + 1) = 4 * 4 ^ (j + 1) := by ring
        rw [h4]
        by_cases h : u / 4 ≤ (4:ℝ) ^ (j + 1)
        · rw [if_pos h, if_pos (by linarith)]; ring
        · rw [if_neg h, if_neg (by linarith)]; ring
      rw [Finset.sum_congr rfl e, ← Finset.mul_sum, if_neg (by norm_num; linarith)]
      have := ih (u / 4) (by positivity)
      have h3 : (1:ℝ) / 4 * (4 / 3 / (u / 4)) = 4 / 3 / u := by field_simp
      nlinarith

lemma H_mono_sum_head (t : ℝ) (ht : 0 < t) :
    (∑ k : Fin n, if H k < t then H k else 0) < 2 / 3 * (2 * t) := by
  have := head_sum n t
  unfold H
  rw [Fin.sum_univ_eq_sum_range (fun j => if (4:ℝ) ^ (j + 1) < t then (4:ℝ) ^ (j + 1) else 0) n]
  have h2 : max 0 ((4 * t - 4) / 3) < 2 / 3 * (2 * t) := by
    rw [max_lt_iff]; constructor <;> linarith
  linarith

lemma q_tail_sum (u : ℝ) (hu : 0 < u) :
    (∑ k : Fin n, if u ≤ H k then q k else 0) ≤ 4 / 3 / u := by
  have := tail_sum n u hu
  unfold H q
  rw [Fin.sum_univ_eq_sum_range (fun j => if u ≤ (4:ℝ) ^ (j + 1) then ((1:ℝ) / 4) ^ (j + 1) else 0) n]
  exact this

lemma val_univ {w : Finset ι.{u} → ℝ} (hw : w ∈ P.{u}.profiles) :
    val P w Finset.univ = (∑ k : Fin n, w (blk k)) +
      ∑ i : ι.{u}, if noise i then w {i} else 0 := by
  rw [val_formula hw]
  simp

lemma E_noise_le : P.{u}.E (fun w => ∑ i : ι.{u}, if noise i then w {i} else 0) ≤ 1 / 1000 := by
  rw [CRGen.E_sum]
  have hterm : ∀ i : ι.{u}, P.{u}.E (fun w => if noise i then w {i} else 0) ≤
      r * (2 * 4 ^ n / M) := by
    intro i
    by_cases hi : noise i
    · simp only [hi, if_true]
      rw [CRGen.E_marg P {i} (fun y => y), supp_noise i hi,
        Finset.sum_pair (δ_pos _).ne, f_noise_0 i hi, f_noise_δ i hi]
      simp only [mul_zero, zero_add]
      refine mul_le_mul_of_nonneg_left ?_ r_pos.le
      unfold δ H
      have hk : (4:ℝ) ^ (i.down.1.val + 1) ≤ 4 ^ n :=
        pow_le_pow_right₀ (by norm_num) (by have := i.down.1.isLt; omega)
      have := M_pos
      gcongr
    · simp only [hi, if_false]
      unfold Population.E; simp only [mul_zero, Finset.sum_const_zero]
      have := M_pos; unfold r; positivity
  refine le_trans (Finset.sum_le_sum (fun i _ => hterm i)) ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card ι.{u} : ℝ) = n * (M + 1) := by
    simp [Fintype.card_ulift, Fintype.card_prod, Fintype.card_fin]
  rw [hc]
  unfold r
  rw [n_def, M_def]
  norm_num

open Classical in
lemma Pr_nonneg' (A : (Finset ι.{u} → ℝ) → Prop) : 0 ≤ P.{u}.Pr A := by
  unfold Population.Pr
  have := CRGen.E_mono P (fun _ => 0) (fun w => if A w then 1 else 0)
    (fun w _ => by split_ifs <;> norm_num)
  unfold Population.E at this ⊢
  simpa using this

lemma brev_le : BREV P.{u} ≤ 3 := by
  unfold BREV
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨p, rfl⟩
  simp only
  by_cases hp : p ≤ 0
  · have := Pr_nonneg' (fun w => p ≤ val P w Finset.univ)
    nlinarith
  push Not at hp
  set s := 19 / 20 * p with hs
  have hpt : ∀ w ∈ P.{u}.profiles,
      (if p ≤ val P w Finset.univ then (1:ℝ) else 0) ≤
        (∑ k : Fin n, if s / 2 ≤ H k then (if w (blk k) = H k then 1 else 0) else 0) +
          (20 / p) * (∑ i : ι.{u}, if noise i then w {i} else 0) := by
    intro w hw
    have hN0 : 0 ≤ ∑ i : ι.{u}, if noise i then w {i} else 0 :=
      Finset.sum_nonneg (fun i _ => by split_ifs; exact CRGen.w_nonneg P hw _; exact le_refl _)
    have hS0 : 0 ≤ ∑ k : Fin n, if s / 2 ≤ H k then (if w (blk k) = H k then (1:ℝ) else 0) else 0 :=
      Finset.sum_nonneg (fun k _ => by split_ifs <;> norm_num)
    by_cases hv : p ≤ val P w Finset.univ
    · rw [if_pos hv]
      rw [val_univ hw] at hv
      set N := ∑ i : ι.{u}, if noise i then w {i} else 0 with hN
      by_cases hNp : p / 20 ≤ N
      · have : 1 ≤ 20 / p * N := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hp]; linarith
        linarith
      · push Not at hNp
        have hX : s < ∑ k : Fin n, w (blk k) := by rw [hs]; linarith
        by_contra hcon
        push Not at hcon
        have hall : ∀ k : Fin n, w (blk k) = H k → H k < s / 2 := by
          intro k hk
          by_contra hn
          push Not at hn
          have hle : (1:ℝ) ≤ ∑ k : Fin n, if s / 2 ≤ H k then
              (if w (blk k) = H k then (1:ℝ) else 0) else 0 := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), if_pos hn, if_pos hk]
            have : 0 ≤ ∑ x ∈ Finset.univ.erase k, if s / 2 ≤ H x then
                (if w (blk x) = H x then (1:ℝ) else 0) else 0 :=
              Finset.sum_nonneg (fun k _ => by split_ifs <;> norm_num)
            linarith
          have : 0 ≤ 20 / p * N := by positivity
          linarith
        have hXle : (∑ k : Fin n, w (blk k)) ≤ ∑ k : Fin n, if H k < s / 2 then H k else 0 := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          rcases w_blk hw k with h0 | h1
          · rw [h0]; split_ifs; exact (H_pos k).le; exact le_refl _
          · rw [h1, if_pos (hall k h1)]
        have := H_mono_sum_head (s / 2) (by positivity)
        linarith
    · rw [if_neg hv]; positivity
  have hE := CRGen.E_mono P _ _ hpt
  unfold Population.Pr
  rw [← CRGen.E_add] at hE
  have hE1 : P.{u}.E (fun w => ∑ k : Fin n, if s / 2 ≤ H k then
      (if w (blk k) = H k then (1:ℝ) else 0) else 0) = ∑ k : Fin n, if s / 2 ≤ H k then q k else 0 := by
    rw [CRGen.E_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : s / 2 ≤ H k
    · simp only [hk, if_true]
      rw [CRGen.E_marg P (blk k) (fun y => if y = H k then 1 else 0), supp_blk,
        Finset.sum_pair (H_pos k).ne, f_blk_0, f_blk_H]
      simp [(H_pos k).ne]
    · simp only [hk, if_false]
      unfold Population.E; simp
  have hE2 : P.{u}.E (fun w => 20 / p * ∑ i : ι.{u}, if noise i then w {i} else 0) =
      20 / p * P.{u}.E (fun w => ∑ i : ι.{u}, if noise i then w {i} else 0) := by
    unfold Population.E; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun w _ => by ring)
  rw [hE1, hE2] at hE
  have hq := q_tail_sum (s / 2) (by positivity)
  have hEN := E_noise_le.{u}
  have hpr : p * P.{u}.E (fun w => if p ≤ val P w Finset.univ then 1 else 0) ≤
      p * (4 / 3 / (s / 2) + 20 / p * (1 / 1000)) := by
    refine mul_le_mul_of_nonneg_left (le_trans hE ?_) hp.le
    have : 20 / p * P.{u}.E (fun w => ∑ i : ι.{u}, if noise i then w {i} else 0) ≤
        20 / p * (1 / 1000) := mul_le_mul_of_nonneg_left hEN (by positivity)
    linarith
  have hcalc : p * (4 / 3 / (s / 2) + 20 / p * (1 / 1000)) ≤ 3 := by
    rw [hs]; field_simp; norm_num
  linarith

lemma val_single {w : Finset ι.{u} → ℝ} (hw : w ∈ P.{u}.profiles) (j : ι.{u}) :
    val P w {j} = if noise j then w {j} else 0 := by
  rw [val_formula hw]
  have h1 : (∑ k : Fin n, if blk k ⊆ ({j} : Finset ι.{u}) then w (blk k) else 0) = 0 := by
    refine Finset.sum_eq_zero (fun k _ => if_neg ?_)
    intro h
    have h0 := h (a0_mem k); have h1 := h (a1_mem k)
    rw [Finset.mem_singleton] at h0 h1
    exact a0_ne_a1 k (h0.trans h1.symm)
  rw [h1, zero_add]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; rw [if_neg]; rintro ⟨_, hi⟩; exact hij (Finset.mem_singleton.mp hi)
  · intro h; exact absurd (Finset.mem_univ _) h

lemma sdiff_blk (S : Finset ι.{u}) (k : Fin n) :
    S \ blk k = S.filter (fun i => i.down.1 ≠ k) := by
  ext i; simp [blk]

lemma blk_sub_sdiff (S : Finset ι.{u}) (k k' : Fin n) (hk : k' ≠ k) :
    blk k' ⊆ S \ blk k ↔ blk k' ⊆ S := by
  constructor
  · intro h; exact h.trans Finset.sdiff_subset
  · intro h i hi
    rw [sdiff_blk, Finset.mem_filter]
    refine ⟨h hi, ?_⟩
    have : i.down.1 = k' := (Finset.mem_filter.mp hi).2
    rw [this]; exact hk

lemma val_diff {w : Finset ι.{u} → ℝ} (hw : w ∈ P.{u}.profiles) (S : Finset ι.{u}) (k : Fin n) :
    val P w S - val P w (S \ blk k) = (if blk k ⊆ S then w (blk k) else 0) +
      ∑ i : ι.{u}, if noise i ∧ i ∈ S ∧ i.down.1 = k then w {i} else 0 := by
  rw [val_formula hw, val_formula hw]
  have e1 : (∑ k' : Fin n, if blk k' ⊆ S then w (blk k') else 0) -
      (∑ k' : Fin n, if blk k' ⊆ S \ blk k then w (blk k') else 0) =
      if blk k ⊆ S then w (blk k) else 0 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single k]
    · have : ¬ blk k ⊆ S \ blk k := by
        intro h
        have := h (a0_mem k)
        rw [sdiff_blk, Finset.mem_filter] at this
        exact this.2 rfl
      rw [if_neg this, sub_zero]
    · intro k' _ hk'
      rw [if_congr (blk_sub_sdiff S k k' hk') rfl rfl, sub_self]
    · intro h; exact absurd (Finset.mem_univ _) h
  have e2 : (∑ i : ι.{u}, if noise i ∧ i ∈ S then w {i} else 0) -
      (∑ i : ι.{u}, if noise i ∧ i ∈ S \ blk k then w {i} else 0) =
      ∑ i : ι.{u}, if noise i ∧ i ∈ S ∧ i.down.1 = k then w {i} else 0 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [sdiff_blk]
    by_cases h1 : noise i <;> by_cases h2 : i ∈ S <;> by_cases h3 : i.down.1 = k <;>
      simp [h1, h2, h3]
  linarith

lemma price_diff (p : ι.{u} → ℝ) (S : Finset ι.{u}) (k : Fin n) :
    (∑ j ∈ S, p j) - (∑ j ∈ S \ blk k, p j) = ∑ j ∈ S.filter (fun i => i.down.1 = k), p j := by
  rw [sdiff_blk, ← Finset.sum_filter_add_sum_filter_not S (fun i => i.down.1 = k)]
  ring

def noiseBlk (k : Fin n) : Finset ι.{u} := Finset.univ.filter (fun i => i.down.1 = k ∧ noise i)

lemma card_noiseBlk (k : Fin n) : (noiseBlk.{u} k).card = M := by
  have : noiseBlk.{u} k = ((Finset.univ : Finset (Fin (M + 1))).erase 0).map
      ⟨fun j => (⟨(k, j)⟩ : ι.{u}), fun a b h => by
        have := congrArg (fun i : ι.{u} => i.down.2) h; simpa using this⟩ := by
    ext i
    constructor
    · intro h
      have h' := (Finset.mem_filter.mp h).2
      refine Finset.mem_map.mpr ⟨i.down.2, Finset.mem_erase.mpr ⟨h'.2, Finset.mem_univ _⟩, ?_⟩
      show (⟨(k, i.down.2)⟩ : ι.{u}) = i
      rw [← h'.1]
    · intro h
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, (Finset.mem_erase.mp hj).1⟩
  rw [this, Finset.card_map, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]
  simp

lemma δ_le (k : Fin n) : δ k ≤ 2 * 4 ^ n / M := by
  unfold δ H
  have hk : (4:ℝ) ^ (k.val + 1) ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) (by have := k.isLt; omega)
  have := M_pos
  gcongr

lemma δM (k : Fin n) : δ k * M = 2 * H k := by
  unfold δ; field_simp [M_pos.ne']

open Classical in
/-- Pointwise revenue bound for conservative item pricing. -/
lemma rev_pt (p : ι.{u} → ℝ) {w : Finset ι.{u} → ℝ} (hw : w ∈ P.{u}.profiles) :
    (∑ i : ι.{u}, Psold (val P w) p i * p i) ≤
      2 * 4 ^ n / M +
      (if (∀ i, noise i → p i < δ i.down.1 → w {i} = 0) then
        ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
          M ≤ 4 * (Finset.univ.filter (fun i : ι.{u} => i.down.1 = k ∧ noise i ∧ p i < δ i.down.1)).card),
          w (blk k) else 0) +
      3 * ∑ i : ι.{u}, (if noise i then w {i} else 0) := by
  set v := val P w with hv
  set Kset := Finset.univ.filter (fun k : Fin n =>
    M ≤ 4 * (Finset.univ.filter (fun i : ι.{u} => i.down.1 = k ∧ noise i ∧ p i < δ i.down.1)).card)
    with hKset
  have hδm : 0 ≤ 2 * (4:ℝ) ^ n / M := by have := M_pos; positivity
  have hN0 : 0 ≤ ∑ i : ι.{u}, (if noise i then w {i} else 0) :=
    Finset.sum_nonneg (fun i _ => by split_ifs; exact CRGen.w_nonneg P hw _; exact le_refl _)
  have hK0 : 0 ≤ ∑ k ∈ Kset, w (blk k) := Finset.sum_nonneg (fun k _ => CRGen.w_nonneg P hw _)
  have hvs : ∀ j, v {j} = if noise j then w {j} else 0 := fun j => val_single hw j
  have hvs_le : ∀ j, v {j} ≤ 2 * 4 ^ n / M := by
    intro j; rw [hvs]
    split_ifs with hj
    · rcases w_noise hw j hj with h | h
      · rw [h]; exact hδm
      · rw [h]; exact δ_le _
    · exact hδm
  have hps : ∀ i, Psold v p i = 0 ∨ (Psold v p i = 1 ∧ (∃ S, i ∈ S ∧ 0 < v S - ∑ j ∈ S, p j) ∧
      (∀ S, i ∉ S → v S - ∑ j ∈ S, p j ≤ 0)) := by
    intro i; unfold Psold; split_ifs with h
    · exact Or.inr ⟨rfl, h⟩
    · exact Or.inl rfl
  by_cases hA : ∃ j, 0 < v {j} - p j
  · -- a wanted singleton blocks every other item
    obtain ⟨j, hj⟩ := hA
    have hz : ∀ i, i ≠ j → Psold v p i = 0 := by
      intro i hij
      rcases hps i with h | ⟨_, _, h2⟩
      · exact h
      · have := h2 {j} (by simpa using hij)
        simp at this; linarith
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [hz i hij, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    have hrest : 0 ≤ (if (∀ i, noise i → p i < δ i.down.1 → w {i} = 0) then
        ∑ k ∈ Kset, w (blk k) else 0) := by split_ifs; exact hK0; exact le_refl _
    rcases hps j with h | ⟨h, _, _⟩
    · rw [h, zero_mul]; linarith
    · rw [h, one_mul]; have := hvs_le j; linarith
  · push Not at hA
    have hpos : ∀ i, 0 ≤ p i := by
      intro i
      have := hA i
      have h0 : 0 ≤ v {i} := by rw [hvs]; split_ifs; exact CRGen.w_nonneg P hw _; exact le_refl _
      linarith
    have hNCA : ∀ i, noise i → p i < δ i.down.1 → w {i} = 0 := by
      intro i hi hpi
      rcases w_noise hw i hi with h | h
      · exact h
      · have := hA i; rw [hvs, if_pos hi, h] at this; linarith
    rw [if_pos hNCA]
    set Z := Finset.univ.filter (fun i => Psold v p i = 1) with hZ
    have hrevZ : (∑ i : ι.{u}, Psold v p i * p i) = ∑ i ∈ Z, p i := by
      rw [hZ, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rcases hps i with h | ⟨h, _⟩
      · rw [h, zero_mul, if_neg (by norm_num)]
      · rw [h, one_mul, if_pos rfl]
    rw [hrevZ]
    by_cases hZe : Z = ∅
    · rw [hZe, Finset.sum_empty]; linarith
    obtain ⟨z, hzZ⟩ := Finset.nonempty_iff_ne_empty.mpr hZe
    have hzP : Psold v p z = 1 := (Finset.mem_filter.mp hzZ).2
    obtain ⟨S, hzS, hSpos⟩ : ∃ S, z ∈ S ∧ 0 < v S - ∑ j ∈ S, p j := by
      rcases hps z with h | ⟨_, h1, _⟩
      · rw [h] at hzP; norm_num at hzP
      · exact h1
    have hZS : ∀ i ∈ Z, i ∈ S := by
      intro i hi
      by_contra hn
      rcases hps i with h | ⟨_, _, h2⟩
      · rw [(Finset.mem_filter.mp hi).2] at h; norm_num at h
      · have := h2 S hn; linarith
    -- split the revenue by block
    rw [← Finset.sum_fiberwise Z (fun i : ι.{u} => i.down.1) p]
    have hN : (∑ i : ι.{u}, (if noise i then w {i} else 0)) =
        ∑ k : Fin n, ∑ i : ι.{u}, (if noise i ∧ i.down.1 = k then w {i} else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hi : noise i
      · simp [hi]
      · simp [hi]
    have hK : (∑ k ∈ Kset, w (blk k)) = ∑ k : Fin n, if k ∈ Kset then w (blk k) else 0 := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [hN, hK, Finset.mul_sum]
    have hblock : ∀ k : Fin n, (∑ i ∈ Z.filter (fun i => i.down.1 = k), p i) ≤
        (if k ∈ Kset then w (blk k) else 0) +
          3 * ∑ i : ι.{u}, (if noise i ∧ i.down.1 = k then w {i} else 0) := by
      intro k
      set Nk := ∑ i : ι.{u}, (if noise i ∧ i.down.1 = k then w {i} else 0) with hNk
      have hNk0 : 0 ≤ Nk :=
        Finset.sum_nonneg (fun i _ => by split_ifs; exact CRGen.w_nonneg P hw _; exact le_refl _)
      have hite0 : 0 ≤ (if k ∈ Kset then w (blk k) else 0) := by
        split_ifs; exact CRGen.w_nonneg P hw _; exact le_refl _
      by_cases hZk : Z.filter (fun i => i.down.1 = k) = ∅
      · rw [hZk, Finset.sum_empty]; linarith
      obtain ⟨z', hz'⟩ := Finset.nonempty_iff_ne_empty.mpr hZk
      obtain ⟨hz'Z, hz'k⟩ := Finset.mem_filter.mp hz'
      have hS' : v (S \ blk k) - ∑ j ∈ S \ blk k, p j ≤ 0 := by
        rcases hps z' with h | ⟨_, _, h2⟩
        · rw [(Finset.mem_filter.mp hz'Z).2] at h; norm_num at h
        · refine h2 _ ?_
          rw [sdiff_blk, Finset.mem_filter]; push Not; intro _; exact hz'k
      have hd := val_diff hw S k
      have hpd := price_diff p S k
      have hNkS : (∑ i : ι.{u}, if noise i ∧ i ∈ S ∧ i.down.1 = k then w {i} else 0) ≤ Nk := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        by_cases h : noise i ∧ i ∈ S ∧ i.down.1 = k
        · rw [if_pos h, if_pos ⟨h.1, h.2.2⟩]
        · rw [if_neg h]; split_ifs; exact CRGen.w_nonneg P hw _; exact le_refl _
      have hZsub : (∑ i ∈ Z.filter (fun i => i.down.1 = k), p i) ≤
          ∑ j ∈ S.filter (fun i => i.down.1 = k), p j := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hpos i)
        intro i hi
        obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨hZS i h1, h2⟩
      have hmain : (∑ j ∈ S.filter (fun i => i.down.1 = k), p j) <
          (if blk k ⊆ S then w (blk k) else 0) + Nk := by
        linarith
      by_cases hbS : blk k ⊆ S
      · rw [if_pos hbS] at hmain
        rcases w_blk hw k with h0 | h1
        · rw [h0] at hmain; linarith
        · by_cases hkK : k ∈ Kset
          · rw [if_pos hkK, h1]; rw [h1] at hmain; linarith
          · rw [if_neg hkK]
            -- the block's noncheap noise items already cost more than 3H/2
            have hcK : 4 * (Finset.univ.filter (fun i : ι.{u} =>
                i.down.1 = k ∧ noise i ∧ p i < δ i.down.1)).card < M := by
              rw [hKset, Finset.mem_filter] at hkK; push Not at hkK; exact hkK (Finset.mem_univ _)
            set NC := (noiseBlk.{u} k).filter (fun i => ¬ p i < δ i.down.1) with hNC
            have hcard : (Finset.univ.filter (fun i : ι.{u} =>
                i.down.1 = k ∧ noise i ∧ p i < δ i.down.1)).card + NC.card = M := by
              refine Eq.trans ?_ (card_noiseBlk.{u} k)
              rw [hNC]
              have := Finset.card_filter_add_card_filter_not
                (s := noiseBlk.{u} k) (fun i => p i < δ i.down.1)
              rw [← this]
              congr 2
              ext i; simp [noiseBlk, and_assoc]
            have hNCsub : NC ⊆ S.filter (fun i => i.down.1 = k) := by
              intro i hi
              obtain ⟨hi1, _⟩ := Finset.mem_filter.mp hi
              obtain ⟨hik, _⟩ := (Finset.mem_filter.mp hi1).2
              refine Finset.mem_filter.mpr ⟨hbS ?_, hik⟩
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hik⟩
            have hNCsum : (NC.card : ℝ) * δ k ≤ ∑ j ∈ S.filter (fun i => i.down.1 = k), p j := by
              refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hNCsub
                (fun i _ _ => hpos i))
              have : ∀ i ∈ NC, δ k ≤ p i := by
                intro i hi
                obtain ⟨hi1, hi2⟩ := Finset.mem_filter.mp hi
                obtain ⟨hik, _⟩ := (Finset.mem_filter.mp hi1).2
                rw [← hik]; push Not at hi2; exact hi2
              have := Finset.card_nsmul_le_sum NC p (δ k) this
              rw [nsmul_eq_mul] at this; exact this
            have hNCbig : (3:ℝ) * M < 4 * NC.card := by
              have : 3 * M < 4 * NC.card := by omega
              exact_mod_cast this
            have hδk := δM k
            have hδpos := δ_pos k
            have hMpos := M_pos
            have h32 : 3 / 2 * H k < (NC.card : ℝ) * δ k := by
              have : (NC.card : ℝ) * δ k * 4 > 3 * M * δ k := by nlinarith
              nlinarith
            rw [h1] at hmain
            linarith
      · rw [if_neg hbS] at hmain; linarith
    have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hblock k)
    rw [Finset.sum_add_distrib] at hsum
    linarith

lemma rM4 : r * (4 ^ 99 : ℕ) = 1 := by
  unfold r; rw [M_def]; push_cast; field_simp; norm_num

lemma pow_r_half : (1 - r) ^ (4 ^ 99 : ℕ) ≤ 1 / 2 := by
  have h1 : 1 - r ≤ Real.exp (-r) := by
    have := Real.add_one_le_exp (-r); linarith
  have h0 : 0 ≤ 1 - r := by linarith [r_lt_one]
  calc (1 - r) ^ (4 ^ 99 : ℕ) ≤ (Real.exp (-r)) ^ (4 ^ 99 : ℕ) := pow_le_pow_left₀ h0 h1 _
    _ = Real.exp (-(r * (4 ^ 99 : ℕ))) := by rw [← Real.exp_nat_mul]; ring_nf
    _ = Real.exp (-1) := by rw [rM4]
    _ ≤ 1 / 2 := by
      have := Real.exp_one_gt_d9
      rw [Real.exp_neg, ← one_div]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith

open Classical in
lemma E_NCA (p : ι.{u} → ℝ) (k : Fin n) :
    P.{u}.E (fun w => if (∀ i, noise i → p i < δ i.down.1 → w {i} = 0) then w (blk k) else 0) ≤
      (1 - r) ^ (Finset.univ.filter (fun i : ι.{u} => noise i ∧ p i < δ i.down.1)).card := by
  set CS : Finset (Finset ι.{u}) :=
    (Finset.univ.filter (fun i : ι.{u} => noise i ∧ p i < δ i.down.1)).image (fun i => {i}) with hCS
  set h : Finset ι.{u} → ℝ → ℝ := fun T y =>
    (if T = blk k then y else 1) * (if T ∈ CS then (if y = 0 then 1 else 0) else 1) with hh
  have hpt : ∀ w ∈ P.{u}.profiles,
      (if (∀ i, noise i → p i < δ i.down.1 → w {i} = 0) then w (blk k) else 0) ≤
        ∏ T, h T (w T) := by
    intro w hw
    simp only [hh]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ (blk k) (fun T => w T),
      if_pos (Finset.mem_univ _), Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_boole]
    by_cases hc : ∀ i, noise i → p i < δ i.down.1 → w {i} = 0
    · rw [if_pos hc, if_pos]
      · simp
      · intro T hT
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hT
        obtain ⟨hi1, hi2⟩ := (Finset.mem_filter.mp hi).2
        exact hc i hi1 hi2
    · rw [if_neg hc]
      split_ifs
      · simp only [mul_one]; exact CRGen.w_nonneg P hw _
      · simp
  refine le_trans (CRGen.E_mono P _ _ hpt) ?_
  rw [CRGen.E_prod]
  have hfac : ∀ T : Finset ι.{u}, (∑ y ∈ P.supp T, P.f T y * h T y) =
      if T ∈ CS then (1 - r) else 1 := by
    intro T
    simp only [hh]
    by_cases hT : T = blk k
    · subst hT
      have hnot : blk k ∉ CS := by
        intro hm
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
        exact blk_ne_single k i hi.symm
      rw [if_neg hnot, supp_blk, Finset.sum_pair (H_pos k).ne, f_blk_0, f_blk_H]
      simp only [if_neg hnot, mul_one]
      simp
      linarith [Hq k, mul_comm (H k) (q k)]
    · by_cases hT2 : T ∈ CS
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hT2
        obtain ⟨hi1, _⟩ := (Finset.mem_filter.mp hi).2
        rw [if_pos hT2, supp_noise i hi1, Finset.sum_pair (δ_pos _).ne, f_noise_0 i hi1,
          f_noise_δ i hi1]
        simp [hT, hT2, (δ_pos _).ne']
      · rw [if_neg hT2]
        simp only [hT, hT2, if_false, mul_one]
        exact P.f_sum T
  rw [Finset.prod_congr rfl (fun T _ => hfac T), Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const]
  rw [hCS, Finset.card_image_of_injective _ Finset.singleton_injective]

lemma E_const (c : ℝ) : P.{u}.E (fun _ => c) = c := by
  have h1 := CRGen.E_one P.{u}
  have : P.{u}.E (fun _ => c) = c * P.{u}.E (fun _ => 1) := by
    unfold Population.E; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun w _ => by ring)
  rw [this, h1, mul_one]

open Classical in
lemma srev_le : SREVstar P.{u} ≤ 3 := by
  unfold SREVstar
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨p, rfl⟩
  simp only
  set Kset := Finset.univ.filter (fun k : Fin n =>
    M ≤ 4 * (Finset.univ.filter (fun i : ι.{u} => i.down.1 = k ∧ noise i ∧ p i < δ i.down.1)).card)
    with hKset
  set C := (Finset.univ.filter (fun i : ι.{u} => noise i ∧ p i < δ i.down.1)).card with hC
  have hpt := fun w (hw : w ∈ P.{u}.profiles) => rev_pt p hw
  have hpt2 : ∀ w ∈ P.{u}.profiles, (∑ i : ι.{u}, Psold (val P w) p i * p i) ≤
      2 * 4 ^ n / M +
      (∑ k ∈ Kset, (if (∀ i, noise i → p i < δ i.down.1 → w {i} = 0) then w (blk k) else 0)) +
      3 * ∑ i : ι.{u}, (if noise i then w {i} else 0) := by
    intro w hw
    have := hpt w hw
    rw [← hKset] at this
    have e : (if (∀ i, noise i → p i < δ i.down.1 → w {i} = 0) then ∑ k ∈ Kset, w (blk k) else 0)
        = ∑ k ∈ Kset, (if (∀ i, noise i → p i < δ i.down.1 → w {i} = 0) then w (blk k) else 0) := by
      split_ifs <;> simp
    linarith
  refine le_trans (CRGen.E_mono P _ _ hpt2) ?_
  rw [← CRGen.E_add, ← CRGen.E_add, E_const, CRGen.E_sum]
  have hE3 : P.{u}.E (fun w => 3 * ∑ i : ι.{u}, (if noise i then w {i} else 0)) =
      3 * P.{u}.E (fun w => ∑ i : ι.{u}, (if noise i then w {i} else 0)) := by
    unfold Population.E; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun w _ => by ring)
  rw [hE3]
  have hN := E_noise_le.{u}
  have hsum : (∑ k ∈ Kset, P.{u}.E (fun w =>
      if (∀ i, noise i → p i < δ i.down.1 → w {i} = 0) then w (blk k) else 0)) ≤
      Kset.card * (1 - r) ^ C := by
    have := Finset.sum_le_sum (fun k (_ : k ∈ Kset) => E_NCA p k)
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  -- C ≥ |K| * 4^99
  have hCge : Kset.card * (4 ^ 99 : ℕ) ≤ C := by
    rw [hC, Finset.card_eq_sum_card_fiberwise (f := fun i : ι.{u} => i.down.1)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    calc Kset.card * (4 ^ 99 : ℕ) = ∑ k ∈ Kset, (4 ^ 99 : ℕ) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ k ∈ Kset, ((Finset.univ.filter (fun i : ι.{u} => noise i ∧ p i < δ i.down.1)).filter
            (fun i => i.down.1 = k)).card := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          have hk' := (Finset.mem_filter.mp hk).2
          have e : (Finset.univ.filter (fun i : ι.{u} => i.down.1 = k ∧ noise i ∧ p i < δ i.down.1))
              = ((Finset.univ.filter (fun i : ι.{u} => noise i ∧ p i < δ i.down.1)).filter
                (fun i => i.down.1 = k)) := by
            ext i; simp [and_comm, and_assoc]
          rw [e] at hk'
          have hM : M = 4 * (4 ^ 99 : ℕ) := by rw [M_def]; norm_num
          have h4 := hM.symm.trans_le hk'
          exact Nat.le_of_mul_le_mul_left h4 (by norm_num)
      _ ≤ ∑ k : Fin n, ((Finset.univ.filter (fun i : ι.{u} => noise i ∧ p i < δ i.down.1)).filter
            (fun i => i.down.1 = k)).card :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have h0r : 0 ≤ 1 - r := by linarith [r_lt_one]
  have hpow : (1 - r) ^ C ≤ (1 / 2) ^ Kset.card := by
    calc (1 - r) ^ C ≤ (1 - r) ^ (Kset.card * (4 ^ 99 : ℕ)) :=
          pow_le_pow_of_le_one h0r (by linarith [r_pos]) hCge
      _ = ((1 - r) ^ (4 ^ 99 : ℕ)) ^ Kset.card := by rw [← pow_mul, mul_comm]
      _ ≤ (1 / 2) ^ Kset.card := pow_le_pow_left₀ (pow_nonneg h0r _) pow_r_half _
  have hK1 : (Kset.card : ℝ) * (1 / 2) ^ Kset.card ≤ 1 := by
    have h2 : (Kset.card : ℝ) ≤ 2 ^ Kset.card := by
      exact_mod_cast (Nat.lt_two_pow_self).le
    rw [one_div_pow]
    rw [mul_one_div, div_le_one (by positivity)]
    exact h2
  have hKr : (Kset.card : ℝ) * (1 - r) ^ C ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left hpow (by positivity)) hK1
  have hδm : 2 * (4:ℝ) ^ n / M ≤ 1 / 1000 := by
    rw [n_def, M_def]; norm_num
  linarith

lemma prod_one_sub_ge {α : Type*} (s : Finset α) (x : α → ℝ) (h0 : ∀ a ∈ s, 0 ≤ x a)
    (h1 : ∀ a ∈ s, x a ≤ 1) : 1 - ∑ a ∈ s, x a ≤ ∏ a ∈ s, (1 - x a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hs := ih (fun b hb => h0 b (Finset.mem_insert_of_mem hb))
      (fun b hb => h1 b (Finset.mem_insert_of_mem hb))
    have hxa0 := h0 a (Finset.mem_insert_self a s)
    have hxa1 := h1 a (Finset.mem_insert_self a s)
    have hsum0 : 0 ≤ ∑ b ∈ s, x b := Finset.sum_nonneg (fun b hb => h0 b (Finset.mem_insert_of_mem hb))
    nlinarith

lemma qtl_blk (k : Fin n) : P.{u}.qtl (blk k) (H k) = P.{u}.f (blk k) (H k) := by
  unfold Population.qtl
  rw [supp_blk]
  have : (({0, H k} : Finset ℝ).filter (fun z => H k ≤ z)) = {H k} := by
    ext z; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h | h, h'⟩
      · rw [h] at h'; linarith [H_pos k]
      · exact h
    · intro h; exact ⟨Or.inr h, le_of_eq h.symm⟩
  rw [this, Finset.sum_singleton]

lemma qtl_nonneg (T : Finset ι.{u}) (y : ℝ) : 0 ≤ P.{u}.qtl T y := by
  unfold Population.qtl
  exact Finset.sum_nonneg (fun z hz => le_of_lt (P.f_pos T z (Finset.mem_filter.mp hz).1))

lemma qtl_le_one (T : Finset ι.{u}) (y : ℝ) : P.{u}.qtl T y ≤ 1 := by
  unfold Population.qtl
  rw [← P.f_sum T]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun z hz _ => le_of_lt (P.f_pos T z hz))

lemma cR_zero (T : Finset ι.{u}) : P.{u}.concaveRevenue T 0 ≤ 0 := by
  unfold Population.concaveRevenue
  refine csSup_le ⟨0, fun o => if o = none then 1 else 0, fun o => by dsimp only; split_ifs <;> norm_num,
    by simp, by simp, by simp⟩ ?_
  rintro r ⟨a, ha, _, hq, rfl⟩
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => mul_nonneg (ha (some y))
    (qtl_nonneg T y))).mp hq
  refine le_of_eq (Finset.sum_eq_zero (fun y hy => ?_))
  have := hz y hy
  calc a (some y) * (y * P.qtl T y) = y * (a (some y) * P.qtl T y) := by ring
    _ = 0 := by rw [this, mul_zero]

lemma cR_lower (k : Fin n) :
    H k * P.{u}.qtl (blk k) (H k) ≤ P.{u}.concaveRevenue (blk k) (P.{u}.qtl (blk k) (H k)) := by
  unfold Population.concaveRevenue
  refine le_csSup ⟨H k, ?_⟩ ⟨fun o => if o = some (H k) then 1 else 0,
    fun o => by dsimp only; split_ifs <;> norm_num, ?_, ?_, ?_⟩
  · rintro r ⟨a, ha, hsum, _, rfl⟩
    have hb : ∀ y ∈ P.{u}.supp (blk k), a (some y) * (y * P.qtl (blk k) y) ≤ a (some y) * H k := by
      intro y hy
      refine mul_le_mul_of_nonneg_left ?_ (ha _)
      rw [supp_blk] at hy
      have hy' : y = 0 ∨ y = H k := by simpa using hy
      have hq1 := qtl_le_one (blk k) y
      have hq0 := qtl_nonneg (blk k) y
      rcases hy' with rfl | rfl
      · simp; exact (H_pos k).le
      · nlinarith [H_pos k]
    refine le_trans (Finset.sum_le_sum hb) ?_
    rw [← Finset.sum_mul]
    have : ∑ y ∈ P.{u}.supp (blk k), a (some y) ≤ 1 := by have := ha none; linarith
    nlinarith [H_pos k]
  · rw [supp_blk, Finset.sum_pair (H_pos k).ne]; simp [(H_pos k).ne]
  · rw [supp_blk, Finset.sum_pair (H_pos k).ne]; simp [(H_pos k).ne]
  · rw [supp_blk, Finset.sum_pair (H_pos k).ne]; simp [(H_pos k).ne]

lemma phibar_ge (k : Fin n) : H k ≤ P.{u}.phibar (blk k) (H k) := by
  unfold Population.phibar
  have hq := qtl_blk.{u} k
  have hf : 0 < P.{u}.f (blk k) (H k) := by rw [f_blk_H]; exact q_pos k
  have h1 := cR_lower.{u} k
  rw [hq] at h1 ⊢
  rw [sub_self]
  have h0 := cR_zero.{u} (blk k)
  rw [le_div_iff₀ hf]
  linarith

lemma H_lt (j k : Fin n) (h : j < k) : H j < H k := by
  unfold H
  exact pow_lt_pow_right₀ (by norm_num) (by have : j.val < k.val := h; omega)

lemma H_ge4 (k : Fin n) : 4 ≤ H k := by
  unfold H
  calc (4:ℝ) = 4 ^ 1 := by norm_num
    _ ≤ 4 ^ (k.val + 1) := pow_le_pow_right₀ (by norm_num) (by omega)

lemma inRegion_of (rk : Finset ι.{u} → ℕ) {w : Finset ι.{u} → ℝ} (hw : w ∈ P.{u}.profiles)
    (k : Fin n) (hk : w (blk k) = H k) (hhi : ∀ j, k < j → w (blk j) = 0) :
    InRegion rk w (blk k) := by
  refine ⟨blk_nonempty k, fun T _ hT => Or.inl ?_⟩
  rw [hk]
  by_cases h1 : ∃ j, T = blk j
  · obtain ⟨j, rfl⟩ := h1
    have hjk : j ≠ k := fun h => hT (by rw [h])
    rcases lt_or_gt_of_ne hjk with hlt | hgt
    · rcases w_blk hw j with h | h
      · rw [h]; exact H_pos k
      · rw [h]; exact H_lt j k hlt
    · rw [hhi j hgt]; exact H_pos k
  · by_cases h2 : ∃ i, noise i ∧ T = {i}
    · obtain ⟨i, hi, rfl⟩ := h2
      have hsmall : 2 * (4:ℝ) ^ n / M < 4 := by rw [n_def, M_def]; norm_num
      rcases w_noise hw i hi with h | h
      · rw [h]; exact H_pos k
      · rw [h]; linarith [δ_le i.down.1, H_ge4 k]
    · rw [w_other hw T (fun j hj => h1 ⟨j, hj⟩) (fun i hi hT' => h2 ⟨i, hi, hT'⟩)]
      exact H_pos k

open Classical in
lemma single_ge (rk : Finset ι.{u} → ℕ) : (n : ℝ) * (2 / 3) ≤ SINGLE P.{u} rk := by
  unfold SINGLE
  set Hi : Fin n → Finset (Finset ι.{u}) := fun k =>
    (Finset.univ.filter (fun j : Fin n => k < j)).image blk with hHi
  set h : Fin n → Finset ι.{u} → ℝ → ℝ := fun k T y =>
    (if T = blk k then (if y = H k then H k else 0) else 1) *
      (if T ∈ Hi k then (if y = 0 then 1 else 0) else 1) with hh
  have hnot : ∀ k, blk k ∉ Hi k := by
    intro k hm
    obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp hm
    have := blk_inj hjk
    rw [this] at hj
    exact lt_irrefl _ (Finset.mem_filter.mp hj).2
  have hpt : ∀ w ∈ P.{u}.profiles, (∑ k : Fin n, ∏ T, h k T (w T)) ≤
      ∑ T : Finset ι.{u}, (if InRegion rk w T then max 0 (P.phibar T (w T)) else 0) := by
    intro w hw
    have hnn : ∀ T, 0 ≤ (if InRegion rk w T then max 0 (P.phibar T (w T)) else 0) := by
      intro T; split_ifs; exact le_max_left _ _; exact le_refl _
    have hsub : (∑ T ∈ Finset.univ.image blk,
        (if InRegion rk w T then max 0 (P.phibar T (w T)) else 0)) ≤
        ∑ T : Finset ι.{u}, (if InRegion rk w T then max 0 (P.phibar T (w T)) else 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun T _ _ => hnn T)
    rw [Finset.sum_image (fun a _ b _ hab => blk_inj hab)] at hsub
    refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) hsub
    simp only [hh]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ (blk k)
      (fun T => if w T = H k then H k else 0), if_pos (Finset.mem_univ _), Finset.prod_ite_mem,
      Finset.univ_inter, Finset.prod_boole]
    by_cases hc : w (blk k) = H k ∧ ∀ T ∈ Hi k, w T = 0
    · rw [if_pos hc.1, if_pos hc.2, mul_one]
      have hhi : ∀ j, k < j → w (blk j) = 0 := fun j hj =>
        hc.2 _ (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩)
      rw [if_pos (inRegion_of rk hw k hc.1 hhi), hc.1]
      exact le_trans (phibar_ge k) (le_max_right _ _)
    · refine le_trans (le_of_eq ?_) (hnn _)
      by_cases h1 : w (blk k) = H k
      · have h2 : ¬ ∀ T ∈ Hi k, w T = 0 := fun h2 => hc ⟨h1, h2⟩
        simp [h1, h2]
      · simp [h1]
  refine le_trans ?_ (CRGen.E_mono P _ _ hpt)
  rw [CRGen.E_sum]
  have hval : ∀ k, P.{u}.E (fun w => ∏ T, h k T (w T)) =
      ∏ j ∈ Finset.univ.filter (fun j : Fin n => k < j), (1 - q j) := by
    intro k
    rw [CRGen.E_prod]
    have hfac : ∀ T : Finset ι.{u}, (∑ y ∈ P.supp T, P.f T y * h k T y) =
        if T ∈ Hi k then P.f T 0 else 1 := by
      intro T
      simp only [hh]
      by_cases hT : T = blk k
      · subst hT
        rw [if_neg (hnot k), supp_blk, Finset.sum_pair (H_pos k).ne, f_blk_0, f_blk_H]
        simp only [if_neg (hnot k), mul_one]
        simp [(H_pos k).ne]
        linarith [Hq k, mul_comm (H k) (q k)]
      · by_cases hT2 : T ∈ Hi k
        · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hT2
          rw [if_pos hT2, supp_blk, Finset.sum_pair (H_pos j).ne]
          simp [hT, hT2, (H_pos j).ne']
        · rw [if_neg hT2]
          simp only [hT, hT2, if_false, mul_one]
          exact P.f_sum T
    rw [Finset.prod_congr rfl (fun T _ => hfac T), Finset.prod_ite_mem, Finset.univ_inter, hHi,
      Finset.prod_image (fun a _ b _ hab => blk_inj hab)]
    exact Finset.prod_congr rfl (fun j _ => f_blk_0 j)
  rw [Finset.sum_congr rfl (fun k _ => hval k)]
  have hlow : ∀ k : Fin n, (2:ℝ) / 3 ≤ ∏ j ∈ Finset.univ.filter (fun j : Fin n => k < j), (1 - q j) := by
    intro k
    refine le_trans ?_ (prod_one_sub_ge _ q (fun j _ => (q_pos j).le) (fun j _ => (q_lt_one j).le))
    have : (∑ j ∈ Finset.univ.filter (fun j : Fin n => k < j), q j) ≤ ∑ j : Fin n, q j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => (q_pos j).le)
    linarith [sum_q_le]
  have := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hlow k)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  linarith

end

end CRDis


theorem solution : ¬ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : Population ι) (d : ℕ)
    (hd : HasComplementarity P d) (rk : Finset ι → ℕ) (hrk : Function.Injective rk),
    SINGLE P rk ≤ 4 * (d : ℝ) * SREVstar P + 4 * BREV P) := by
  intro h
  set rk : Finset CRDis.ι → ℕ := fun T => (Fintype.equivFin (Finset CRDis.ι) T).val with hrkd
  have hrk : Function.Injective rk := by
    intro a b hab
    exact (Fintype.equivFin _).injective (Fin.ext hab)
  have h0 := h CRDis.P 2 CRDis.hasComp rk hrk
  have h1 := CRDis.single_ge rk
  have h2 := CRDis.brev_le
  have h3 := CRDis.srev_le
  have hn : (CRDis.n : ℝ) = 80 := by rw [CRDis.n_def]; norm_num
  push_cast at h0
  nlinarith
