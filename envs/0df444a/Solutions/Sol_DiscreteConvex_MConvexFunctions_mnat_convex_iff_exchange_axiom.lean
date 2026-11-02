-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctions.mnat_convex_iff_exchange_axiom
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T01:01:01.794966+00:00
-- url     : https://prove2.me/submissions/ce1a4ebc-9257-47c7-9f85-ae93fd0af400

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctions_MNatExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ

open Classical
open DiscreteConvex.MConvexFunctions

private lemma coe_untopD_of_ne_top {a : WithTop ℝ} (ha : a ≠ ⊤) :
    ((a.untopD 0 : ℝ) : WithTop ℝ) = a := by
  cases a with
  | top => exact absurd rfl ha
  | coe r => rfl

private lemma ne_top_of_add_le {a b c d : WithTop ℝ} (h : a + b ≤ c + d)
    (hc : c ≠ ⊤) (hd : d ≠ ⊤) : a ≠ ⊤ ∧ b ≠ ⊤ := by
  have hcd : c + d ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hc, hd⟩
  have hab : a + b ≠ ⊤ := ne_top_of_le_ne_top hcd h
  exact WithTop.add_ne_top.mp hab

private lemma cancel_middle_le {a b c d e g : WithTop ℝ}
    (h1 : a + b ≤ c + d) (h2 : c + e ≤ a + g)
    (hc : c ≠ ⊤) (hd : d ≠ ⊤) (hg : g ≠ ⊤) :
    e + b ≤ g + d := by
  obtain ⟨ha, hb⟩ := ne_top_of_add_le h1 hc hd
  obtain ⟨_, he⟩ := ne_top_of_add_le h2 ha hg
  rw [← coe_untopD_of_ne_top ha, ← coe_untopD_of_ne_top hb,
      ← coe_untopD_of_ne_top hc, ← coe_untopD_of_ne_top hd] at h1
  rw [← coe_untopD_of_ne_top hc, ← coe_untopD_of_ne_top he,
      ← coe_untopD_of_ne_top ha, ← coe_untopD_of_ne_top hg] at h2
  rw [← coe_untopD_of_ne_top he, ← coe_untopD_of_ne_top hb,
      ← coe_untopD_of_ne_top hg, ← coe_untopD_of_ne_top hd]
  norm_cast at h1 h2 ⊢
  linarith

private lemma cancel_three_le {a b c d e k m : WithTop ℝ}
    (h1 : a + b ≤ c + d) (h2 : e + k ≤ c + b) (h3 : m + c ≤ e + a)
    (hc : c ≠ ⊤) (hd : d ≠ ⊤) :
    m + k ≤ c + d := by
  obtain ⟨ha, hb⟩ := ne_top_of_add_le h1 hc hd
  obtain ⟨he, hk⟩ := ne_top_of_add_le h2 hc hb
  obtain ⟨hm, _⟩ := ne_top_of_add_le h3 he ha
  rw [← coe_untopD_of_ne_top ha, ← coe_untopD_of_ne_top hb,
      ← coe_untopD_of_ne_top hc, ← coe_untopD_of_ne_top hd] at h1
  rw [← coe_untopD_of_ne_top he, ← coe_untopD_of_ne_top hk,
      ← coe_untopD_of_ne_top hc, ← coe_untopD_of_ne_top hb] at h2
  rw [← coe_untopD_of_ne_top hm, ← coe_untopD_of_ne_top hc,
      ← coe_untopD_of_ne_top he, ← coe_untopD_of_ne_top ha] at h3
  rw [← coe_untopD_of_ne_top hm, ← coe_untopD_of_ne_top hk,
      ← coe_untopD_of_ne_top hc, ← coe_untopD_of_ne_top hd]
  norm_cast at h1 h2 h3 ⊢
  linarith

private lemma mnat_exc_cases {V : Type*} [Fintype V] [DecidableEq V]
    {f : (V → ℤ) → WithTop ℝ} (hExc : MNatExchangeAxiom f)
    {x y : V → ℤ} (hx : x ∈ DomZ f) (hy : y ∈ DomZ f)
    {u : V} (hu : u ∈ SuppPos x y) :
    f (fun w => x w - CharVec u w) + f (fun w => y w + CharVec u w) ≤ f x + f y ∨
    ∃ v ∈ SuppNeg x y,
      f (fun w => x w - CharVec u w + CharVec v w) +
        f (fun w => y w + CharVec u w - CharVec v w) ≤ f x + f y := by
  have h := hExc x hx y hy u hu
  rcases le_total
    (f (fun w => x w - CharVec u w) + f (fun w => y w + CharVec u w))
    ((SuppNeg x y).inf (fun v =>
      f (fun w => x w - CharVec u w + CharVec v w) +
        f (fun w => y w + CharVec u w - CharVec v w))) with hle | hle
  · left
    rwa [min_eq_left hle] at h
  · right
    rw [min_eq_right hle] at h
    by_cases hne : (SuppNeg x y).Nonempty
    · obtain ⟨v, hv, hmin⟩ := Finset.exists_mem_eq_inf (SuppNeg x y) hne (fun v =>
        f (fun w => x w - CharVec u w + CharVec v w) +
          f (fun w => y w + CharVec u w - CharVec v w))
      rw [hmin] at h
      exact ⟨v, hv, h⟩
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.inf_empty] at h
      have hxy : f x + f y ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hx, hy⟩
      exact absurd (top_le_iff.mp h) hxy

private def posDist {V : Type*} [Fintype V] (x y : V → ℤ) : ℕ :=
  ∑ w : V, (x w - y w).toNat

private lemma posDist_sub_lt {V : Type*} [Fintype V] [DecidableEq V]
    {x y : V → ℤ} {u : V} (hu : u ∈ SuppPos x y) :
    posDist (fun w => x w - CharVec u w) y < posDist x y := by
  simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  apply Finset.sum_lt_sum
  · intro w _
    by_cases hwu : w = u
    · subst hwu
      simp only [CharVec, ↓reduceIte]
      omega
    · simp only [CharVec, hwu, ↓reduceIte, sub_zero, le_refl]
  · refine ⟨u, Finset.mem_univ u, ?_⟩
    simp only [CharVec, ↓reduceIte]
    omega

private lemma posDist_sub_add_lt {V : Type*} [Fintype V] [DecidableEq V]
    {x y : V → ℤ} {u v : V} (hu : u ∈ SuppPos x y) (hv : v ∈ SuppNeg x y) :
    posDist (fun w => x w - CharVec u w + CharVec v w) y < posDist x y := by
  simp only [SuppPos, SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
  have huv : v ≠ u := by
    intro h
    subst h
    omega
  apply Finset.sum_lt_sum
  · intro w _
    by_cases hwu : w = u
    · subst hwu
      simp only [CharVec, ↓reduceIte, huv.symm, add_zero]
      omega
    · by_cases hwv : w = v
      · subst hwv
        simp only [CharVec, hwu, ↓reduceIte, sub_zero]
        omega
      · simp only [CharVec, hwu, hwv, ↓reduceIte, sub_zero, add_zero, le_refl]
  · refine ⟨u, Finset.mem_univ u, ?_⟩
    simp only [CharVec, ↓reduceIte, huv.symm, add_zero]
    omega

private lemma sum_charVec {V : Type*} [Fintype V] [DecidableEq V] (u : V) :
    ∑ w : V, CharVec u w = 1 := by
  simp [CharVec]

private lemma exists_suppNeg_of_sum_lt {V : Type*} [Fintype V] [DecidableEq V]
    {x y : V → ℤ} (hsum : ∑ w : V, x w < ∑ w : V, y w) :
    ∃ v : V, v ∈ SuppNeg x y := by
  by_contra! h
  have hle : ∑ w : V, y w ≤ ∑ w : V, x w := by
    apply Finset.sum_le_sum
    intro w _
    have hw := h w
    simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hw
    exact hw
  omega

private lemma sum_gt_exchange_aux {V : Type*} [Fintype V] [DecidableEq V]
    {f : (V → ℤ) → WithTop ℝ} (hExc : MNatExchangeAxiom f) :
    ∀ (n : ℕ) (x y : V → ℤ), posDist x y = n → x ∈ DomZ f → y ∈ DomZ f →
      ∑ w : V, x w < ∑ w : V, y w →
      ∃ v ∈ SuppNeg x y,
        f (fun w => x w + CharVec v w) + f (fun w => y w - CharVec v w) ≤ f x + f y := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro x y hn hx hy hsum
  by_cases hpos : (SuppPos x y).Nonempty
  · obtain ⟨u₀, hu₀⟩ := hpos
    have hu₀_lt : y u₀ < x u₀ := by
      simpa [SuppPos] using hu₀
    let S : Finset V := (SuppNeg x y).filter (fun v =>
      (fun w => x w - CharVec u₀ w + CharVec v w) ∈ DomZ f)
    have hS_ne : S.Nonempty := by
      rcases mnat_exc_cases hExc hx hy hu₀ with hbr1 | ⟨v, hv, hbr2⟩
      · obtain ⟨hx', _⟩ := ne_top_of_add_le hbr1 hx hy
        have hlt' : posDist (fun w => x w - CharVec u₀ w) y < n := by
          rw [← hn]
          exact posDist_sub_lt hu₀
        have hsum' : ∑ w : V, (x w - CharVec u₀ w) < ∑ w : V, y w := by
          rw [Finset.sum_sub_distrib, sum_charVec]
          omega
        obtain ⟨v, hv_neg, hv_le⟩ :=
          ih _ hlt' (fun w => x w - CharVec u₀ w) y rfl hx' hy hsum'
        obtain ⟨hx'v, _⟩ := ne_top_of_add_le hv_le hx' hy
        have hv_ne_u₀ : v ≠ u₀ := by
          simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv_neg
          intro hvu
          subst hvu
          simp only [CharVec, ↓reduceIte] at hv_neg
          omega
        have hv_supp : v ∈ SuppNeg x y := by
          simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv_neg ⊢
          simp only [CharVec, hv_ne_u₀, ↓reduceIte, sub_zero] at hv_neg
          exact hv_neg
        exact ⟨v, Finset.mem_filter.mpr ⟨hv_supp, hx'v⟩⟩
      · obtain ⟨hxv, _⟩ := ne_top_of_add_le hbr2 hx hy
        exact ⟨v, Finset.mem_filter.mpr ⟨hv, hxv⟩⟩
    let score : V → WithTop ℝ := fun v =>
      f (fun w => x w + CharVec v w) +
        ((-((f (fun w => x w - CharVec u₀ w + CharVec v w)).untopD 0) : ℝ) : WithTop ℝ)
    obtain ⟨v₁, hv₁S, hv₁_max⟩ := Finset.exists_max_image S score hS_ne
    have hv₁_neg : v₁ ∈ SuppNeg x y := (Finset.mem_filter.mp hv₁S).1
    have hx1 : (fun w => x w - CharVec u₀ w + CharVec v₁ w) ∈ DomZ f :=
      (Finset.mem_filter.mp hv₁S).2
    let x1 : V → ℤ := fun w => x w - CharVec u₀ w + CharVec v₁ w
    have hlt1 : posDist x1 y < n := by
      rw [← hn]
      exact posDist_sub_add_lt hu₀ hv₁_neg
    have hsum1 : ∑ w : V, x1 w < ∑ w : V, y w := by
      have : ∑ w : V, x1 w = ∑ w : V, x w := by
        simp only [x1, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_charVec]
        omega
      omega
    obtain ⟨v₂, hv₂_neg1, hIH⟩ := ih _ hlt1 x1 y rfl hx1 hy hsum1
    have hv₁_lt : x v₁ < y v₁ := by simpa [SuppNeg] using hv₁_neg
    have hv₁_ne : u₀ ≠ v₁ := by
      intro h
      subst h
      omega
    have hv₂_ne_u₀ : v₂ ≠ u₀ := by
      simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv₂_neg1
      intro hvu
      subst hvu
      simp only [x1, CharVec, ↓reduceIte, hv₁_ne, add_zero] at hv₂_neg1
      omega
    have hv₂_neg : v₂ ∈ SuppNeg x y := by
      simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv₂_neg1 ⊢
      by_cases hv₂v₁ : v₂ = v₁
      · subst hv₂v₁
        exact hv₁_lt
      · simp only [x1, CharVec, hv₂_ne_u₀, hv₂v₁, ↓reduceIte, sub_zero, add_zero] at hv₂_neg1
        exact hv₂_neg1
    let a : V → ℤ := fun w => x1 w + CharVec v₂ w
    obtain ⟨ha, hy_v₂⟩ := ne_top_of_add_le hIH hx1 hy
    have hv₂_pos_a : v₂ ∈ SuppPos a x := by
      simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and, a, x1]
      by_cases hv₂v₁ : v₂ = v₁
      · subst hv₂v₁
        simp only [CharVec, hv₂_ne_u₀, ↓reduceIte]
        omega
      · simp only [CharVec, hv₂_ne_u₀, hv₂v₁, ↓reduceIte]
        omega
    have hstep : f x1 + f (fun w => x w + CharVec v₂ w) ≤ f a + f x := by
      rcases mnat_exc_cases hExc ha hx hv₂_pos_a with hbr1 | ⟨u, hu_neg, hbr2⟩
      · have heq1 : (fun w => a w - CharVec v₂ w) = x1 := by
          ext w; simp [a]
        rw [heq1] at hbr1
        exact hbr1
      · have hu_eq : u = u₀ := by
          simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and, x1] at hu_neg
          by_contra! hu_ne
          have : 0 ≤ -(CharVec u₀ u) + CharVec v₁ u + CharVec v₂ u := by
            have h1 : CharVec u₀ u = 0 := by simp [CharVec, hu_ne]
            have h2 : 0 ≤ CharVec v₁ u := by simp [CharVec]; split_ifs <;> omega
            have h3 : 0 ≤ CharVec v₂ u := by simp [CharVec]; split_ifs <;> omega
            omega
          omega
        subst u
        have heq_a : (fun w => a w - CharVec v₂ w + CharVec u₀ w) =
            (fun w => x w + CharVec v₁ w) := by
          ext w; simp [a, x1]; ring
        have heq_b : (fun w => x w + CharVec v₂ w - CharVec u₀ w) =
            (fun w => x w - CharVec u₀ w + CharVec v₂ w) := by
          ext w; ring
        rw [heq_a, heq_b] at hbr2
        obtain ⟨hxv₁, hx2⟩ := ne_top_of_add_le hbr2 ha hx
        have hv₂S : v₂ ∈ S := Finset.mem_filter.mpr ⟨hv₂_neg, hx2⟩
        have hsc : score v₂ ≤ score v₁ := hv₁_max v₂ hv₂S
        have hxv₂ : f (fun w => x w + CharVec v₂ w) ≠ ⊤ := by
          intro htop
          have hsc2 : score v₂ = ⊤ := by simp [score, htop]
          rw [hsc2, top_le_iff] at hsc
          have hsc1 : score v₁ ≠ ⊤ :=
            WithTop.add_ne_top.mpr ⟨hxv₁, WithTop.coe_ne_top⟩
          exact hsc1 hsc
        have hscore_le :
            f x1 + f (fun w => x w + CharVec v₂ w) ≤
              f (fun w => x w + CharVec v₁ w) +
                f (fun w => x w - CharVec u₀ w + CharVec v₂ w) := by
          dsimp only [score] at hsc
          rw [← coe_untopD_of_ne_top hxv₂, ← coe_untopD_of_ne_top hxv₁] at hsc
          rw [← coe_untopD_of_ne_top hx1, ← coe_untopD_of_ne_top hxv₂,
              ← coe_untopD_of_ne_top hxv₁, ← coe_untopD_of_ne_top hx2]
          norm_cast at hsc ⊢
          linarith
        exact le_trans hscore_le hbr2
    exact ⟨v₂, hv₂_neg, cancel_middle_le hIH hstep hx1 hy hx⟩
  · have hpos_empty : SuppPos x y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpos
    obtain ⟨v, hv⟩ := exists_suppNeg_of_sum_lt hsum
    have hv_pos : v ∈ SuppPos y x := by
      simpa [SuppPos, SuppNeg] using hv
    have hneg_yx : SuppNeg y x = ∅ := by
      simpa [SuppPos, SuppNeg] using hpos_empty
    rcases mnat_exc_cases hExc hy hx hv_pos with hbr1 | ⟨u, hu, _⟩
    · refine ⟨v, hv, ?_⟩
      simpa [add_comm] using hbr1
    · rw [hneg_yx] at hu
      exact absurd hu (Finset.notMem_empty u)

private lemma sum_gt_exchange {V : Type*} [Fintype V] [DecidableEq V]
    {f : (V → ℤ) → WithTop ℝ} (hExc : MNatExchangeAxiom f)
    {x y : V → ℤ} (hx : x ∈ DomZ f) (hy : y ∈ DomZ f)
    (hsum : ∑ w : V, x w < ∑ w : V, y w) :
    ∃ v ∈ SuppNeg x y,
      f (fun w => x w + CharVec v w) + f (fun w => y w - CharVec v w) ≤ f x + f y :=
  sum_gt_exchange_aux hExc (posDist x y) x y rfl hx hy hsum

private def liftVec {V : Type*} [Fintype V] (x : V → ℤ) : Option V → ℤ
  | none => -(∑ v : V, x v)
  | some v => x v

@[simp] private lemma liftVec_none {V : Type*} [Fintype V] (x : V → ℤ) :
    liftVec x none = -(∑ v : V, x v) := rfl

@[simp] private lemma liftVec_some {V : Type*} [Fintype V] (x : V → ℤ) (v : V) :
    liftVec x (some v) = x v := rfl

private lemma liftedFunction_liftVec {V : Type*} [Fintype V]
    (f : (V → ℤ) → WithTop ℝ) (x : V → ℤ) :
    LiftedFunction f (liftVec x) = f x := by
  simp [LiftedFunction]

private lemma eq_liftVec_of_mem_domZ {V : Type*} [Fintype V]
    {f : (V → ℤ) → WithTop ℝ} {x : Option V → ℤ}
    (hx : x ∈ DomZ (LiftedFunction f)) :
    x = liftVec (fun v => x (some v)) ∧ (fun v => x (some v)) ∈ DomZ f := by
  simp only [DomZ, Set.mem_setOf_eq, LiftedFunction] at hx
  split_ifs at hx with hsum
  · refine ⟨?_, hx⟩
    ext w
    cases w with
    | none => exact hsum
    | some v => rfl
  · exact absurd rfl hx

private lemma charVec_some_none {V : Type*} [DecidableEq V] (u : V) :
    CharVec (some u) (none : Option V) = 0 := rfl

private lemma charVec_none_none {V : Type*} [DecidableEq V] :
    CharVec (none : Option V) (none : Option V) = 1 := rfl

private lemma charVec_none_some {V : Type*} [DecidableEq V] (v : V) :
    CharVec (none : Option V) (some v) = 0 := rfl

private lemma charVec_some_some {V : Type*} [DecidableEq V] (u v : V) :
    CharVec (some u) (some v) = CharVec u v := by
  simp [CharVec]

private lemma liftVec_sub_some_add_none {V : Type*} [Fintype V] [DecidableEq V]
    (x : V → ℤ) (u : V) :
    (fun w => liftVec x w - CharVec (some u) w + CharVec none w) =
      liftVec (fun v => x v - CharVec u v) := by
  ext w
  cases w with
  | none =>
    simp only [liftVec_none, charVec_some_none, charVec_none_none,
      Finset.sum_sub_distrib, sum_charVec]
    omega
  | some v =>
    simp [charVec_some_some, charVec_none_some]

private lemma liftVec_add_some_sub_none {V : Type*} [Fintype V] [DecidableEq V]
    (y : V → ℤ) (u : V) :
    (fun w => liftVec y w + CharVec (some u) w - CharVec none w) =
      liftVec (fun v => y v + CharVec u v) := by
  ext w
  cases w with
  | none =>
    simp only [liftVec_none, charVec_some_none, charVec_none_none,
      Finset.sum_add_distrib, sum_charVec]
    omega
  | some v =>
    simp [charVec_some_some, charVec_none_some]

private lemma liftVec_sub_none_add_some {V : Type*} [Fintype V] [DecidableEq V]
    (x : V → ℤ) (v : V) :
    (fun w => liftVec x w - CharVec none w + CharVec (some v) w) =
      liftVec (fun w => x w + CharVec v w) := by
  ext w
  cases w with
  | none =>
    simp only [liftVec_none, charVec_some_none, charVec_none_none,
      Finset.sum_add_distrib, sum_charVec]
    omega
  | some u =>
    simp [charVec_some_some, charVec_none_some]

private lemma liftVec_add_none_sub_some {V : Type*} [Fintype V] [DecidableEq V]
    (y : V → ℤ) (v : V) :
    (fun w => liftVec y w + CharVec none w - CharVec (some v) w) =
      liftVec (fun w => y w - CharVec v w) := by
  ext w
  cases w with
  | none =>
    simp only [liftVec_none, charVec_some_none, charVec_none_none,
      Finset.sum_sub_distrib, sum_charVec]
    omega
  | some u =>
    simp [charVec_some_some, charVec_none_some]

private lemma liftVec_sub_some_add_some {V : Type*} [Fintype V] [DecidableEq V]
    (x : V → ℤ) (u v : V) :
    (fun w => liftVec x w - CharVec (some u) w + CharVec (some v) w) =
      liftVec (fun w => x w - CharVec u w + CharVec v w) := by
  ext w
  cases w with
  | none =>
    simp only [liftVec_none, charVec_some_none,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_charVec]
    omega
  | some w =>
    simp [charVec_some_some]

private lemma liftVec_add_some_sub_some {V : Type*} [Fintype V] [DecidableEq V]
    (y : V → ℤ) (u v : V) :
    (fun w => liftVec y w + CharVec (some u) w - CharVec (some v) w) =
      liftVec (fun w => y w + CharVec u w - CharVec v w) := by
  ext w
  cases w with
  | none =>
    simp only [liftVec_none, charVec_some_none,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_charVec]
    omega
  | some w =>
    simp [charVec_some_some]

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : (DomZ f).Nonempty) :
    MNaturalConvex f ↔ MNatExchangeAxiom f := by
  let _ := hf
  constructor
  · intro hM x hx y hy u hu
    have hxL : liftVec x ∈ DomZ (LiftedFunction f) := by
      simpa [DomZ, liftedFunction_liftVec] using hx
    have hyL : liftVec y ∈ DomZ (LiftedFunction f) := by
      simpa [DomZ, liftedFunction_liftVec] using hy
    have huL : some u ∈ SuppPos (liftVec x) (liftVec y) := by
      simpa [SuppPos] using hu
    obtain ⟨vt, hvt, hle⟩ := hM (liftVec x) hxL (liftVec y) hyL (some u) huL
    rw [liftedFunction_liftVec, liftedFunction_liftVec] at hle
    cases vt with
    | none =>
      rw [liftVec_sub_some_add_none, liftVec_add_some_sub_none,
          liftedFunction_liftVec, liftedFunction_liftVec] at hle
      exact le_trans (min_le_left _ _) hle
    | some v =>
      have hv : v ∈ SuppNeg x y := by
        simpa [SuppNeg] using hvt
      rw [liftVec_sub_some_add_some, liftVec_add_some_sub_some,
          liftedFunction_liftVec, liftedFunction_liftVec] at hle
      have hinf : (SuppNeg x y).inf (fun v =>
          f (fun w => x w - CharVec u w + CharVec v w) +
            f (fun w => y w + CharVec u w - CharVec v w)) ≤
          f (fun w => x w - CharVec u w + CharVec v w) +
            f (fun w => y w + CharVec u w - CharVec v w) :=
        Finset.inf_le hv
      exact le_trans (le_trans (min_le_right _ _) hinf) hle
  · intro hExc xt hxt yt hyt ut hut
    let x : V → ℤ := fun v => xt (some v)
    let y : V → ℤ := fun v => yt (some v)
    have hxt_pair : xt = liftVec x ∧ x ∈ DomZ f := eq_liftVec_of_mem_domZ hxt
    have hyt_pair : yt = liftVec y ∧ y ∈ DomZ f := eq_liftVec_of_mem_domZ hyt
    obtain ⟨hxt_eq, hx⟩ := hxt_pair
    obtain ⟨hyt_eq, hy⟩ := hyt_pair
    rw [hxt_eq, hyt_eq] at hut ⊢
    cases ut with
    | none =>
      have hsum : ∑ v : V, x v < ∑ v : V, y v := by
        simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and, liftVec_none] at hut
        omega
      obtain ⟨v, hv, hle⟩ := sum_gt_exchange hExc hx hy hsum
      refine ⟨some v, ?_, ?_⟩
      · simpa [SuppNeg] using hv
      · rw [liftVec_sub_none_add_some, liftVec_add_none_sub_some,
            liftedFunction_liftVec, liftedFunction_liftVec,
            liftedFunction_liftVec, liftedFunction_liftVec]
        exact hle
    | some u =>
      have hu : u ∈ SuppPos x y := by
        simpa [SuppPos] using hut
      rcases mnat_exc_cases hExc hx hy hu with hbr1 | ⟨v, hv, hbr2⟩
      · by_cases hsum : ∑ v : V, y v < ∑ v : V, x v
        · refine ⟨none, ?_, ?_⟩
          · simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and, liftVec_none]
            omega
          · rw [liftVec_sub_some_add_none, liftVec_add_some_sub_none,
                liftedFunction_liftVec, liftedFunction_liftVec,
                liftedFunction_liftVec, liftedFunction_liftVec]
            exact hbr1
        · obtain ⟨hx', hy'⟩ := ne_top_of_add_le hbr1 hx hy
          have hsum' : ∑ v : V, x v < ∑ v : V, (y v + CharVec u v) := by
            rw [Finset.sum_add_distrib, sum_charVec]
            omega
          obtain ⟨v, hv_neg', hle2⟩ := sum_gt_exchange hExc hx hy' hsum'
          have hu_lt : y u < x u := by simpa [SuppPos] using hu
          have hv_ne_u : v ≠ u := by
            simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv_neg'
            intro hvu
            subst hvu
            simp only [CharVec, ↓reduceIte] at hv_neg'
            omega
          have hv : v ∈ SuppNeg x y := by
            simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv_neg' ⊢
            simp only [CharVec, hv_ne_u, ↓reduceIte, add_zero] at hv_neg'
            exact hv_neg'
          obtain ⟨hxv, _⟩ := ne_top_of_add_le hle2 hx hy'
          have hu_pos_pq : u ∈ SuppPos (fun w => x w + CharVec v w) (fun w => x w - CharVec u w) := by
            rw [SuppPos, Finset.mem_filter]
            refine ⟨Finset.mem_univ u, ?_⟩
            simp only [CharVec, ↓reduceIte, hv_ne_u.symm]
            omega
          have hneg_pq : SuppNeg (fun w => x w + CharVec v w) (fun w => x w - CharVec u w) = ∅ := by
            ext w
            simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.notMem_empty, iff_false, not_lt]
            have h1 : 0 ≤ CharVec v w := by simp [CharVec]; split_ifs <;> omega
            have h2 : 0 ≤ CharVec u w := by simp [CharVec]; split_ifs <;> omega
            omega
          have hle3 : f (fun w => x w - CharVec u w + CharVec v w) + f x ≤
              f (fun w => x w + CharVec v w) + f (fun w => x w - CharVec u w) := by
            rcases mnat_exc_cases hExc hxv hx' hu_pos_pq with hbr_pq | ⟨w, hw, _⟩
            · have heq1 : (fun w => x w + CharVec v w - CharVec u w) =
                  (fun w => x w - CharVec u w + CharVec v w) := by
                ext w; ring
              have heq2 : (fun w => x w - CharVec u w + CharVec u w) = x := by
                ext w; simp
              rw [heq1, heq2] at hbr_pq
              exact hbr_pq
            · rw [hneg_pq] at hw
              exact absurd hw (Finset.notMem_empty w)
          have hcomb := cancel_three_le hbr1 hle2 hle3 hx hy
          refine ⟨some v, ?_, ?_⟩
          · simpa [SuppNeg] using hv
          · rw [liftVec_sub_some_add_some, liftVec_add_some_sub_some,
                liftedFunction_liftVec, liftedFunction_liftVec,
                liftedFunction_liftVec, liftedFunction_liftVec]
            exact hcomb
      · refine ⟨some v, ?_, ?_⟩
        · simpa [SuppNeg] using hv
        · rw [liftVec_sub_some_add_some, liftVec_add_some_sub_some,
              liftedFunction_liftVec, liftedFunction_liftVec,
              liftedFunction_liftVec, liftedFunction_liftVec]
          exact hbr2
