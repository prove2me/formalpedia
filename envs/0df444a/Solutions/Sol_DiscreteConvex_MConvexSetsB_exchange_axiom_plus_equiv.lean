-- Prove2me | solution 1 for DiscreteConvex.MConvexSetsB.exchange_axiom_plus_equiv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T02:04:16.119395+00:00
-- url     : https://prove2.me/submissions/c56d6a23-9105-42da-a15e-3d1ded4ff113

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomBPlus



namespace DiscreteConvex.MConvexSetsB

section ExchCore

variable {V : Type*} [Fintype V] [DecidableEq V]

def Dst (a b : V → ℤ) : ℤ := ∑ w, |a w - b w|

lemma Dst_nonneg (a b : V → ℤ) : 0 ≤ Dst a b :=
  Finset.sum_nonneg (fun w _ => abs_nonneg _)

lemma Dst_zero {a b : V → ℤ} (h : Dst a b = 0) : a = b := by
  funext w
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => abs_nonneg (a w - b w))).mp h w
    (Finset.mem_univ w)
  have := abs_eq_zero.mp this
  linarith

lemma sum_cv (p : V) : ∑ w, CharVec p w = 1 := by
  simp [CharVec]

lemma cv_nonneg (p w : V) : 0 ≤ CharVec p w := by
  unfold CharVec; split_ifs <;> norm_num

lemma Dst_move (a b : V → ℤ) (p q : V) (hp : b p < a p) (hq : a q < b q) :
    Dst (fun w => a w - CharVec p w + CharVec q w) b = Dst a b - 2 := by
  have hpq : p ≠ q := by intro h; subst h; omega
  unfold Dst
  have h : ∀ w, |a w - CharVec p w + CharVec q w - b w| =
      |a w - b w| - (CharVec p w + CharVec q w) := by
    intro w
    by_cases hwp : w = p
    · subst hwp; simp only [CharVec, if_pos rfl, if_neg hpq]
      rw [abs_of_nonneg (by omega), abs_of_pos (by omega)]; ring
    by_cases hwq : w = q
    · subst hwq; simp only [CharVec, if_pos rfl, if_neg (Ne.symm hpq)]
      rw [abs_of_nonpos (by omega), abs_of_neg (by omega)]; ring
    simp only [CharVec, if_neg hwp, if_neg hwq]; ring_nf
  simp only [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_cv]
  ring

theorem exch_key (B : Set (V → ℤ)) (hP : ExchangeAxiomBPlus B) :
    ∀ n : ℕ, ∀ x y : V → ℤ, Dst x y = n → x ∈ B → y ∈ B → ∀ u ∈ SuppPos x y,
      ∃ v ∈ SuppNeg x y, (fun w => x w - CharVec u w + CharVec v w) ∈ B ∧
        (fun w => y w + CharVec u w - CharVec v w) ∈ B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x y hD hx hy u hu
  have hu' : y u < x u := hu
  obtain ⟨v, hv, hC⟩ := hP x hx y hy u hu
  have hv' : x v < y v := hv
  obtain ⟨u1, hu1, hx1⟩ := hP y hy x hx v (show x v < y v from hv')
  have hu1' : x u1 > y u1 := hu1
  by_cases hu1u : u1 = u
  · subst hu1u
    refine ⟨v, hv, ?_, hC⟩
    convert hx1 using 1; funext w; ring
  set x1 : V → ℤ := fun w => x w - CharVec u1 w + CharVec v w with hx1def
  have hx1B : x1 ∈ B := by convert hx1 using 1; funext w; simp only [hx1def]; ring
  have hD1 : Dst x1 y = Dst x y - 2 := Dst_move x y u1 v hu1' hv'
  have huv : u ≠ v := by intro h; subst h; omega
  have huv1 : u ≠ u1 := Ne.symm hu1u
  have hux1 : y u < x1 u := by
    show y u < x u - CharVec u1 u + CharVec v u
    simp only [CharVec, if_neg huv1, if_neg huv]; omega
  have hn2 : 2 ≤ n := by have := Dst_nonneg x1 y; omega
  obtain ⟨v2, hv2, hz, hC2⟩ := ih (n-2) (by omega) x1 y (by rw [hD1, hD]; push_cast [Nat.cast_sub hn2]; ring)
    hx1B hy u hux1
  have hv2' : x1 v2 < y v2 := hv2
  have hv2x : x v2 < y v2 := by
    change x v2 - CharVec u1 v2 + CharVec v v2 < y v2 at hv2'
    simp only [CharVec] at hv2'
    split_ifs at hv2' with h1 h2 <;> first | omega | (subst h1; omega)
  set z : V → ℤ := fun w => x1 w - CharVec u w + CharVec v2 w with hzdef
  have hzu : z u < x u := by
    have : u ≠ v2 := by intro h; rw [h] at hu'; omega
    show x u - CharVec u1 u + CharVec v u - CharVec u u + CharVec v2 u < x u
    simp [CharVec, huv1, huv, this]
  -- z expressed via x
  have hzx : ∀ w, z w = x w - CharVec u1 w + CharVec v w - CharVec u w + CharVec v2 w := by
    intro w; rfl
  by_cases hn5 : 5 ≤ n
  · have hDxz : Dst x z ≤ 4 := by
      unfold Dst
      calc ∑ w, |x w - z w| ≤ ∑ w, (CharVec u1 w + CharVec v w + CharVec u w + CharVec v2 w) := by
            apply Finset.sum_le_sum; intro w _
            rw [hzx]
            have := cv_nonneg u1 w; have := cv_nonneg v w; have := cv_nonneg u w
            have := cv_nonneg v2 w
            rw [abs_le]; constructor <;> linarith
        _ = 4 := by simp only [Finset.sum_add_distrib, sum_cv]; norm_num
    have hDn := Dst_nonneg x z
    obtain ⟨v3, hv3, hA3, _⟩ := ih (Dst x z).toNat (by omega) x z (by omega) hx hz u hzu
    have hv3' : x v3 < z v3 := hv3
    rw [hzx] at hv3'
    by_cases h3 : v3 = v
    · subst h3; exact ⟨v3, hv, hA3, hC⟩
    by_cases h3' : v3 = v2
    · subst h3'; exact ⟨v3, hv2x, hA3, hC2⟩
    exfalso
    have := cv_nonneg u1 v3; have := cv_nonneg u v3
    simp only [CharVec, if_neg h3, if_neg h3'] at hv3'
    simp only [CharVec] at this
    split_ifs at hv3' <;> omega
  · -- n = 4 and z = y
    have hDz : Dst z y = Dst x1 y - 2 := Dst_move x1 y u v2 hux1 hv2'
    have hDz0 : Dst z y = 0 := by have := Dst_nonneg z y; omega
    have hzy : z = y := Dst_zero hDz0
    have hyx : ∀ w, y w = x w - CharVec u1 w + CharVec v w - CharVec u w + CharVec v2 w := by
      intro w; rw [← hzx, hzy]
    obtain ⟨w0, hw0, hw0B⟩ := hP x hx y hy u1 hu1
    have hw0' : x w0 < y w0 := hw0
    by_cases h3 : w0 = v
    · subst h3
      refine ⟨v2, hv2x, ?_, hC2⟩
      convert hw0B using 1; funext w; rw [hyx w]; ring
    by_cases h3' : w0 = v2
    · subst h3'
      refine ⟨v, hv, ?_, hC⟩
      convert hw0B using 1; funext w; rw [hyx w]; ring
    exfalso
    rw [hyx] at hw0'
    have := cv_nonneg u1 w0; have := cv_nonneg u w0
    simp only [CharVec, if_neg h3, if_neg h3'] at hw0'
    simp only [CharVec] at this
    split_ifs at hw0' <;> omega

theorem exch_core (B : Set (V → ℤ)) : ExchangeAxiomB B ↔ ExchangeAxiomBPlus B := by
  constructor
  · intro h x hx y hy u hu
    obtain ⟨v, hv, _, h2⟩ := h x hx y hy u hu
    exact ⟨v, hv, h2⟩
  · intro hP x hx y hy u hu
    have := Dst_nonneg x y
    exact exch_key B hP (Dst x y).toNat x y (by omega) hx hy u hu

end ExchCore

end DiscreteConvex.MConvexSetsB

open DiscreteConvex.MConvexSetsB


theorem solution {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ)) :
    ExchangeAxiomB B ↔ ExchangeAxiomBPlus B := by
  exact exch_core B
