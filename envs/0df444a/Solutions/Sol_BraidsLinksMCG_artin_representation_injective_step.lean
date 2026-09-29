-- Prove2me | solution 1 for BraidsLinksMCG.artin_representation_injective_step
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T11:11:48.279346+00:00
-- url     : https://prove2.me/submissions/3a068d08-4ec6-4732-80f7-b8fba5754193

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BraidsLinksMCG
namespace StepM

def s (n i : ℕ) : ArtinBraidGroup (n+1) := if h : i < n then sigma ⟨i, by omega⟩ else 1
def X (n j : ℕ) : FreeGroup (Fin (n+1)) := if h : j < n+1 then FreeGroup.of ⟨j, h⟩ else 1

theorem s_comm (n i j : ℕ) (h : i + 2 ≤ j ∨ j + 2 ≤ i) : s n i * s n j = s n j * s n i := by
  unfold s
  split_ifs with hi hj
  · have hr : (FreeGroup.of (⟨i, by omega⟩ : Fin (n+1-1)) * FreeGroup.of ⟨j, by omega⟩ *
        (FreeGroup.of (⟨i, by omega⟩ : Fin (n+1-1)))⁻¹ * (FreeGroup.of ⟨j, by omega⟩)⁻¹)
        ∈ braidRels (n+1) := Or.inl ⟨_, _, by simp only; omega, rfl⟩
    have h1 := PresentedGroup.one_of_mem (rels := braidRels (n+1)) hr
    simp only [map_mul, map_inv] at h1
    have h2 : (sigma (⟨i, by omega⟩ : Fin (n+1-1)) : ArtinBraidGroup (n+1)) * sigma ⟨j, by omega⟩ *
      (sigma ⟨i, by omega⟩)⁻¹ * (sigma ⟨j, by omega⟩)⁻¹ = 1 := h1
    calc (sigma (⟨i, by omega⟩ : Fin (n+1-1)) : ArtinBraidGroup (n+1)) * sigma ⟨j, by omega⟩
        = (sigma ⟨i, by omega⟩ * sigma ⟨j, by omega⟩ * (sigma ⟨i, by omega⟩)⁻¹ *
            (sigma ⟨j, by omega⟩)⁻¹) * (sigma ⟨j, by omega⟩ * sigma ⟨i, by omega⟩) := by group
      _ = _ := by rw [h2, one_mul]
  all_goals simp

theorem s_braid (n i : ℕ) (h : i + 1 < n) :
    s n i * s n (i+1) * s n i = s n (i+1) * s n i * s n (i+1) := by
  unfold s
  rw [dif_pos (by omega), dif_pos h]
  have hr : (FreeGroup.of (⟨i, by omega⟩ : Fin (n+1-1)) * FreeGroup.of ⟨i+1, by omega⟩ *
      FreeGroup.of (⟨i, by omega⟩ : Fin (n+1-1)) *
      (FreeGroup.of ⟨i+1, by omega⟩ * FreeGroup.of ⟨i, by omega⟩ * FreeGroup.of ⟨i+1, by omega⟩)⁻¹)
      ∈ braidRels (n+1) := Or.inr ⟨_, _, rfl, rfl⟩
  have h1 := PresentedGroup.one_of_mem (rels := braidRels (n+1)) hr
  simp only [map_mul, map_inv] at h1
  have h2 : (sigma (⟨i, by omega⟩ : Fin (n+1-1)) : ArtinBraidGroup (n+1)) * sigma ⟨i+1, by omega⟩ *
      sigma ⟨i, by omega⟩ * (sigma ⟨i+1, by omega⟩ * sigma ⟨i, by omega⟩ * sigma ⟨i+1, by omega⟩)⁻¹ = 1 := h1
  calc (sigma (⟨i, by omega⟩ : Fin (n+1-1)) : ArtinBraidGroup (n+1)) * sigma ⟨i+1, by omega⟩ *
        sigma ⟨i, by omega⟩
      = (sigma ⟨i, by omega⟩ * sigma ⟨i+1, by omega⟩ * sigma ⟨i, by omega⟩ *
          (sigma ⟨i+1, by omega⟩ * sigma ⟨i, by omega⟩ * sigma ⟨i+1, by omega⟩)⁻¹) *
          (sigma ⟨i+1, by omega⟩ * sigma ⟨i, by omega⟩ * sigma ⟨i+1, by omega⟩) := by group
    _ = _ := by rw [h2, one_mul]

section XiLemmas
variable {n : ℕ} (ξ : ArtinBraidGroup (n+1) →* MulAut (FreeGroup (Fin (n+1))))
  (hξ : ∀ i : Fin (n + 1 - 1), ∀ w : FreeGroup (Fin (n + 1)), ξ (sigma i) w = artinEndo (n + 1) i w)
include hξ

theorem xi_s_gen (i j : ℕ) (hi : i < n) (hj : j < n + 1) :
    ξ (s n i) (X n j) = if j = i then X n i * X n (i+1) * (X n i)⁻¹
      else if j = i + 1 then X n i else X n j := by
  unfold s X
  rw [dif_pos hi, dif_pos hj, hξ, artinEndo, FreeGroup.lift_apply_of]
  simp only [strandIdx, strandIdxSucc, Fin.ext_iff]
  rw [dif_pos (by omega : i < n + 1), dif_pos (by omega : i + 1 < n + 1)]

theorem xi_s_self (i : ℕ) (hi : i < n) :
    ξ (s n i) (X n i) = X n i * X n (i+1) * (X n i)⁻¹ := by
  rw [xi_s_gen ξ hξ i i hi (by omega), if_pos rfl]

theorem xi_s_succ (i : ℕ) (hi : i < n) : ξ (s n i) (X n (i+1)) = X n i := by
  rw [xi_s_gen ξ hξ i (i+1) hi (by omega), if_neg (by omega), if_pos rfl]

theorem xi_s_other (i j : ℕ) (h1 : j ≠ i) (h2 : j ≠ i + 1) : ξ (s n i) (X n j) = X n j := by
  by_cases hi : i < n
  · by_cases hj : j < n + 1
    · rw [xi_s_gen ξ hξ i j hi hj, if_neg h1, if_neg h2]
    · unfold X; rw [dif_neg hj, map_one]
  · unfold s; rw [dif_neg hi, map_one]; rfl

end XiLemmas

open FreeGroup in
theorem centralizer_of {α : Type*} [DecidableEq α] (a : α) :
    ∀ (m : ℕ) (g : FreeGroup α), g.toWord.length ≤ m → g * of a = of a * g →
      g ∈ Subgroup.zpowers (of a) := by
  intro m
  induction m with
  | zero =>
    intro g hg _
    have : g.toWord = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [toWord_eq_nil_iff] at this; subst this; exact one_mem _
  | succ m ih =>
    intro g hg hc
    rcases hw : g.toWord with _ | ⟨x, t⟩
    · rw [toWord_eq_nil_iff] at hw; subst hw; exact one_mem _
    have hred : IsReduced (x :: t) := hw ▸ isReduced_toWord
    have hgm : g = mk [x] * mk t := by
      rw [mul_mk, ← mk_toWord (x := g), hw]; rfl
    by_cases hx : x.1 = a
    · obtain ⟨x1, x2⟩ := x
      simp only at hx; subst hx
      have hz : mk [(x1, x2)] ∈ Subgroup.zpowers (of x1) := by
        cases x2
        · have : mk [(x1, false)] = (of x1)⁻¹ := by rw [of, inv_mk]; rfl
          rw [this]; exact inv_mem (Subgroup.mem_zpowers _)
        · exact Subgroup.mem_zpowers _
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
      have ht : (mk t).toWord = t := by
        rw [toWord_mk]; exact (hred.infix (List.infix_cons (List.infix_refl t))).reduce_eq
      have hcomm : mk t * of x1 = of x1 * mk t := by
        have e : mk t = (of x1 ^ k)⁻¹ * g := by rw [hgm, hk]; group
        rw [e]
        calc (of x1 ^ k)⁻¹ * g * of x1 = (of x1 ^ k)⁻¹ * (g * of x1) := by group
          _ = (of x1 ^ k)⁻¹ * (of x1 * g) := by rw [hc]
          _ = of x1 * ((of x1 ^ k)⁻¹ * g) := by group
      have := ih (mk t) (by rw [ht]; rw [hw] at hg; simp at hg; omega) hcomm
      rw [hgm]; exact mul_mem hz this
    · exfalso
      have h1 : (of a * g).toWord = (a, true) :: x :: t := by
        rw [toWord_mul, toWord_of, hw]
        apply IsReduced.reduce_eq
        rw [List.singleton_append, isReduced_cons_cons]
        exact ⟨fun h => absurd h.symm hx, hred⟩
      have h2 := toWord_mul_sublist g (of a)
      rw [hc, h1, hw, toWord_of] at h2
      have h3 := h2.eq_of_length (by simp)
      simp at h3
      exact hx (congrArg Prod.fst h3.1).symm

/-! ## Products of generators -/

def R (n a : ℕ) : ℕ → ArtinBraidGroup (n+1)
  | 0 => 1
  | l+1 => s n (a+l) * R n a l

def R' (n a : ℕ) : ℕ → ArtinBraidGroup (n+1)
  | 0 => 1
  | l+1 => R' n a l * s n (a+l)

theorem R_succ' (n a l : ℕ) : R n a (l+1) = R n (a+1) l * s n a := by
  induction l generalizing a with
  | zero => simp [R]
  | succ l ih =>
    rw [R, ih, R, show a + (l+1) = a + 1 + l by omega]; group

theorem R'_succ' (n a l : ℕ) : R' n a (l+1) = s n a * R' n (a+1) l := by
  induction l generalizing a with
  | zero => simp [R']
  | succ l ih =>
    rw [R', ih, R', show a + (l+1) = a + 1 + l by omega]; group

theorem s_comm_R (n j a l : ℕ) (h : j + 2 ≤ a ∨ a + l + 1 ≤ j) :
    s n j * R n a l = R n a l * s n j := by
  induction l with
  | zero => simp [R]
  | succ l ih =>
    rw [R, ← mul_assoc, s_comm n j (a+l) (by omega), mul_assoc, ih (by omega), mul_assoc]

theorem s_comm_R' (n j a l : ℕ) (h : j + 2 ≤ a ∨ a + l + 1 ≤ j) :
    s n j * R' n a l = R' n a l * s n j := by
  induction l with
  | zero => simp [R']
  | succ l ih =>
    rw [R', ← mul_assoc, ih (by omega), mul_assoc, s_comm n j (a+l) (by omega), mul_assoc]

theorem R_shift (n a l i : ℕ) (h1 : a ≤ i) (h2 : i + 1 < a + l) (h3 : i + 1 < n) :
    R n a l * s n (i+1) = s n i * R n a l := by
  induction l with
  | zero => omega
  | succ l ih =>
    rw [R]
    by_cases hl : i + 1 < a + l
    · rw [mul_assoc, ih hl, ← mul_assoc, s_comm n (a+l) i (by omega), mul_assoc]
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      have hi : i = a + l' := by omega
      subst hi
      rw [R, show a + (l'+1) = a + l' + 1 by omega]
      have hc := s_comm_R n (a + l' + 1) a l' (Or.inr (by omega))
      calc s n (a + l' + 1) * (s n (a + l') * R n a l') * s n (a + l' + 1)
          = s n (a + l' + 1) * s n (a + l') * (R n a l' * s n (a + l' + 1)) := by group
        _ = s n (a + l' + 1) * s n (a + l') * s n (a + l' + 1) * R n a l' := by rw [← hc]; group
        _ = s n (a + l') * s n (a + l' + 1) * s n (a + l') * R n a l' := by
            rw [s_braid n (a + l') h3]
        _ = _ := by group

theorem R'_shift (n a l j : ℕ) (h1 : a ≤ j) (h2 : j + 1 < a + l) (h3 : j + 1 < n) :
    R' n a l * s n j = s n (j+1) * R' n a l := by
  induction l with
  | zero => omega
  | succ l ih =>
    rw [R']
    by_cases hl : j + 1 < a + l
    · rw [mul_assoc, ← s_comm n j (a+l) (by omega), ← mul_assoc, ih hl, mul_assoc]
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      have hi : j = a + l' := by omega
      subst hi
      rw [R', show a + (l'+1) = a + l' + 1 by omega]
      have hc := s_comm_R' n (a + l' + 1) a l' (Or.inr (by omega))
      calc R' n a l' * s n (a + l') * s n (a + l' + 1) * s n (a + l')
          = R' n a l' * (s n (a + l') * s n (a + l' + 1) * s n (a + l')) := by group
        _ = R' n a l' * (s n (a + l' + 1) * s n (a + l') * s n (a + l' + 1)) := by
            rw [s_braid n (a + l') h3]
        _ = (s n (a + l' + 1) * R' n a l') * s n (a + l') * s n (a + l' + 1) := by rw [hc]; group
        _ = _ := by group

/-! ## Coset representatives and the free generators -/

def c (n k : ℕ) : ArtinBraidGroup (n+1) := R n k (n - k)
def c' (n k : ℕ) : ArtinBraidGroup (n+1) := R' n k (n - k)
def D (n k : ℕ) : ArtinBraidGroup (n+1) := c n k * c' n k

theorem c_self (n : ℕ) : c n n = 1 := by simp [c, R]
theorem c'_self (n : ℕ) : c' n n = 1 := by simp [c', R']
theorem D_self (n : ℕ) : D n n = 1 := by simp [D, c_self, c'_self]

theorem c_step (n k : ℕ) (h : k < n) : c n k = c n (k+1) * s n k := by
  unfold c; rw [show n - k = (n - (k+1)) + 1 by omega, R_succ']
theorem c'_step (n k : ℕ) (h : k < n) : c' n k = s n k * c' n (k+1) := by
  unfold c'; rw [show n - k = (n - (k+1)) + 1 by omega, R'_succ']

theorem comm_c (n j k : ℕ) (h : j + 2 ≤ k) : s n j * c n k = c n k * s n j :=
  s_comm_R n j k _ (Or.inl h)
theorem comm_c' (n j k : ℕ) (h : j + 2 ≤ k) : s n j * c' n k = c' n k * s n j :=
  s_comm_R' n j k _ (Or.inl h)

theorem c_shift (n k i : ℕ) (h1 : k ≤ i) (h3 : i + 1 < n) : c n k * s n (i+1) = s n i * c n k :=
  R_shift n k (n-k) i h1 (by omega) h3
theorem c'_shift (n k j : ℕ) (h1 : k ≤ j) (h3 : j + 1 < n) : c' n k * s n j = s n (j+1) * c' n k :=
  R'_shift n k (n-k) j h1 (by omega) h3

theorem c_mul_s_self (n k : ℕ) (h : k < n) :
    c n k * s n k = D n k * (D n (k+1))⁻¹ * c n (k+1) := by
  unfold D; rw [c_step n k h, c'_step n k h]; group

theorem D_comm_ge (n j k : ℕ) (h1 : k ≤ j) (h3 : j + 1 < n) : s n j * D n k = D n k * s n j := by
  unfold D
  rw [← mul_assoc, ← c_shift n k j h1 h3, mul_assoc, ← c'_shift n k j h1 h3, mul_assoc]

theorem D_comm_le (n j k : ℕ) (h : j + 2 ≤ k) : s n j * D n k = D n k * s n j := by
  unfold D
  rw [← mul_assoc, comm_c n j k h, mul_assoc, comm_c' n j k h, mul_assoc]

theorem grp_conj1 {G : Type*} [Group G] (a b C C' : G) (hab : a * b * a = b * a * b)
    (hC : a * C = C * a) (hC' : a * C' = C' * a) :
    a * (C * b * b * C') * a⁻¹ = (C * C') * (C * b * b * C')⁻¹ * (C * b * a * a * b * C') := by
  have e1 : a * b * a⁻¹ = b⁻¹ * a * b := by
    calc a * b * a⁻¹ = b⁻¹ * (b * a * b) * a⁻¹ * a⁻¹ * a := by group
      _ = b⁻¹ * (a * b * a) * a⁻¹ * a⁻¹ * a := by rw [hab]
      _ = _ := by group
  have e2 : a * (b * b) * a⁻¹ = b⁻¹ * (a * a) * b := by
    calc a * (b * b) * a⁻¹ = (a * b * a⁻¹) * (a * b * a⁻¹) := by group
      _ = _ := by rw [e1]; group
  have hC'2 : C' * a⁻¹ = a⁻¹ * C' := by
    calc C' * a⁻¹ = a⁻¹ * (a * C') * a⁻¹ := by group
      _ = a⁻¹ * (C' * a) * a⁻¹ := by rw [hC']
      _ = _ := by group
  calc a * (C * b * b * C') * a⁻¹ = (a * C) * b * b * (C' * a⁻¹) := by group
    _ = (C * a) * b * b * (a⁻¹ * C') := by rw [hC, hC'2]
    _ = C * (a * (b * b) * a⁻¹) * C' := by group
    _ = C * (b⁻¹ * (a * a) * b) * C' := by rw [e2]
    _ = _ := by group

theorem grp_conj2 {G : Type*} [Group G] (a b C C' : G) (hab : a * b * a = b * a * b)
    (hC : a * C = C * a) (hC' : a * C' = C' * a) :
    a⁻¹ * (C * b * b * C') * a = (C * b * a * a * b * C') * (C * b * b * C')⁻¹ * (C * C') := by
  have e1 : a⁻¹ * b * a = b * a * b⁻¹ := by
    calc a⁻¹ * b * a = a⁻¹ * (b * a * b) * b⁻¹ := by group
      _ = a⁻¹ * (a * b * a) * b⁻¹ := by rw [hab]
      _ = _ := by group
  have e2 : a⁻¹ * (b * b) * a = b * (a * a) * b⁻¹ := by
    calc a⁻¹ * (b * b) * a = (a⁻¹ * b * a) * (a⁻¹ * b * a) := by group
      _ = _ := by rw [e1]; group
  have hC2 : a⁻¹ * C = C * a⁻¹ := by
    calc a⁻¹ * C = a⁻¹ * (C * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * C) * a⁻¹ := by rw [hC]
      _ = _ := by group
  calc a⁻¹ * (C * b * b * C') * a = (a⁻¹ * C) * b * b * (C' * a) := by group
    _ = (C * a⁻¹) * b * b * (a * C') := by rw [hC2, hC']
    _ = C * (a⁻¹ * (b * b) * a) * C' := by group
    _ = C * (b * (a * a) * b⁻¹) * C' := by rw [e2]
    _ = _ := by group

theorem D_conj (n j : ℕ) (h : j + 1 < n) :
    s n j * D n (j+1) * (s n j)⁻¹ = D n (j+2) * (D n (j+1))⁻¹ * D n j ∧
    (s n j)⁻¹ * D n (j+1) * s n j = D n j * (D n (j+1))⁻¹ * D n (j+2) := by
  have eDj : D n j = c n (j+2) * s n (j+1) * s n j * s n j * s n (j+1) * c' n (j+2) := by
    unfold D; rw [c_step n j (by omega), c'_step n j (by omega), c_step n (j+1) h,
      c'_step n (j+1) h]; group
  have eDj1 : D n (j+1) = c n (j+2) * s n (j+1) * s n (j+1) * c' n (j+2) := by
    unfold D; rw [c_step n (j+1) h, c'_step n (j+1) h]; group
  have eDj2 : D n (j+2) = c n (j+2) * c' n (j+2) := rfl
  rw [eDj, eDj1, eDj2]
  have hab := s_braid n j h
  have hC := comm_c n j (j+2) le_rfl
  have hC' := comm_c' n j (j+2) le_rfl
  exact ⟨grp_conj1 _ _ _ _ hab hC hC', grp_conj2 _ _ _ _ hab hC hC'⟩

/-! ## The action of the free generators -/

def E (n k : ℕ) : ℕ → FreeGroup (Fin (n+1))
  | 0 => X n k
  | l+1 => E n k l * X n (k + l + 1)

def yv (n k l : ℕ) : FreeGroup (Fin (n+1)) := E n k l * X n (k + l + 1) * (E n k l)⁻¹

def Fm (n k l j : ℕ) : FreeGroup (Fin (n+1)) :=
  if j < k then X n j else if j ≤ k + l then yv n k l * X n j * (yv n k l)⁻¹
  else if j = k + l + 1 then E n k l * X n j * (E n k l)⁻¹ else X n j

theorem Fm_lt (n k l j : ℕ) (h : j < k) : Fm n k l j = X n j := by
  unfold Fm; rw [if_pos h]
theorem Fm_mid (n k l j : ℕ) (h1 : k ≤ j) (h2 : j ≤ k + l) :
    Fm n k l j = yv n k l * X n j * (yv n k l)⁻¹ := by
  unfold Fm; rw [if_neg (by omega), if_pos h2]
theorem Fm_top (n k l j : ℕ) (h : j = k + l + 1) :
    Fm n k l j = E n k l * X n j * (E n k l)⁻¹ := by
  unfold Fm; rw [if_neg (by omega), if_neg (by omega), if_pos h]
theorem Fm_gt (n k l j : ℕ) (h : k + l + 1 < j) : Fm n k l j = X n j := by
  unfold Fm; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

def M' (n k l : ℕ) : ArtinBraidGroup (n+1) := R n (k+1) l * s n k * s n k * R' n (k+1) l

theorem M'_zero (n k : ℕ) : M' n k 0 = s n k * s n k := by simp [M', R, R']

theorem M'_succ (n k l : ℕ) : M' n k (l+1) = s n (k+l+1) * M' n k l * s n (k+l+1) := by
  simp only [M', R, R', show k + 1 + l = k + l + 1 by omega, mul_assoc]

section XiM
variable {n : ℕ} (ξ : ArtinBraidGroup (n+1) →* MulAut (FreeGroup (Fin (n+1))))
  (hξ : ∀ i : Fin (n + 1 - 1), ∀ w : FreeGroup (Fin (n + 1)), ξ (sigma i) w = artinEndo (n + 1) i w)
include hξ

theorem xi_s_E (i k l : ℕ) (h : k + l < i) : ξ (s n i) (E n k l) = E n k l := by
  induction l with
  | zero => rw [E, xi_s_other ξ hξ i k (by omega) (by omega)]
  | succ l ih => rw [E, map_mul, ih (by omega), xi_s_other ξ hξ i _ (by omega) (by omega)]

theorem xi_M (k l : ℕ) (h : k + l + 1 ≤ n) : ∀ j, ξ (M' n k l) (X n j) = Fm n k l j := by
  induction l with
  | zero =>
    intro j
    have hk : k < n := by omega
    rw [M'_zero, map_mul, MulAut.mul_apply]
    by_cases h1 : j < k
    · rw [Fm_lt _ _ _ _ h1, xi_s_other ξ hξ k j (by omega) (by omega),
        xi_s_other ξ hξ k j (by omega) (by omega)]
    by_cases h2 : j = k
    · subst h2
      rw [Fm_mid _ _ _ _ le_rfl (by omega), xi_s_self ξ hξ _ hk, map_mul, map_mul, map_inv,
        xi_s_self ξ hξ _ hk, xi_s_succ ξ hξ _ hk]
      simp only [yv, E, Nat.add_zero]
    by_cases h3 : j = k + 1
    · subst h3
      rw [Fm_top _ _ _ _ (by omega), xi_s_succ ξ hξ _ hk, xi_s_self ξ hξ _ hk]
      simp only [E]
    · rw [Fm_gt _ _ _ _ (by omega), xi_s_other ξ hξ k j (by omega) (by omega),
        xi_s_other ξ hξ k j (by omega) (by omega)]
  | succ l ih =>
    intro j
    have hm : k + l + 1 < n := by omega
    have ih := ih (by omega)
    rw [M'_succ, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
    have hE := xi_s_E ξ hξ (k + l + 1) k l (by omega)
    have e1 : k + (l + 1) + 1 = k + l + 1 + 1 := by omega
    by_cases h1 : j < k
    · rw [Fm_lt _ _ _ _ h1, xi_s_other ξ hξ _ j (by omega) (by omega), ih,
        Fm_lt _ _ _ _ h1, xi_s_other ξ hξ _ j (by omega) (by omega)]
    by_cases h2 : j ≤ k + l
    · rw [Fm_mid _ _ _ _ (by omega) (by omega), xi_s_other ξ hξ _ j (by omega) (by omega), ih,
        Fm_mid _ _ _ _ (by omega) h2]
      simp only [yv, map_mul, map_inv, hE, xi_s_self ξ hξ _ hm,
        xi_s_other ξ hξ (k + l + 1) j (by omega) (by omega), E, e1]
      group
    by_cases h3 : j = k + l + 1
    · subst h3
      rw [Fm_mid _ _ _ _ (by omega) (by omega), xi_s_self ξ hξ _ hm]
      simp only [map_mul, map_inv, ih]
      rw [Fm_top _ _ _ _ rfl, Fm_gt _ _ _ _ (by omega)]
      simp only [yv, map_mul, map_inv, hE, xi_s_self ξ hξ _ hm, xi_s_succ ξ hξ _ hm, E, e1]
      group
    by_cases h4 : j = k + l + 1 + 1
    · subst h4
      rw [Fm_top _ _ _ _ (by omega), xi_s_succ ξ hξ _ hm, ih, Fm_top _ _ _ _ rfl]
      simp only [map_mul, map_inv, hE, xi_s_self ξ hξ _ hm, E, e1]
      group
    · rw [Fm_gt _ _ _ _ (by omega), xi_s_other ξ hξ _ j (by omega) (by omega), ih,
        Fm_gt _ _ _ _ (by omega), xi_s_other ξ hξ _ j (by omega) (by omega)]

omit hξ in
theorem D_eq_M' (k : ℕ) (hk : k < n) : D n k = M' n k (n - (k+1)) := by
  unfold D M'; rw [c_step n k hk, c'_step n k hk]; unfold c c'; group

theorem xi_D (k : ℕ) (hk : k < n) (j : ℕ) :
    ξ (D n k) (X n j) = Fm n k (n - (k+1)) j := by
  rw [D_eq_M' k hk]; exact xi_M ξ hξ k _ (by omega) j

theorem xi_R_low (a l j : ℕ) (h : j < a) : ξ (R n a l) (X n j) = X n j := by
  induction l with
  | zero => simp [R]
  | succ l ih => rw [R, map_mul, MulAut.mul_apply, ih, xi_s_other ξ hξ _ j (by omega) (by omega)]

theorem xi_c_conj : ∀ d k, k + d = n → ∃ g, ξ (c n k) (X n k) = g * X n n * g⁻¹ := by
  intro d
  induction d with
  | zero => intro k hk; subst hk; exact ⟨1, by simp [c_self]⟩
  | succ d ih =>
    intro k hk
    obtain ⟨g, hg⟩ := ih (k+1) (by omega)
    refine ⟨X n k * g, ?_⟩
    rw [c_step n k (by omega), map_mul, MulAut.mul_apply, xi_s_self ξ hξ _ (by omega),
      map_mul, map_mul, map_inv, hg]
    unfold c
    rw [xi_R_low ξ hξ _ _ _ (by omega)]
    group

end XiM

/-! ## Killing the last generator -/

def q (n : ℕ) : FreeGroup (Fin (n+1)) →* FreeGroup (Fin n) :=
  FreeGroup.lift (fun j => if h : (j : ℕ) < n then FreeGroup.of ⟨j, h⟩ else 1)

def Y (n j : ℕ) : FreeGroup (Fin n) := if h : j < n then FreeGroup.of ⟨j, h⟩ else 1

theorem q_X (n j : ℕ) : q n (X n j) = Y n j := by
  unfold X Y
  by_cases h1 : j < n + 1
  · rw [dif_pos h1, q, FreeGroup.lift_apply_of]
  · rw [dif_neg h1, dif_neg (by omega), map_one]

theorem Y_self (n : ℕ) : Y n n = 1 := by unfold Y; rw [dif_neg (lt_irrefl n)]

theorem X_of (n : ℕ) (a : Fin (n+1)) : FreeGroup.of a = X n a.val := by
  unfold X; rw [dif_pos a.isLt]

def P (n : ℕ) : FreeGroup (Fin n) →* ArtinBraidGroup (n+1) :=
  FreeGroup.lift (fun k => D n k.val)

theorem D_mem (n k : ℕ) (hk : k ≤ n) : D n k ∈ (P n).range := by
  rcases Nat.lt_or_ge k n with h | h
  · exact ⟨FreeGroup.of ⟨k, h⟩, by rw [P, FreeGroup.lift_apply_of]⟩
  · rw [show k = n by omega, D_self]; exact one_mem _

def θ (n : ℕ) : FreeGroup (Fin n) →* FreeGroup (Fin n) :=
  FreeGroup.lift (fun k => (q n (E n k.val (n - (k.val + 1))))⁻¹)

def lam (n : ℕ) : FreeGroup (Fin n) →* FreeGroup (Fin n) :=
  FreeGroup.lift (fun k => if k.val + 1 < n then (Y n k.val)⁻¹ * Y n (k.val + 1) else (Y n k.val)⁻¹)

theorem E_succ_left (n k l : ℕ) : E n k (l+1) = X n k * E n (k+1) l := by
  induction l with
  | zero => rfl
  | succ l ih => rw [E, ih, E, mul_assoc, show k + (l + 1) + 1 = k + 1 + l + 1 by omega]

theorem lam_Y (n k : ℕ) (hk : k < n) :
    lam n (Y n k) = if k + 1 < n then (Y n k)⁻¹ * Y n (k + 1) else (Y n k)⁻¹ := by
  conv_lhs => rw [Y, dif_pos hk]
  rw [lam, FreeGroup.lift_apply_of]

theorem lam_qE (n : ℕ) : ∀ l k, k + l + 1 = n → lam n (q n (E n k l)) = (Y n k)⁻¹ := by
  intro l
  induction l with
  | zero => intro k hk; rw [E, q_X, lam_Y n k (by omega), if_neg (by omega)]
  | succ l ih =>
    intro k hk
    rw [E_succ_left, map_mul, map_mul, q_X, lam_Y n k (by omega), if_pos (by omega),
      ih (k+1) (by omega)]
    group

theorem lam_theta (n : ℕ) (w : FreeGroup (Fin n)) : lam n (θ n w) = w := by
  have : (lam n).comp (θ n) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom; intro k
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, θ, FreeGroup.lift_apply_of, map_inv]
    rw [lam_qE n (n - (k.val + 1)) k.val (by omega), inv_inv, Y, dif_pos k.isLt]
  exact DFunLike.congr_fun this w

theorem of_eq_conj_of {α : Type*} [DecidableEq α] {j k : α} {A : FreeGroup α}
    (h : FreeGroup.of j = A * FreeGroup.of k * A⁻¹) : j = k := by
  by_contra hne
  set phi : FreeGroup α →* Multiplicative ℤ :=
    FreeGroup.lift (fun m => if m = j then Multiplicative.ofAdd (1 : ℤ) else 1) with hphi
  have h1 : phi (FreeGroup.of j) = Multiplicative.ofAdd (1 : ℤ) := by
    rw [hphi]; simp
  have h3 : phi (FreeGroup.of k) = 1 := by
    rw [hphi]; simp [if_neg (Ne.symm hne)]
  have h2 : phi (A * FreeGroup.of k * A⁻¹) = phi (FreeGroup.of k) := by
    rw [map_mul, map_mul, map_inv, mul_comm (phi A) (phi (FreeGroup.of k)),
      mul_assoc, mul_inv_cancel, mul_one]
  rw [h, h2, h3] at h1
  exact absurd h1.symm (by simp)

/-! ## The embedding of `B_n` -/

theorem iota_rel (n : ℕ) : ∀ r ∈ braidRels n,
    FreeGroup.lift (fun i : Fin (n-1) => s n i.val) r = 1 := by
  intro r hr
  rcases hr with ⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [s_comm n i.val j.val (by omega)]; group
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [hij, s_braid n i.val (by omega)]; group

def iota (n : ℕ) : ArtinBraidGroup n →* ArtinBraidGroup (n+1) := PresentedGroup.toGroup (iota_rel n)

theorem iota_sigma (n : ℕ) (i : Fin (n-1)) : iota n (sigma i) = s n i.val :=
  PresentedGroup.toGroup.of (iota_rel n)

theorem braid_induction {m : ℕ} (p : ArtinBraidGroup m → Prop) (h1 : p 1)
    (hmul : ∀ a b, p a → p b → p (a * b)) (hgen : ∀ i, p (sigma i))
    (hinv : ∀ i, p (sigma i)⁻¹) : ∀ b, p b := by
  intro b
  induction b using PresentedGroup.induction_on with
  | H z =>
    induction z using FreeGroup.induction_on with
    | C1 => rw [map_one]; exact h1
    | of x => exact hgen x
    | inv_of x _ => rw [map_inv]; exact hinv x
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy

theorem s_eq_sigma (n j : ℕ) (h : j < n) : s n j = sigma ⟨j, by omega⟩ := by
  unfold s; rw [dif_pos h]

/-! ## The coset decomposition -/

def Tset (n : ℕ) (β : ArtinBraidGroup (n+1)) : Prop :=
  ∃ w b k, k ≤ n ∧ β = P n w * iota n b * c n k

theorem conj_gen (n j : ℕ) (h : j + 1 < n) : ∀ w, s n j * P n w * (s n j)⁻¹ ∈ (P n).range ∧
    (s n j)⁻¹ * P n w * s n j ∈ (P n).range := by
  intro w
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of k =>
    rw [P, FreeGroup.lift_apply_of, ← P]
    rcases Nat.lt_or_ge j k.val with h1 | h1
    · rcases Nat.lt_or_ge (j+1) k.val with h2 | h2
      · have e := D_comm_le n j k.val (by omega)
        constructor
        · rw [e]; simpa using D_mem n k.val k.isLt.le
        · rw [mul_assoc, ← e]; simpa using D_mem n k.val k.isLt.le
      · have hk : k.val = j + 1 := by omega
        rw [hk]
        obtain ⟨e1, e2⟩ := D_conj n j h
        rw [e1, e2]
        exact ⟨mul_mem (mul_mem (D_mem n _ (by omega)) (inv_mem (D_mem n _ (by omega))))
            (D_mem n _ (by omega)),
          mul_mem (mul_mem (D_mem n _ (by omega)) (inv_mem (D_mem n _ (by omega))))
            (D_mem n _ (by omega))⟩
    · have e := D_comm_ge n j k.val h1 h
      constructor
      · rw [e]; simpa using D_mem n k.val k.isLt.le
      · rw [mul_assoc, ← e]; simpa using D_mem n k.val k.isLt.le
  | inv_of k hk =>
    rw [map_inv]
    constructor
    · have := inv_mem hk.1; rw [show s n j * (P n (FreeGroup.of k))⁻¹ * (s n j)⁻¹ =
        (s n j * P n (FreeGroup.of k) * (s n j)⁻¹)⁻¹ by group]; exact this
    · have := inv_mem hk.2; rw [show (s n j)⁻¹ * (P n (FreeGroup.of k))⁻¹ * s n j =
        ((s n j)⁻¹ * P n (FreeGroup.of k) * s n j)⁻¹ by group]; exact this
  | mul x y hx hy =>
    rw [map_mul]
    constructor
    · rw [show s n j * (P n x * P n y) * (s n j)⁻¹ =
        (s n j * P n x * (s n j)⁻¹) * (s n j * P n y * (s n j)⁻¹) by group]
      exact mul_mem hx.1 hy.1
    · rw [show (s n j)⁻¹ * (P n x * P n y) * s n j =
        ((s n j)⁻¹ * P n x * s n j) * ((s n j)⁻¹ * P n y * s n j) by group]
      exact mul_mem hx.2 hy.2

theorem normal_iota (n : ℕ) : ∀ b : ArtinBraidGroup n, ∀ x ∈ (P n).range,
    iota n b * x * (iota n b)⁻¹ ∈ (P n).range ∧ (iota n b)⁻¹ * x * iota n b ∈ (P n).range := by
  apply braid_induction
  · intro x hx; simpa using hx
  · intro a b ha hb x hx
    rw [map_mul]
    constructor
    · rw [show iota n a * iota n b * x * (iota n a * iota n b)⁻¹ =
        iota n a * (iota n b * x * (iota n b)⁻¹) * (iota n a)⁻¹ by group]
      exact (ha _ (hb x hx).1).1
    · rw [show (iota n a * iota n b)⁻¹ * x * (iota n a * iota n b) =
        (iota n b)⁻¹ * ((iota n a)⁻¹ * x * iota n a) * iota n b by group]
      exact (hb _ (ha x hx).2).2
  · intro i x hx
    obtain ⟨w, rfl⟩ := hx
    rw [iota_sigma]
    exact conj_gen n i.val (by omega) w
  · intro i x hx
    obtain ⟨w, rfl⟩ := hx
    rw [map_inv, iota_sigma, inv_inv]
    exact (conj_gen n i.val (by omega) w).symm

theorem absorb (n : ℕ) (w : FreeGroup (Fin n)) (b : ArtinBraidGroup n)
    (A : ArtinBraidGroup (n+1)) (hA : A ∈ (P n).range) :
    ∃ w', P n w * iota n b * A = P n w' * iota n b := by
  obtain ⟨w'', hw''⟩ := (normal_iota n b A hA).1
  refine ⟨w * w'', ?_⟩
  rw [map_mul, hw'']; group

theorem Tset_step (n j : ℕ) (hj : j < n) (β : ArtinBraidGroup (n+1)) (hβ : Tset n β) :
    Tset n (β * s n j) ∧ Tset n (β * (s n j)⁻¹) := by
  obtain ⟨w, b, k, hk, rfl⟩ := hβ
  rcases Nat.lt_or_ge (j + 1) k with h1 | h1
  · -- j + 2 ≤ k : commute
    have e := comm_c n j k (by omega)
    have hs : iota n (sigma ⟨j, by omega⟩) = s n j := iota_sigma n _
    constructor
    · refine ⟨w, b * sigma ⟨j, by omega⟩, k, hk, ?_⟩
      rw [map_mul, hs, mul_assoc, ← e]; group
    · refine ⟨w, b * (sigma ⟨j, by omega⟩)⁻¹, k, hk, ?_⟩
      have e' : c n k * (s n j)⁻¹ = (s n j)⁻¹ * c n k := by
        calc c n k * (s n j)⁻¹ = (s n j)⁻¹ * (s n j * c n k) * (s n j)⁻¹ := by group
          _ = (s n j)⁻¹ * (c n k * s n j) * (s n j)⁻¹ := by rw [e]
          _ = _ := by group
      rw [map_mul, map_inv, hs, mul_assoc, e']; group
  rcases Nat.lt_or_ge j k with h2 | h2
  · -- k = j + 1
    have hk' : k = j + 1 := by omega
    subst hk'
    constructor
    · refine ⟨w, b, j, by omega, ?_⟩
      rw [c_step n j hj]; group
    · have hA : (D n j * (D n (j+1))⁻¹)⁻¹ ∈ (P n).range :=
        inv_mem (mul_mem (D_mem n j (by omega)) (inv_mem (D_mem n (j+1) (by omega))))
      obtain ⟨w', hw'⟩ := absorb n w b _ hA
      refine ⟨w', b, j, by omega, ?_⟩
      have e : c n (j+1) * (s n j)⁻¹ = (D n j * (D n (j+1))⁻¹)⁻¹ * c n j := by
        have := c_mul_s_self n j hj
        rw [c_step n j hj] at this ⊢
        calc c n (j+1) * (s n j)⁻¹
            = (D n j * (D n (j+1))⁻¹)⁻¹ * (D n j * (D n (j+1))⁻¹ * c n (j+1)) * (s n j)⁻¹ *
                (s n j)⁻¹ * s n j := by group
          _ = (D n j * (D n (j+1))⁻¹)⁻¹ * (c n (j+1) * s n j * s n j) * (s n j)⁻¹ *
                (s n j)⁻¹ * s n j := by rw [← this]
          _ = _ := by group
      rw [mul_assoc, e, ← mul_assoc, hw']
  rcases Nat.lt_or_ge k j with h3 | h3
  · -- k < j : shift
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have e := c_shift n k i (by omega) hj
    have hs : iota n (sigma ⟨i, by omega⟩) = s n i := iota_sigma n _
    constructor
    · refine ⟨w, b * sigma ⟨i, by omega⟩, k, hk, ?_⟩
      rw [map_mul, hs, mul_assoc, e]; group
    · refine ⟨w, b * (sigma ⟨i, by omega⟩)⁻¹, k, hk, ?_⟩
      have e' : c n k * (s n (i+1))⁻¹ = (s n i)⁻¹ * c n k := by
        calc c n k * (s n (i+1))⁻¹ = (s n i)⁻¹ * (s n i * c n k) * (s n (i+1))⁻¹ := by group
          _ = (s n i)⁻¹ * (c n k * s n (i+1)) * (s n (i+1))⁻¹ := by rw [e]
          _ = _ := by group
      rw [map_mul, map_inv, hs, mul_assoc, e']; group
  · -- k = j
    have hk' : k = j := by omega
    subst hk'
    constructor
    · have hA : D n k * (D n (k+1))⁻¹ ∈ (P n).range :=
        mul_mem (D_mem n k (by omega)) (inv_mem (D_mem n (k+1) (by omega)))
      obtain ⟨w', hw'⟩ := absorb n w b _ hA
      refine ⟨w', b, k+1, by omega, ?_⟩
      rw [mul_assoc, c_mul_s_self n k hj, show P n w * iota n b * (D n k * (D n (k+1))⁻¹ * c n (k+1))
        = (P n w * iota n b * (D n k * (D n (k+1))⁻¹)) * c n (k+1) by group, hw']
    · refine ⟨w, b, k+1, by omega, ?_⟩
      rw [c_step n k hj]; group

theorem Tset_all (n : ℕ) (β : ArtinBraidGroup (n+1)) : Tset n β := by
  have key : ∀ g : ArtinBraidGroup (n+1), ∀ β, Tset n β → Tset n (β * g) := by
    apply braid_induction
    · intro β h; simpa using h
    · intro a b ha hb β h; rw [← mul_assoc]; exact hb _ (ha _ h)
    · intro i β h
      have := (Tset_step n i.val (by omega) β h).1
      rwa [s_eq_sigma n i.val (by omega)] at this
    · intro i β h
      have := (Tset_step n i.val (by omega) β h).2
      rwa [s_eq_sigma n i.val (by omega)] at this
  have h1 : Tset n 1 := ⟨1, 1, n, le_rfl, by simp [c_self]⟩
  simpa using key β 1 h1

/-! ## Faithfulness on the free part -/

section Final
variable {n : ℕ} (ξ : ArtinBraidGroup (n+1) →* MulAut (FreeGroup (Fin (n+1))))
  (hξ : ∀ i : Fin (n + 1 - 1), ∀ w : FreeGroup (Fin (n + 1)), ξ (sigma i) w = artinEndo (n + 1) i w)
include hξ

theorem qD (k : ℕ) (hk : k < n) (w : FreeGroup (Fin (n+1))) : q n (ξ (D n k) w) = q n w := by
  have hy : q n (yv n k (n - (k+1))) = 1 := by
    unfold yv; rw [show k + (n - (k+1)) + 1 = n by omega]
    simp only [map_mul, map_inv, q_X, Y_self, mul_one, mul_inv_cancel]
  have : (q n).comp (ξ (D n k)).toMonoidHom = q n := by
    apply FreeGroup.ext_hom; intro a
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [X_of n a, xi_D ξ hξ k hk]
    have ha := a.isLt
    by_cases h1 : a.val < k
    · rw [Fm_lt _ _ _ _ h1]
    by_cases h2 : a.val ≤ k + (n - (k+1))
    · rw [Fm_mid _ _ _ _ (by omega) h2]; simp only [map_mul, map_inv, hy]; group
    · rw [Fm_top _ _ _ _ (by omega), show a.val = n by omega]
      simp only [map_mul, map_inv, q_X, Y_self]; group
  exact DFunLike.congr_fun this w

theorem qP (w : FreeGroup (Fin n)) : ∀ x, q n (ξ (P n w) x) = q n (x) := by
  induction w using FreeGroup.induction_on with
  | C1 => intro x; simp
  | of k => intro x; rw [P, FreeGroup.lift_apply_of]; exact qD ξ hξ k.val k.isLt x
  | inv_of k hk =>
    intro x
    rw [map_inv, map_inv]
    have := hk ((ξ (P n (FreeGroup.of k)))⁻¹ x)
    rw [MulAut.apply_inv_self] at this
    exact this.symm
  | mul a b ha hb => intro x; rw [map_mul, map_mul, MulAut.mul_apply, ha, hb]

theorem S_all (w : FreeGroup (Fin n)) :
    ∃ g, ξ (P n w) (X n n) = g * X n n * g⁻¹ ∧ (q n g)⁻¹ = θ n w := by
  have hinv : ∀ w : FreeGroup (Fin n), (∃ g, ξ (P n w) (X n n) = g * X n n * g⁻¹ ∧ (q n g)⁻¹ = θ n w) →
      ∃ g, ξ (P n w⁻¹) (X n n) = g * X n n * g⁻¹ ∧ (q n g)⁻¹ = θ n w⁻¹ := by
    rintro w ⟨g, hg1, hg2⟩
    set φ := ξ (P n w)
    refine ⟨(φ⁻¹ g)⁻¹, ?_, ?_⟩
    · rw [map_inv, map_inv]
      apply MulEquiv.injective φ
      rw [MulAut.apply_inv_self]
      simp only [map_mul, map_inv, MulAut.apply_inv_self, hg1, inv_inv]; group
    · rw [map_inv, inv_inv, map_inv, ← hg2, inv_inv]
      have := qP ξ hξ w (φ⁻¹ g)
      rw [MulAut.apply_inv_self] at this
      exact this.symm
  induction w using FreeGroup.induction_on with
  | C1 => exact ⟨1, by simp, by simp⟩
  | of k =>
    refine ⟨E n k.val (n - (k.val+1)), ?_, ?_⟩
    · rw [P, FreeGroup.lift_apply_of, xi_D ξ hξ k.val k.isLt, Fm_top _ _ _ _ (by omega)]
    · rw [θ, FreeGroup.lift_apply_of]
  | inv_of k hk => exact hinv _ hk
  | mul a b ha hb =>
    obtain ⟨g1, h11, h12⟩ := ha
    obtain ⟨g2, h21, h22⟩ := hb
    refine ⟨ξ (P n a) g2 * g1, ?_, ?_⟩
    · rw [map_mul, map_mul, MulAut.mul_apply, h21]
      simp only [map_mul, map_inv, h11]; group
    · rw [map_mul, qP ξ hξ a, map_mul, ← h12, ← h22]; group

theorem P_faithful (w : FreeGroup (Fin n)) (h : ξ (P n w) = 1) : w = 1 := by
  obtain ⟨g, hg1, hg2⟩ := S_all ξ hξ w
  rw [h, MulAut.one_apply] at hg1
  have hc : g * X n n = X n n * g := by
    calc g * X n n = (g * X n n * g⁻¹) * g := by group
      _ = X n n * g := by rw [← hg1]
  have hX : X n n = FreeGroup.of (⟨n, by omega⟩ : Fin (n+1)) := by unfold X; rw [dif_pos (by omega)]
  rw [hX] at hc
  have hz := centralizer_of _ _ g le_rfl hc
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hq : q n g = 1 := by
    rw [← hm, map_zpow, X_of, q_X, Y_self, one_zpow]
  rw [← lam_theta n w, ← hg2, hq, inv_one, map_one]

/-! ## The induced representation of `B_n` -/

def incl (n : ℕ) : FreeGroup (Fin n) →* FreeGroup (Fin (n+1)) := FreeGroup.map Fin.castSucc

omit hξ in
theorem q_incl (x : FreeGroup (Fin n)) : q n (incl n x) = x := by
  have : (q n).comp (incl n) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom; intro a
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, incl, FreeGroup.map.of, q,
      FreeGroup.lift_apply_of, Fin.val_castSucc]
    rw [dif_pos a.isLt]
  exact DFunLike.congr_fun this x

theorem iota_fix (b : ArtinBraidGroup n) : ξ (iota n b) (X n n) = X n n := by
  revert b
  apply braid_induction
  · simp
  · intro a b ha hb; rw [map_mul, map_mul, MulAut.mul_apply, hb, ha]
  · intro i; rw [iota_sigma]; exact xi_s_other ξ hξ _ _ (by omega) (by omega)
  · intro i
    rw [map_inv, map_inv, iota_sigma]
    conv_lhs => rw [← xi_s_other ξ hξ i.val n (by omega) (by omega)]
    rw [MulAut.inv_apply_self]

def psi (b : ArtinBraidGroup n) : FreeGroup (Fin n) →* FreeGroup (Fin n) :=
  (q n).comp ((ξ (iota n b)).toMonoidHom.comp (incl n))

theorem K (b : ArtinBraidGroup n) (w : FreeGroup (Fin (n+1))) :
    q n (ξ (iota n b) w) = psi ξ b (q n w) := by
  have : (q n).comp (ξ (iota n b)).toMonoidHom = (psi ξ b).comp (q n) := by
    apply FreeGroup.ext_hom; intro a
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rcases Nat.lt_or_ge a.val n with h | h
    · have e : incl n (q n (FreeGroup.of a)) = FreeGroup.of a := by
        simp only [q, FreeGroup.lift_apply_of, dif_pos h, incl, FreeGroup.map.of]; rfl
      simp only [psi, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e]
    · have ha : a = ⟨n, by omega⟩ := Fin.ext (by show a.val = n; have := a.isLt; omega)
      rw [ha]
      have e1 : (FreeGroup.of (⟨n, by omega⟩ : Fin (n+1))) = X n n := X_of n _
      rw [e1, iota_fix ξ hξ, q_X, Y_self, map_one]
  exact DFunLike.congr_fun this w

theorem psi_mul (a b : ArtinBraidGroup n) (w : FreeGroup (Fin n)) :
    psi ξ (a * b) w = psi ξ a (psi ξ b w) := by
  show q n (ξ (iota n (a * b)) (incl n w)) = psi ξ a (q n (ξ (iota n b) (incl n w)))
  rw [map_mul, map_mul, MulAut.mul_apply, K ξ hξ]

omit hξ in
theorem psi_one (w : FreeGroup (Fin n)) : psi ξ 1 w = w := by
  show q n (ξ (iota n 1) (incl n w)) = w
  rw [map_one, map_one, MulAut.one_apply, q_incl]

def xin : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)) where
  toFun b :=
    { toFun := psi ξ b
      invFun := psi ξ b⁻¹
      left_inv := fun w => by rw [← psi_mul ξ hξ, inv_mul_cancel, psi_one]
      right_inv := fun w => by rw [← psi_mul ξ hξ, mul_inv_cancel, psi_one]
      map_mul' := map_mul (psi ξ b) }
  map_one' := by ext w; exact psi_one ξ w
  map_mul' a b := by ext w; exact psi_mul ξ hξ a b w

theorem xin_apply (b : ArtinBraidGroup n) (w : FreeGroup (Fin n)) : xin ξ hξ b w = psi ξ b w := rfl

theorem xin_sigma (i : Fin (n - 1)) (w : FreeGroup (Fin n)) :
    xin ξ hξ (sigma i) w = artinEndo n i w := by
  rw [xin_apply]
  have : psi ξ (sigma i) = artinEndo n i := by
    apply FreeGroup.ext_hom; intro a
    have hi := i.isLt
    have ha := a.isLt
    have e : incl n (FreeGroup.of a) = X n a.val := by
      simp only [incl, FreeGroup.map.of]; rw [X_of]; rfl
    simp only [psi, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e, iota_sigma]
    rw [xi_s_gen ξ hξ i.val a.val (by omega) (by omega), artinEndo, FreeGroup.lift_apply_of]
    simp only [strandIdx, strandIdxSucc, Fin.ext_iff]
    have yi : Y n i.val = FreeGroup.of ⟨i.val, by omega⟩ := by unfold Y; rw [dif_pos (by omega)]
    have yi1 : Y n (i.val + 1) = FreeGroup.of ⟨i.val + 1, by omega⟩ := by
      unfold Y; rw [dif_pos (by omega)]
    have ya : Y n a.val = FreeGroup.of a := by unfold Y; rw [dif_pos ha]
    split_ifs <;> simp only [map_mul, map_inv, q_X, yi, yi1, ya]
  rw [this]

end Final

end StepM

open StepM in
theorem _root_.solution (n : ℕ)
    (ih : ∀ xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)),
      (∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w) →
        Function.Injective xi) :
    ∀ xi : ArtinBraidGroup (n + 1) →* MulAut (FreeGroup (Fin (n + 1))),
      (∀ i : Fin (n + 1 - 1), ∀ w : FreeGroup (Fin (n + 1)),
          xi (sigma i) w = artinEndo (n + 1) i w) →
        Function.Injective xi := by
  intro ξ hξ
  rw [injective_iff_map_eq_one]
  intro β hβ
  obtain ⟨w, b, k, hk, rfl⟩ := Tset_all n β
  have happ : ∀ y, ξ (P n w) (ξ (iota n b) (ξ (c n k) y)) = y := by
    intro y
    have := DFunLike.congr_fun hβ y
    simpa [map_mul, MulAut.mul_apply] using this
  -- the coset representative is trivial
  have hkn : k = n := by
    by_contra hne
    have hk' : k < n := by omega
    obtain ⟨g, hg⟩ := xi_c_conj ξ hξ (n - k) k (by omega)
    obtain ⟨g2, hg2, -⟩ := S_all ξ hξ w
    have h1 := happ (X n k)
    rw [hg] at h1
    simp only [map_mul, map_inv, iota_fix ξ hξ, hg2] at h1
    have hXk : X n k = FreeGroup.of (⟨k, by omega⟩ : Fin (n+1)) := by
      unfold X; rw [dif_pos (by omega)]
    have hXn : X n n = FreeGroup.of (⟨n, by omega⟩ : Fin (n+1)) := by
      unfold X; rw [dif_pos (by omega)]
    rw [hXk, hXn] at h1
    have h2 : FreeGroup.of (⟨k, by omega⟩ : Fin (n+1)) =
        (ξ (P n w) (ξ (iota n b) g) * g2) * FreeGroup.of (⟨n, by omega⟩ : Fin (n+1)) *
          (ξ (P n w) (ξ (iota n b) g) * g2)⁻¹ := by rw [← h1]; group
    have := of_eq_conj_of h2
    exact hne (congrArg Fin.val this)
  rw [hkn, c_self] at happ
  -- the `B_n` part is trivial
  have hb : b = 1 := by
    apply ih (xin ξ hξ) (xin_sigma ξ hξ)
    rw [map_one]
    ext x
    rw [xin_apply, MulAut.one_apply]
    show q n (ξ (iota n b) (incl n x)) = x
    have := congrArg (q n) (happ (incl n x))
    rw [map_one, MulAut.one_apply, qP ξ hξ w, q_incl] at this
    exact this
  subst hb
  have hw : ξ (P n w) = 1 := by
    ext y
    have := happ y
    rw [map_one, map_one, MulAut.one_apply, MulAut.one_apply] at this
    rw [this, MulAut.one_apply]
  rw [P_faithful ξ hξ w hw, map_one, map_one, hkn, c_self, one_mul, one_mul]

end BraidsLinksMCG
