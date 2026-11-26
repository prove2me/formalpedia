-- Prove2me | solution 1 for GRH.dirichlet_weighted_prefix_cover_of_rational_table
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T16:16:20.643829+00:00
-- url     : https://prove2.me/submissions/f0ce4a7e-793e-4a40-b571-be66c6f7ec2b

import Definitions.Def_GRH_DirichletPrefix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open GRH.DirichletPrefix

private lemma bracket (D p t n v : ℕ) (hn : 0<n) (ht : 0<t)
    (lo : (v-1)^t*n^p ≤ D^t) (hi : D^t ≤ v^t*n^p) :
    ((v-1:ℕ):ℝ) ≤ (D:ℝ)*(n:ℝ)^(-((p:ℝ)/t)) ∧
      (D:ℝ)*(n:ℝ)^(-((p:ℝ)/t)) ≤ (v:ℝ) := by
  let z := (n:ℝ)^((p:ℝ)/t)
  have hz : 0 < z := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have power : z^t=(n:ℝ)^p := by
    dsimp [z]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _),div_mul_cancel₀ _
      (Nat.cast_ne_zero.mpr ht.ne'),Real.rpow_natCast]
  have l : (((v-1:ℕ):ℝ)*z)^t ≤ (D:ℝ)^t := by
    rw [mul_pow,power]
    exact_mod_cast lo
  have u : (D:ℝ)^t ≤ ((v:ℝ)*z)^t := by
    rw [mul_pow,power]
    exact_mod_cast hi
  rw [Real.rpow_neg (Nat.cast_nonneg _),← div_eq_mul_inv]
  exact ⟨(le_div_iff₀ hz).2 (le_of_pow_le_pow_left₀ ht.ne' (by positivity) l),
    (div_le_iff₀ hz).2 (le_of_pow_le_pow_left₀ ht.ne' (by positivity) u)⟩

/-- Integer power brackets for a finite table imply a weighted prefix
cover using one rational comparison for the total error. -/
theorem solution (d Q M R D p t v w : ℕ) (u : ℕ → ℕ) (a b H : ℝ)
    (hq : 2<Q) (hd : d ∣ Q) (hD : 0<D) (hp : 0<p) (ht : 0<t) (hw : 0<w)
    (hx : (p:ℝ)/t ≤ a) (hrect : b^2+H^2 ≤ (((v:ℝ)/w)*((p:ℝ)/t))^2)
    (hR : ∀ r : Fin Q, weightAt Q r.val ≤ R)
    (htable : Table M D p t u) (hstrict : v*mass Q M R u < w*D) : Covers d a b H := by
  let x := (p:ℝ)/t
  have hxp : 0<x := div_pos (by exact_mod_cast hp) (by exact_mod_cast ht)
  refine ⟨Q,M,R,x,(v:ℝ)/w,hq,hd,hxp,hx,by positivity,hrect,hR,?_⟩
  have val (k : ℕ) (hk : k ≤ M) :
      ((u (k+1)-1:ℕ):ℝ) ≤ (D:ℝ)*((k:ℝ)+1)^(-x) ∧
      (D:ℝ)*((k:ℝ)+1)^(-x) ≤ (u (k+1):ℝ) := by
    obtain ⟨_,l,h,_⟩ := htable ⟨k,by omega⟩
    simpa only [Nat.cast_add,Nat.cast_one] using bracket D p t (k+1) (u (k+1))
      (by omega) ht l h
  have term (k : ℕ) (hk : k ∈ Finset.range M) :
      (D:ℝ)*((weight Q (k+1):ℝ)*(((k:ℝ)+1)^(-x)-((k:ℝ)+2)^(-x))) ≤
      ((weight Q (k+1)*(u (k+1)-(u (k+2)-1)):ℕ):ℝ) := by
    have hk' := Finset.mem_range.mp hk
    have mono := (htable ⟨k,by omega⟩).2.2.2
    change u (k+2) ≤ u (k+1) at mono
    have hsub : u (k+2)-1 ≤ u (k+1) := (Nat.sub_le _ _).trans mono
    rw [Nat.cast_mul,Nat.cast_sub hsub]
    have l := (val (k+1) (by omega)).1
    simp only [Nat.cast_add,Nat.cast_one] at l
    rw [show (k:ℝ)+1+1=(k:ℝ)+2 by ring] at l
    have hi := (val k (by omega)).2
    have bound := mul_le_mul_of_nonneg_left (sub_le_sub hi l) (Nat.cast_nonneg (α:=ℝ) (weight Q (k+1)))
    linarith only [bound]
  have all : (D:ℝ)*error Q M R x ≤ (mass Q M R u:ℝ) := by
    dsimp [error,mass]
    rw [mul_add,Finset.mul_sum,Nat.cast_add,Nat.cast_sum,Nat.cast_mul]
    apply add_le_add (Finset.sum_le_sum term)
    have bnd := mul_le_mul_of_nonneg_left (val M le_rfl).2 (Nat.cast_nonneg (α:=ℝ) R)
    linarith only [bnd]
  have strict : (v:ℝ)*(mass Q M R u:ℝ) < (w:ℝ)*(D:ℝ) := by exact_mod_cast hstrict
  have product := (mul_le_mul_of_nonneg_left all (Nat.cast_nonneg (α:=ℝ) v)).trans_lt strict
  have ordered : ((v:ℝ)*error Q M R x)*(D:ℝ) < (w:ℝ)*(D:ℝ) := by linarith only [product]
  have lt := (mul_lt_mul_iff_left₀ (show 0 < (D:ℝ) by exact_mod_cast hD)).1 ordered
  rw [div_mul_eq_mul_div,(div_lt_one (show 0 < (w:ℝ) by exact_mod_cast hw))]
  exact lt
