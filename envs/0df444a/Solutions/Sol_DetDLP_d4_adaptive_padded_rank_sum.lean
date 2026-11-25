-- Prove2me | solution 1 for DetDLP.d4_adaptive_padded_rank_sum
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T06:34:49.649877+00:00
-- url     : https://prove2.me/submissions/da78db9b-e4cd-4df2-b18c-a7d387dfbe19

import Mathlib
import Definitions.Def_DetDLP_D4RankCode
set_option autoImplicit false
open DetDLP.D4RankCode Tree
private theorem pad {R : Type} [AddCommMonoid R] {n m : ℕ} (hn : n ≤ m) (g : Fin n → R) :
    (∑ j : Fin m, if h : j.val<n then g ⟨j.val,h⟩ else 0) = ∑ i, g i := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Fin.sum_univ_add]; simp [Fin.castAdd,Fin.natAdd]

theorem solution {α R : Type} [AddCommMonoid R] (t : DetDLP.D4RankCode.Tree α) (v : α → R) (b : ℕ) (h : Fits t b) :
    (∑ j : Fin (2^b), ((read t b j.val).map v).getD 0) = total v t := by
  classical
  induction t generalizing b with
  | leaf a =>
    let z : Fin (2^b) := ⟨0,by positivity⟩
    rw [Finset.sum_eq_single z]
    · simp [DetDLP.D4RankCode.Tree.read,total,z]
    · intro j _ hj; have hz : j.val ≠ 0 := fun e => hj (Fin.ext e); simp [DetDLP.D4RankCode.Tree.read,hz]
    · simp
  | choice n f ih =>
    obtain ⟨hle,hs⟩ := h
    let w := Nat.clog 2 n
    let lo := 2^w
    let hi := 2^(b-w)
    have cap : hi*lo=2^b := by dsimp [hi,lo,w]; rw [← pow_add,Nat.sub_add_cancel hle]
    let e : Fin hi × Fin lo ≃ Fin (2^b) := finProdFinEquiv.trans (finCongr cap)
    let term (u : Fin hi) (i : Fin n) := ((read (f i) (b-w) u.val).map v).getD 0
    trans ∑ p : Fin hi × Fin lo, if h : p.2.val<n then term p.1 ⟨p.2.val,h⟩ else 0
    · symm; apply Fintype.sum_equiv e; intro ⟨u,j⟩
      have hv : (e (u,j)).val = j.val+lo*u.val := rfl
      have hp : 0<lo := by dsimp [lo]; positivity
      simp only [DetDLP.D4RankCode.Tree.read,if_pos hle,hv]
      change _ = ((if h : (j.val+lo*u.val)%lo<n then read (f ⟨_,h⟩) (b-w) ((j.val+lo*u.val)/lo) else none).map v).getD 0
      simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt j.isLt,Nat.add_mul_div_left _ _ hp,Nat.div_eq_of_lt j.isLt,zero_add]
      split <;> rfl
    · rw [Fintype.sum_prod_type]
      change (∑ u : Fin hi, ∑ j : Fin lo, if h : j.val<n then term u ⟨j.val,h⟩ else 0) = _
      have bound : n ≤ lo := Nat.le_pow_clog (by decide) n
      simp_rw [pad bound]; rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => ih i _ (hs i))
