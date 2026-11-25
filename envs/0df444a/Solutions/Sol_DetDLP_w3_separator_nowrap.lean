-- Prove2me | solution 1 for DetDLP.w3_separator_nowrap
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T21:29:10.303677+00:00
-- url     : https://prove2.me/submissions/96adf9d5-bd81-4885-afeb-67570215d1de

import Definitions.Def_DetDLP_W3_Separator

set_option autoImplicit false
open DetDLP

private theorem w3_tuple_bound (q : w3_Query) (X : q.FB.BlockTuple) :
    0 ≤ q.FB.tupleLabelSum q.M q.y X ∧ q.FB.tupleLabelSum q.M q.y X ≤ ((2*q.m : ℕ) : ℤ) * ((q.M:ℤ)-1) := by
  classical
  have slots : q.FB.tupleLabelSum q.M q.y X = ∑ i, ∑ k, ((q.y (q.FB.coordOf i (X i k))).val : ℤ) := by
    simp only [IndexedFactorBase.tupleLabelSum, IndexedFactorBase.tupleCnt,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.sum_mul]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _; simp [ite_mul]
  rw [slots]; constructor
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => by positivity
  calc _ ≤ ∑ _i : Fin q.m, ∑ _k : Fin 2, ((q.M:ℤ)-1) := by
              gcongr with i _ k; have := (q.y (q.FB.coordOf i (X i k))).val_lt; omega
       _ = _ := by simp; ring

private theorem w3_filter_bound (w M : ℕ) (d : ℤ)
    (lo : -((w:ℤ)*((M:ℤ)-1)) ≤ d) (hi : d ≤ (w:ℤ)*((M:ℤ)-1)) :
    (filterPoly w M).eval d ≤ ((2*w*M+2 : ℕ) : ℤ) ^ dFilt w := by
  let s := Finset.Icc (-(w:ℤ)) (w:ℤ)
  let u := ((2*w*M+2 : ℕ) : ℤ)
  have hfac (j : ℤ) (hj : j ∈ s) : (d - (1+j*(M:ℤ)))^2 ≤ u^2 := by
    obtain ⟨h1,h2⟩ := Finset.mem_Icc.mp hj
    have H1 := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℤ) M)
    have H2 := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg (α := ℤ) M)
    apply sq_le_sq' <;> dsimp [u] <;> push_cast <;> nlinarith [Nat.cast_nonneg (α := ℤ) w]
  have hcard : 2*s.card = dFilt w := by unfold s dFilt; rw [Int.card_Icc]; omega
  calc (filterPoly w M).eval d = ∏ j ∈ s, (d-(1+j*(M:ℤ)))^2 := by simp [filterPoly,s,Polynomial.eval_prod]
       _ ≤ ∏ _j ∈ s, u^2 := Finset.prod_le_prod (fun _ _ => sq_nonneg _) hfac
       _ = u ^ dFilt w := by rw [Finset.prod_const, ←pow_mul,hcard]

theorem solution (q : w3_Query) (width : ∀ i : Fin q.m, (q.FB.blocks i).length ≤ 2^q.k) :
    w3_mass q < (2 : ℤ)^w3_precision q := by
  classical
  let w := 2*q.m
  let u := 2*w*q.M+2
  let D := dFilt w
  let c := Nat.clog 2 u
  have wc : Fintype.card q.FB.BlockTuple ≤ (2^q.k)^(2*q.m) := by
    change Fintype.card ((i : Fin q.m) → Fin 2 → Fin (q.FB.blocks i).length) ≤ _
    calc _ = ∏ i, (q.FB.blocks i).length ^ 2 := by simp [Fintype.card_pi_const]
         _ ≤ ∏ _i : Fin q.m, (2^q.k)^2 := Finset.prod_le_prod' (fun i _ => Nat.pow_le_pow_left (width i) _)
         _ = _ := by simp [← pow_mul,Nat.mul_assoc]
  have size : (Fintype.card (q.FB.BlockTuple × q.FB.BlockTuple) : ℤ) ≤ (2:ℤ)^(4*q.m*q.k) := by
    have hw := Nat.mul_le_mul wc wc
    rw [← pow_add, ← pow_mul, show q.k*(2*q.m+2*q.m) = 4*q.m*q.k by ring] at hw
    exact_mod_cast (show Fintype.card (q.FB.BlockTuple × q.FB.BlockTuple) ≤ 2^(4*q.m*q.k) by simpa only [Fintype.card_prod] using hw)
  have hu : (u:ℤ) ≤ (2:ℤ)^c := by exact_mod_cast Nat.le_pow_clog (b:=2) (by decide) u
  have bound (t : q.FB.BlockTuple × q.FB.BlockTuple) :
      (if w3_valid q t then (filterPoly w q.M).eval (w3_delta q.FB q.M q.y t.1 t.2) else 0) ≤ (u:ℤ)^D := by
    split_ifs
    · obtain ⟨hx,hx'⟩ := w3_tuple_bound q t.1
      obtain ⟨hy,hy'⟩ := w3_tuple_bound q t.2
      apply w3_filter_bound; all_goals unfold w3_delta; dsimp only [w]; linarith
    · positivity
  calc w3_mass q ≤ ∑ _t : q.FB.BlockTuple × q.FB.BlockTuple, (u:ℤ)^D := Finset.sum_le_sum (fun t _ => bound t)
       _ = (Fintype.card (q.FB.BlockTuple × q.FB.BlockTuple) : ℤ)*(u:ℤ)^D := by simp
       _ ≤ (2:ℤ)^(4*q.m*q.k)*((2:ℤ)^c)^D := mul_le_mul size (pow_le_pow_left₀ (by positivity) hu D) (by positivity) (by positivity)
       _ = (2:ℤ)^(4*q.m*q.k + D*c) := by rw [←pow_mul,←pow_add,Nat.mul_comm c D]
       _ < (2:ℤ)^w3_precision q := by
         apply pow_lt_pow_right₀ (by decide : (1:ℤ)<2)
         change 4*q.m*q.k + D*c < 2 + 4*q.m*q.k + D*c; omega
