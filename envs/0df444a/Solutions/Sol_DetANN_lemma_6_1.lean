-- Prove2me | solution 1 for DetANN.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-14T09:53:31.133894+00:00
-- url     : https://prove2.me/submissions/6490b5fb-82dc-4d68-b95e-cf9f2431bb5c

import Mathlib
import Definitions.Def_DetANN_SignedBlocks

open DetANN Finset
open scoped Nat

namespace DetANNL61Aux

variable {R : Type} [Fintype R] [DecidableEq R]

/-- Uniform average over all sign vectors `σ : R → Bool`. -/
noncomputable def avg (f : (R → Bool) → ℝ) : ℝ :=
  (Fintype.card (R → Bool) : ℝ)⁻¹ * ∑ σ, f σ

lemma card_pos' : (0 : ℝ) < Fintype.card (R → Bool) := by
  exact_mod_cast Fintype.card_pos

lemma avg_const (c : ℝ) : avg (R := R) (fun _ => c) = c := by
  unfold avg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ card_pos'.ne', one_mul]

lemma avg_add (f g : (R → Bool) → ℝ) : avg (fun σ => f σ + g σ) = avg f + avg g := by
  unfold avg; rw [Finset.sum_add_distrib, mul_add]

lemma avg_sub (f g : (R → Bool) → ℝ) : avg (fun σ => f σ - g σ) = avg f - avg g := by
  unfold avg; rw [Finset.sum_sub_distrib, mul_sub]

lemma avg_smul (c : ℝ) (f : (R → Bool) → ℝ) : avg (fun σ => c * f σ) = c * avg f := by
  unfold avg; rw [← Finset.mul_sum]; ring

lemma avg_sum {ι : Type*} (s : Finset ι) (f : ι → (R → Bool) → ℝ) :
    avg (fun σ => ∑ i ∈ s, f i σ) = ∑ i ∈ s, avg (f i) := by
  unfold avg; rw [Finset.sum_comm, Finset.mul_sum]

lemma avg_mono {f g : (R → Bool) → ℝ} (h : ∀ σ, f σ ≤ g σ) : avg f ≤ avg g := by
  unfold avg
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => h σ) (inv_nonneg.2 card_pos'.le)

lemma signOf_sq (b : Bool) : signOf b ^ 2 = 1 := by cases b <;> simp [signOf]

lemma abs_signOf (b : Bool) : |signOf b| = 1 := by cases b <;> simp [signOf]

lemma sum_signOf_pow (k : ℕ) : ∑ b : Bool, signOf b ^ k = if Even k then 2 else 0 := by
  rw [Fintype.sum_bool]
  simp only [signOf, if_true, Bool.false_eq_true, if_false, one_pow]
  rcases Nat.even_or_odd k with h | h
  · rw [h.neg_one_pow, if_pos h]; norm_num
  · rw [h.neg_one_pow, if_neg (Nat.not_even_iff_odd.mpr h)]; norm_num

/-! ### Step A -/

/-- **Step A.** The average of `∏_r σ_r^{k_r}` is `1` if every `k_r` is even and `0` otherwise. -/
theorem avg_prod_signOf_pow (k : R → ℕ) :
    avg (fun σ => ∏ r, signOf (σ r) ^ k r) = if ∀ r, Even (k r) then 1 else 0 := by
  unfold avg
  have h : ∑ σ : R → Bool, ∏ r, signOf (σ r) ^ k r = ∏ r, ∑ b : Bool, signOf b ^ k r :=
    (Fintype.prod_sum (fun r b => signOf b ^ k r)).symm
  rw [h]
  simp_rw [sum_signOf_pow]
  split_ifs with hall
  · rw [Finset.prod_congr rfl (fun r _ => if_pos (hall r)), Finset.prod_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool]
    push_cast
    exact inv_mul_cancel₀ (by positivity)
  · push_neg at hall
    obtain ⟨r, hr⟩ := hall
    rw [Finset.prod_eq_zero (Finset.mem_univ r) (if_neg hr), mul_zero]

/-! ### Step B -/

/-- The Rademacher sum `Y = ∑_r a_r σ_r`. -/
noncomputable def Ysum (a : R → ℝ) (σ : R → Bool) : ℝ := ∑ r, a r * signOf (σ r)

/-- Exact moments: `E Y^n = ∑_{k ⊢ n, all k_r even} multinomial(k) ∏ a_r^{k_r}`. -/
theorem avg_Ysum_pow_eq (a : R → ℝ) (n : ℕ) :
    avg (fun σ => Ysum a σ ^ n) =
      ∑ k ∈ piAntidiag univ n,
        if ∀ r, Even (k r) then (Nat.multinomial univ k : ℝ) * ∏ r, a r ^ k r else 0 := by
  unfold Ysum
  simp_rw [sum_pow_eq_sum_piAntidiag, mul_pow, Finset.prod_mul_distrib]
  rw [avg_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : (fun σ : R → Bool => (Nat.multinomial univ k : ℝ) *
      ((∏ r, a r ^ k r) * ∏ r, signOf (σ r) ^ k r)) =
      fun σ => ((Nat.multinomial univ k : ℝ) * ∏ r, a r ^ k r) * ∏ r, signOf (σ r) ^ k r := by
    funext σ; ring
  rw [e, avg_smul, avg_prod_signOf_pow]
  split_ifs <;> simp

/-- `multinomial(2j) ≤ (2q)^q · multinomial(j)` when `∑ j = q`. -/
lemma multinomial_two_mul_le (j : R → ℕ) (q : ℕ) (hj : ∑ r, j r = q) :
    Nat.multinomial univ (fun r => 2 * j r) ≤ (2 * q) ^ q * Nat.multinomial univ j := by
  have h2 := Nat.multinomial_spec univ (fun r => 2 * j r)
  have h1 := Nat.multinomial_spec univ j
  rw [← Finset.mul_sum, hj] at h2
  rw [hj] at h1
  -- (2q)! = q! · (2q)↓q ≤ q! · (2q)^q
  have hfac : (2 * q)! ≤ q ! * (2 * q) ^ q := by
    have := Nat.factorial_mul_descFactorial (n := 2 * q) (k := q) (by omega)
    rw [show 2 * q - q = q by omega] at this
    rw [← this]
    exact Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)
  -- ∏ j_r! ≤ ∏ (2 j_r)!
  have hprod : ∏ r, (j r)! ≤ ∏ r, (2 * j r)! :=
    Finset.prod_le_prod' fun r _ => Nat.factorial_le (by omega)
  have hpos : 0 < ∏ r, (j r)! := Finset.prod_pos fun r _ => Nat.factorial_pos _
  have key : (∏ r, (j r)!) * Nat.multinomial univ (fun r => 2 * j r) ≤
      (∏ r, (j r)!) * ((2 * q) ^ q * Nat.multinomial univ j) := by
    calc (∏ r, (j r)!) * Nat.multinomial univ (fun r => 2 * j r)
        ≤ (∏ r, (2 * j r)!) * Nat.multinomial univ (fun r => 2 * j r) :=
          Nat.mul_le_mul_right _ hprod
      _ = (2 * q)! := h2
      _ ≤ q ! * (2 * q) ^ q := hfac
      _ = (∏ r, (j r)!) * ((2 * q) ^ q * Nat.multinomial univ j) := by rw [← h1]; ring
  exact Nat.le_of_mul_le_mul_left key hpos

/-- **Step B.** `E Y^{2q} ≤ (2q)^q v^q`, `v = ∑ a_r²`. -/
theorem avg_Ysum_pow_two_mul_le (a : R → ℝ) (q : ℕ) :
    avg (fun σ => Ysum a σ ^ (2 * q)) ≤ ((2 * q : ℕ) : ℝ) ^ q * (∑ r, a r ^ 2) ^ q := by
  rw [avg_Ysum_pow_eq, sum_pow_eq_sum_piAntidiag, Finset.mul_sum, ← Finset.sum_filter]
  -- reindex the even compositions of 2q by compositions of q
  have hre : ∑ k ∈ (piAntidiag univ (2 * q)).filter (fun k : R → ℕ => ∀ r, Even (k r)),
      (Nat.multinomial univ k : ℝ) * ∏ r, a r ^ k r =
      ∑ j ∈ piAntidiag univ q,
        (Nat.multinomial univ (fun r => 2 * j r) : ℝ) * ∏ r, a r ^ (2 * j r) := by
    refine Finset.sum_nbij' (fun k r => k r / 2) (fun j r => 2 * j r) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, mem_piAntidiag] at hk ⊢
      obtain ⟨⟨hs, -⟩, hev⟩ := hk
      refine ⟨?_, fun _ _ => Finset.mem_univ _⟩
      have : ∑ r, k r = ∑ r, 2 * (k r / 2) :=
        Finset.sum_congr rfl fun r _ => (Nat.two_mul_div_two_of_even (hev r)).symm
      rw [← Finset.mul_sum] at this
      have hs' : ∑ r, k r = 2 * q := hs
      omega
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, mem_piAntidiag] at hj ⊢
      refine ⟨⟨?_, fun _ _ => Finset.mem_univ _⟩, fun r => even_two_mul _⟩
      rw [← Finset.mul_sum, hj.1]
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter] at hk
      funext r; exact Nat.two_mul_div_two_of_even (hk.2 r)
    · intro j _
      funext r; simp
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter] at hk
      have e' : ∀ r, 2 * (k r / 2) = k r := fun r => Nat.two_mul_div_two_of_even (hk.2 r)
      simp only [e']
  rw [hre]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjq : ∑ r, j r = q := (mem_piAntidiag.1 hj).1
  have hm := multinomial_two_mul_le j q hjq
  have hprod : ∏ r, a r ^ (2 * j r) = ∏ r, (a r ^ 2) ^ j r :=
    Finset.prod_congr rfl fun r _ => by rw [pow_mul]
  rw [hprod]
  have hnn : 0 ≤ ∏ r, (a r ^ 2) ^ j r := Finset.prod_nonneg fun r _ => by positivity
  calc (Nat.multinomial univ (fun r => 2 * j r) : ℝ) * ∏ r, (a r ^ 2) ^ j r
      ≤ ((2 * q) ^ q * Nat.multinomial univ j : ℕ) * ∏ r, (a r ^ 2) ^ j r :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hnn
    _ = ((2 * q : ℕ) : ℝ) ^ q * ((Nat.multinomial univ j : ℝ) * ∏ r, (a r ^ 2) ^ j r) := by
        push_cast; ring

/-- Flipping one sign is a bijection of the sign cube, so averages are invariant under it. -/
lemma avg_flip (r : R) (f : (R → Bool) → ℝ) :
    avg f = avg (fun σ => f (Function.update σ r (!(σ r)))) := by
  unfold avg
  congr 1
  let e : (R → Bool) ≃ (R → Bool) :=
    { toFun := fun σ => Function.update σ r (!(σ r))
      invFun := fun σ => Function.update σ r (!(σ r))
      left_inv := fun σ => by funext t; by_cases h : t = r <;> simp [Function.update, h]
      right_inv := fun σ => by funext t; by_cases h : t = r <;> simp [Function.update, h] }
  exact (e.sum_comp f).symm

lemma signOf_not (b : Bool) : signOf (!b) = -signOf b := by cases b <;> simp [signOf]

/-- `E[σ_r σ_t] = [r = t]`. -/
lemma avg_signOf_mul (r t : R) :
    avg (fun σ => signOf (σ r) * signOf (σ t)) = if r = t then 1 else 0 := by
  split_ifs with h
  · subst h
    have : (fun σ : R → Bool => signOf (σ r) * signOf (σ r)) = fun _ => 1 := by
      funext σ; rw [← sq, signOf_sq]
    rw [this, avg_const]
  · have hflip := avg_flip r (fun σ => signOf (σ r) * signOf (σ t))
    have e : (fun σ : R → Bool => signOf (Function.update σ r (!(σ r)) r) *
        signOf (Function.update σ r (!(σ r)) t)) = fun σ => -(signOf (σ r) * signOf (σ t)) := by
      funext σ
      rw [Function.update_self, Function.update_of_ne (Ne.symm h), signOf_not]; ring
    rw [e] at hflip
    have hneg : avg (R := R) (fun σ => -(signOf (σ r) * signOf (σ t))) =
        -avg (fun σ => signOf (σ r) * signOf (σ t)) := by
      have := avg_smul (R := R) (-1) (fun σ => signOf (σ r) * signOf (σ t))
      simpa using this
    rw [hneg] at hflip
    linarith

/-- `E Y² = v`. -/
theorem avg_Ysum_sq (a : R → ℝ) : avg (fun σ => Ysum a σ ^ 2) = ∑ r, a r ^ 2 := by
  have e : (fun σ : R → Bool => Ysum a σ ^ 2) =
      fun σ => ∑ r, ∑ t, (a r * a t) * (signOf (σ r) * signOf (σ t)) := by
    funext σ
    unfold Ysum
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => by ring
  rw [e, avg_sum]
  simp_rw [avg_sum, avg_smul, avg_signOf_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun r _ => by ring

/-! ### Step C -/

/-- `X = Y² − v`. -/
noncomputable def Xc (a : R → ℝ) (σ : R → Bool) : ℝ := Ysum a σ ^ 2 - ∑ r, a r ^ 2

/-- **Step C, first part.** `E X = 0`. -/
theorem avg_Xc (a : R → ℝ) : avg (Xc a) = 0 := by
  unfold Xc
  rw [avg_sub, avg_Ysum_sq, avg_const, sub_self]

lemma add_pow_le_two_pow (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (m : ℕ) :
    (x + y) ^ m ≤ 2 ^ m * (x ^ m + y ^ m) := by
  rcases le_total x y with h | h
  · calc (x + y) ^ m ≤ (2 * y) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * y ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (x ^ m + y ^ m) := by gcongr; linarith [pow_nonneg hx m]
  · calc (x + y) ^ m ≤ (2 * x) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * x ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (x ^ m + y ^ m) := by gcongr; linarith [pow_nonneg hy m]

/-- **Step C, second part.** `E |X|^m ≤ (8m)^m v^m` for `m ≥ 1`. -/
theorem avg_abs_Xc_pow_le (a : R → ℝ) (m : ℕ) (hm : 1 ≤ m) :
    avg (fun σ => |Xc a σ| ^ m) ≤ ((8 * m : ℕ) : ℝ) ^ m * (∑ r, a r ^ 2) ^ m := by
  set v := ∑ r, a r ^ 2
  have hv : 0 ≤ v := Finset.sum_nonneg fun r _ => sq_nonneg _
  -- pointwise: |X|^m ≤ 2^m (Y^{2m} + v^m)
  have hpt : ∀ σ, |Xc a σ| ^ m ≤ 2 ^ m * (Ysum a σ ^ (2 * m) + v ^ m) := by
    intro σ
    have habs : |Xc a σ| ≤ Ysum a σ ^ 2 + v := by
      unfold Xc
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (Ysum a σ)]
    calc |Xc a σ| ^ m ≤ (Ysum a σ ^ 2 + v) ^ m := pow_le_pow_left₀ (abs_nonneg _) habs m
      _ ≤ 2 ^ m * ((Ysum a σ ^ 2) ^ m + v ^ m) := add_pow_le_two_pow _ _ (sq_nonneg _) hv m
      _ = 2 ^ m * (Ysum a σ ^ (2 * m) + v ^ m) := by rw [← pow_mul]
  have hB := avg_Ysum_pow_two_mul_le a m
  calc avg (fun σ => |Xc a σ| ^ m)
      ≤ avg (fun σ => 2 ^ m * (Ysum a σ ^ (2 * m) + v ^ m)) := avg_mono hpt
    _ = 2 ^ m * (avg (fun σ => Ysum a σ ^ (2 * m)) + v ^ m) := by
        rw [avg_smul, avg_add, avg_const]
    _ ≤ 2 ^ m * (((2 * m : ℕ) : ℝ) ^ m * v ^ m + v ^ m) := by gcongr
    _ ≤ ((8 * m : ℕ) : ℝ) ^ m * v ^ m := by
        set A : ℝ := ((2 * m : ℕ) : ℝ) ^ m
        have h1 : (1 : ℝ) ≤ A := one_le_pow₀ (by
          have : (1 : ℝ) ≤ m := by exact_mod_cast hm
          push_cast; linarith)
        have hvm : 0 ≤ v ^ m := pow_nonneg hv m
        have e : ((8 * m : ℕ) : ℝ) ^ m = 4 ^ m * A := by
          simp only [A]; push_cast; rw [← mul_pow]; ring_nf
        have h4 : (2 : ℝ) * 2 ^ m ≤ 4 ^ m := by
          have : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
          rw [this]
          exact mul_le_mul_of_nonneg_right (by
            calc (2 : ℝ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm) (by positivity)
        rw [e]
        calc (2 : ℝ) ^ m * (A * v ^ m + v ^ m) ≤ 2 ^ m * (2 * A * v ^ m) := by
              gcongr; nlinarith
          _ = (2 * 2 ^ m) * A * v ^ m := by ring
          _ ≤ 4 ^ m * A * v ^ m := by gcongr
          _ = 4 ^ m * A * v ^ m := rfl

end DetANNL61Aux

namespace DetANNL61Aux

variable {R : Type} [Fintype R] [DecidableEq R]

/-- Uniform average over `L` independent rows of signs. -/
noncomputable def avgL (L : ℕ) (F : (Fin L → R → Bool) → ℝ) : ℝ :=
  (Fintype.card (Fin L → R → Bool) : ℝ)⁻¹ * ∑ σ, F σ

lemma avgL_zero (F : (Fin 0 → R → Bool) → ℝ) : avgL 0 F = F Fin.elim0 := by
  unfold avgL
  have : (Finset.univ : Finset (Fin 0 → R → Bool)) = {Fin.elim0} := by
    ext σ; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]; funext i; exact i.elim0
  rw [this, Finset.sum_singleton]; simp

/-- **Step D.** Split off the first row. -/
lemma avgL_succ (L : ℕ) (F : (Fin (L + 1) → R → Bool) → ℝ) :
    avgL (L + 1) F = avg (fun τ => avgL L (fun σ => F (Fin.cons τ σ))) := by
  unfold avgL avg
  rw [← (Fin.consEquiv fun _ : Fin (L + 1) => R → Bool).sum_comp, Fintype.sum_prod_type]
  have hc : (Fintype.card (Fin (L + 1) → R → Bool) : ℝ) =
      (Fintype.card (R → Bool) : ℝ) * Fintype.card (Fin L → R → Bool) := by
    simp only [Fintype.card_fun, Fintype.card_fin]; push_cast; ring
  rw [hc, mul_inv, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [mul_assoc]; rfl

lemma avgL_mul_split (L : ℕ) (f : (R → Bool) → ℝ) (g : (Fin L → R → Bool) → ℝ) :
    avgL (L + 1) (fun σ => f (σ 0) * g (Fin.tail σ)) = avg f * avgL L g := by
  rw [avgL_succ]
  simp only [Fin.cons_zero, Fin.tail_cons]
  have : ∀ τ, avgL L (fun σ => f τ * g σ) = f τ * avgL L g := by
    intro τ; unfold avgL; rw [← Finset.mul_sum]; ring
  simp_rw [this]
  unfold avg
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun σ _ => by ring

lemma avgL_sum (L : ℕ) {ι : Type*} (s : Finset ι) (F : ι → (Fin L → R → Bool) → ℝ) :
    avgL L (fun σ => ∑ i ∈ s, F i σ) = ∑ i ∈ s, avgL L (F i) := by
  unfold avgL; rw [Finset.sum_comm, Finset.mul_sum]

lemma avgL_smul (L : ℕ) (c : ℝ) (F : (Fin L → R → Bool) → ℝ) :
    avgL L (fun σ => c * F σ) = c * avgL L F := by
  unfold avgL; rw [← Finset.mul_sum]; ring

lemma abs_avg_le (f : (R → Bool) → ℝ) : |avg f| ≤ avg (fun σ => |f σ|) := by
  unfold avg
  rw [abs_mul, abs_of_nonneg (inv_nonneg.2 card_pos'.le)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.2 card_pos'.le)

/-- The row sum `S_L = ∑_ℓ X(σ_ℓ)`. -/
noncomputable def Ssum (a : R → ℝ) (L : ℕ) (σ : Fin L → R → Bool) : ℝ := ∑ ℓ, Xc a (σ ℓ)

/-- Moments of `S_L`. -/
noncomputable def Mom (a : R → ℝ) (L n : ℕ) : ℝ := avgL L (fun σ => Ssum a L σ ^ n)

/-- Moments of one `X`. -/
noncomputable def mu (a : R → ℝ) (j : ℕ) : ℝ := avg (fun τ => Xc a τ ^ j)

/-- The recursion over rows: `E S_{L+1}^n = ∑_j C(n,j) E X^j E S_L^{n-j}`. -/
lemma Mom_succ (a : R → ℝ) (L n : ℕ) :
    Mom a (L + 1) n = ∑ j ∈ range (n + 1), (n.choose j : ℝ) * mu a j * Mom a L (n - j) := by
  unfold Mom
  have e : (fun σ : Fin (L + 1) → R → Bool => Ssum a (L + 1) σ ^ n) =
      fun σ => ∑ j ∈ range (n + 1),
        (n.choose j : ℝ) * (Xc a (σ 0) ^ j * Ssum a L (Fin.tail σ) ^ (n - j)) := by
    funext σ
    have hs : Ssum a (L + 1) σ = Xc a (σ 0) + Ssum a L (Fin.tail σ) := by
      unfold Ssum; rw [Fin.sum_univ_succ]; rfl
    rw [hs, add_pow]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [e, avgL_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsplit := avgL_mul_split L (fun τ => Xc a τ ^ j) (fun σ => Ssum a L σ ^ (n - j))
  rw [avgL_smul, hsplit]
  unfold mu; ring

/-- `|E X^j| ≤ j! cʲ` with `c = 8e·v` (and `E X = 0`). -/
lemma abs_mu_le (a : R → ℝ) (j : ℕ) (hj : j ≠ 1) :
    |mu a j| ≤ (j ! : ℝ) * (8 * Real.exp 1 * ∑ r, a r ^ 2) ^ j := by
  set v := ∑ r, a r ^ 2
  have hv : 0 ≤ v := Finset.sum_nonneg fun r _ => sq_nonneg _
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0; unfold mu; simp [avg_const]
  have hj2 : 1 ≤ j := hpos
  calc |mu a j| ≤ avg (fun τ => |Xc a τ ^ j|) := abs_avg_le _
    _ = avg (fun τ => |Xc a τ| ^ j) := by simp_rw [abs_pow]
    _ ≤ ((8 * j : ℕ) : ℝ) ^ j * v ^ j := avg_abs_Xc_pow_le a j hj2
    _ ≤ (j ! : ℝ) * (8 * Real.exp 1 * v) ^ j := by
        have hjj : (j : ℝ) ^ j ≤ j ! * Real.exp 1 ^ j := by
          have := Real.pow_div_factorial_le_exp (x := (j : ℝ)) (Nat.cast_nonneg j) j
          rw [div_le_iff₀ (by exact_mod_cast Nat.factorial_pos j)] at this
          rw [← Real.exp_nat_mul, mul_one]; linarith
        push_cast
        rw [mul_pow, mul_pow, mul_pow]
        have h8 : (0 : ℝ) ≤ 8 ^ j := by positivity
        have hvj : (0 : ℝ) ≤ v ^ j := pow_nonneg hv j
        calc (8 : ℝ) ^ j * (j : ℝ) ^ j * v ^ j ≤ 8 ^ j * (j ! * Real.exp 1 ^ j) * v ^ j := by gcongr
          _ = (j ! : ℝ) * (8 ^ j * Real.exp 1 ^ j * v ^ j) := by ring

/-- The majorant `Q_L(n) = 2ⁿ C(L + ⌊n/2⌋, L)`. -/
noncomputable def Qm (L n : ℕ) : ℝ := (2 : ℝ) ^ n * ((L + n / 2).choose L : ℝ)

lemma Qm_nonneg (L n : ℕ) : 0 ≤ Qm L n := by unfold Qm; positivity

/-- The majorant is preserved: `Q_L(n) + ∑_{j=2}^{n} Q_L(n-j) ≤ Q_{L+1}(n)`. -/
lemma Qm_step (L n : ℕ) :
    ∑ j ∈ (range (n + 1)).erase 1, Qm L (n - j) ≤ Qm (L + 1) n := by
  set h := n / 2 with hdef
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- n ≤ 1: only j = 0 survives
    have hset : (range (n + 1)).erase 1 = {0} := by
      ext j; simp only [mem_erase, mem_range, mem_singleton]; omega
    rw [hset, Finset.sum_singleton, Nat.sub_zero]
    unfold Qm
    have : h = 0 := by omega
    simp [h, this]
  · have hh : 1 ≤ h := by omega
    -- split off j = 0
    have hsplit : (range (n + 1)).erase 1 = insert 0 ((range (n + 1)).filter (fun j => 2 ≤ j)) := by
      ext j; simp only [mem_erase, mem_range, mem_insert, mem_filter]; omega
    rw [hsplit, Finset.sum_insert (by simp), Nat.sub_zero]
    -- each remaining term is ≤ 2^{n-j} C(L + h - 1, L)
    have hterm : ∀ j ∈ (range (n + 1)).filter (fun j => 2 ≤ j),
        Qm L (n - j) ≤ (2 : ℝ) ^ (n - j) * ((L + (h - 1)).choose L : ℝ) := by
      intro j hj
      simp only [mem_filter, mem_range] at hj
      unfold Qm
      gcongr
      omega
    have hgeo : ∑ j ∈ (range (n + 1)).filter (fun j => 2 ≤ j), (2 : ℝ) ^ (n - j) ≤ 2 ^ (n - 1) := by
      -- reindex by i = n - j ∈ [0, n-2]
      have : ∑ j ∈ (range (n + 1)).filter (fun j => 2 ≤ j), (2 : ℝ) ^ (n - j) =
          ∑ i ∈ range (n - 1), (2 : ℝ) ^ i := by
        refine Finset.sum_nbij' (fun j => n - j) (fun i => n - i) ?_ ?_ ?_ ?_ ?_
        · intro j hj; simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢; omega
        · intro i hi; simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢; omega
        · intro j hj; simp only [Finset.mem_filter, Finset.mem_range] at hj; omega
        · intro i hi; simp only [Finset.mem_range] at hi; omega
        · intro j _; rfl
      rw [this]
      have hg := geom_sum_eq (x := (2 : ℝ)) (by norm_num) (n - 1)
      rw [hg]; norm_num
    have hpascal : ((L + (h - 1)).choose L : ℝ) ≤ ((L + h).choose (L + 1) : ℝ) := by
      have e1 : L + h = (L + (h - 1)) + 1 := by omega
      rw [e1, Nat.choose_succ_succ']
      push_cast; linarith [(Nat.cast_nonneg ((L + (h - 1)).choose (L + 1)) : (0 : ℝ) ≤ _)]
    have hnext : (((L + 1) + h).choose (L + 1) : ℝ) =
        ((L + h).choose L : ℝ) + ((L + h).choose (L + 1) : ℝ) := by
      have e1 : (L + 1) + h = (L + h) + 1 := by omega
      rw [e1, Nat.choose_succ_succ']; push_cast; ring
    calc Qm L n + ∑ j ∈ (range (n + 1)).filter (fun j => 2 ≤ j), Qm L (n - j)
        ≤ Qm L n + ∑ j ∈ (range (n + 1)).filter (fun j => 2 ≤ j),
            (2 : ℝ) ^ (n - j) * ((L + (h - 1)).choose L : ℝ) := by
          gcongr with j hj; exact hterm j hj
      _ = Qm L n + (∑ j ∈ (range (n + 1)).filter (fun j => 2 ≤ j), (2 : ℝ) ^ (n - j)) *
            ((L + (h - 1)).choose L : ℝ) := by rw [Finset.sum_mul]
      _ ≤ Qm L n + 2 ^ (n - 1) * ((L + (h - 1)).choose L : ℝ) := by gcongr
      _ ≤ Qm L n + 2 ^ n * ((L + h).choose (L + 1) : ℝ) := by
          have h2 : (2 : ℝ) ^ (n - 1) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
          have := mul_le_mul h2 hpascal (Nat.cast_nonneg _) (by positivity)
          linarith
      _ = Qm (L + 1) n := by unfold Qm; rw [hnext]; ring

/-- **Step E, induction.** `|E S_L^n| ≤ n! cⁿ Q_L(n)`. -/
theorem abs_Mom_le (a : R → ℝ) (L n : ℕ) :
    |Mom a L n| ≤ (n ! : ℝ) * (8 * Real.exp 1 * ∑ r, a r ^ 2) ^ n * Qm L n := by
  set c := 8 * Real.exp 1 * ∑ r, a r ^ 2
  have hc : 0 ≤ c := by
    have : 0 ≤ ∑ r, a r ^ 2 := Finset.sum_nonneg fun r _ => sq_nonneg _
    positivity
  induction L generalizing n with
  | zero =>
    unfold Mom
    rw [avgL_zero]
    unfold Ssum
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; unfold Qm; simp
    · rw [zero_pow hpos.ne', abs_zero]
      exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hc n)) (Qm_nonneg 0 n)
  | succ L ih =>
    rw [Mom_succ]
    -- drop j = 1 (E X = 0)
    have hmu1 : mu a 1 = 0 := by unfold mu; simp only [pow_one]; exact avg_Xc a
    calc |∑ j ∈ range (n + 1), (n.choose j : ℝ) * mu a j * Mom a L (n - j)|
        ≤ ∑ j ∈ range (n + 1), |(n.choose j : ℝ) * mu a j * Mom a L (n - j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ (range (n + 1)).erase 1, |(n.choose j : ℝ) * mu a j * Mom a L (n - j)| := by
          rcases Nat.lt_or_ge n 1 with hn | hn
          · rw [Finset.erase_eq_of_notMem (by simp; omega)]
          · rw [← Finset.add_sum_erase _ _ (by simp; omega : 1 ∈ range (n + 1)), hmu1]; simp
      _ ≤ ∑ j ∈ (range (n + 1)).erase 1, (n ! : ℝ) * c ^ n * Qm L (n - j) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj1 : j ≠ 1 := (Finset.mem_erase.1 hj).1
          have hjn : j ≤ n := by have := (Finset.mem_erase.1 hj).2; simp at this; omega
          rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
          have h1 := abs_mu_le a j hj1
          have h2 := ih (n - j)
          calc (n.choose j : ℝ) * |mu a j| * |Mom a L (n - j)|
              ≤ (n.choose j : ℝ) * ((j ! : ℝ) * c ^ j) * (((n - j) ! : ℝ) * c ^ (n - j) *
                  Qm L (n - j)) := by
                gcongr
              _ = ((n.choose j * j ! * (n - j) ! : ℕ) : ℝ) * (c ^ j * c ^ (n - j)) * Qm L (n - j) := by
                push_cast; ring
              _ = (n ! : ℝ) * c ^ n * Qm L (n - j) := by
                rw [Nat.choose_mul_factorial_mul_factorial hjn, ← pow_add, Nat.add_sub_cancel' hjn]
      _ = (n ! : ℝ) * c ^ n * ∑ j ∈ (range (n + 1)).erase 1, Qm L (n - j) := by
          rw [Finset.mul_sum]
      _ ≤ (n ! : ℝ) * c ^ n * Qm (L + 1) n := by
          gcongr; exact Qm_step L n

/-- **Step E, conclusion.** For `1 ≤ p ≤ L`: `E S_L^{2p} ≤ (1024 e² p L)^p v^{2p}`. -/
theorem Mom_two_mul_le (a : R → ℝ) (L p : ℕ) (hpL : p ≤ L) :
    Mom a L (2 * p) ≤ (1024 * Real.exp 1 ^ 2 * p * L) ^ p * (∑ r, a r ^ 2) ^ (2 * p) := by
  set v := ∑ r, a r ^ 2
  have hv : 0 ≤ v := Finset.sum_nonneg fun r _ => sq_nonneg _
  have hb := le_trans (le_abs_self _) (abs_Mom_le a L (2 * p))
  refine hb.trans ?_
  unfold Qm
  rw [show 2 * p / 2 = p by omega]
  -- C(L+p, L) = C(L+p, p) ≤ (L+p)^p / p! ≤ (2L)^p / p!
  have hch : (((L + p).choose L : ℕ) : ℝ) ≤ ((2 * L : ℕ) : ℝ) ^ p / (p ! : ℝ) := by
    rw [show (L + p).choose L = (L + p).choose p from by
      rw [Nat.choose_symm_of_eq_add]; ring]
    calc (((L + p).choose p : ℕ) : ℝ) ≤ ((L + p : ℕ) : ℝ) ^ p / (p ! : ℝ) := Nat.choose_le_pow_div p _
      _ ≤ ((2 * L : ℕ) : ℝ) ^ p / (p ! : ℝ) := by
          gcongr; push_cast; exact_mod_cast (by omega : L + p ≤ 2 * L)
  -- (2p)! ≤ p! (2p)^p
  have hfac : ((2 * p) ! : ℝ) ≤ (p ! : ℝ) * ((2 * p : ℕ) : ℝ) ^ p := by
    have := Nat.factorial_mul_descFactorial (n := 2 * p) (k := p) (by omega)
    rw [show 2 * p - p = p by omega] at this
    rw [← this]; push_cast
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.descFactorial_le_pow _ _) (by positivity)
  have hpf : (0 : ℝ) < p ! := by exact_mod_cast Nat.factorial_pos p
  have hc0 : 0 ≤ 8 * Real.exp 1 * v := by positivity
  calc ((2 * p) ! : ℝ) * (8 * Real.exp 1 * v) ^ (2 * p) * (2 ^ (2 * p) * (((L + p).choose L : ℕ) : ℝ))
      ≤ ((p ! : ℝ) * ((2 * p : ℕ) : ℝ) ^ p) * (8 * Real.exp 1 * v) ^ (2 * p) *
          (2 ^ (2 * p) * (((2 * L : ℕ) : ℝ) ^ p / (p ! : ℝ))) := by gcongr
    _ = ((2 * p : ℕ) : ℝ) ^ p * ((2 * L : ℕ) : ℝ) ^ p * (4 : ℝ) ^ p *
          ((8 * Real.exp 1 * v) ^ 2) ^ p := by
        have h4 : (2 : ℝ) ^ (2 * p) = 4 ^ p := by rw [pow_mul]; norm_num
        rw [← pow_mul, h4]
        field_simp
    _ = (1024 * Real.exp 1 ^ 2 * p * L) ^ p * v ^ (2 * p) := by
        rw [pow_mul v 2 p]
        simp only [← mul_pow]
        congr 1
        push_cast
        ring

end DetANNL61Aux

open DetANNL61Aux in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : Type) [Fintype R] [DecidableEq R] (a : R → ℝ) (L p : ℕ),
      1 ≤ p → p ≤ L →
        (Fintype.card (Fin L → R → Bool) : ℝ)⁻¹ *
            ∑ σ : Fin L → R → Bool,
              (∑ ℓ : Fin L, ((∑ r, a r * signOf (σ ℓ r)) ^ 2 - ∑ r, a r ^ 2)) ^ (2 * p) ≤
          (C * p * L) ^ p * (∑ r, a r ^ 2) ^ (2 * p) := by
  refine ⟨1024 * Real.exp 1 ^ 2, by positivity, ?_⟩
  intro R _ _ a L p _ hpL
  exact Mom_two_mul_le a L p hpL
