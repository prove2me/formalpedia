-- Prove2me | solution 1 for DeMorganApprox.Main.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:26:00.52688+00:00
-- url     : https://prove2.me/submissions/b80bba7d-a24f-40d5-9039-b21439fedff5

import Theorems.Thm_DeMorganApprox_Main_claim_4_1_1

import Definitions.Def_DeMorganApprox_Main_Supplement_Multilinearize



namespace FilterTools

open DeMorganApprox.Main Polynomial Polynomial.Chebyshev

private noncomputable def mass (P : Polynomial ℝ) := P.sum fun _ t => |t|

private lemma mass_nonneg (P : Polynomial ℝ) : 0 ≤ mass P :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private lemma mass_add (P Q : Polynomial ℝ) : mass (P + Q) ≤ mass P + mass Q := by
  let U := P.support ∪ Q.support
  have h (R : Polynomial ℝ) (hR : R.support ⊆ U) :
      mass R = ∑ i ∈ U, |R.coeff i| := sum_eq_of_subset _ (fun _ => abs_zero) hR
  rw [h _ support_add, h _ Finset.subset_union_left, h _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by simpa using abs_add_le (P.coeff i) (Q.coeff i)

private lemma mass_sub (P Q : Polynomial ℝ) : mass (P - Q) ≤ mass P + mass Q := by
  simpa [sub_eq_add_neg, mass, Polynomial.sum] using mass_add P (-Q)

private lemma mass_sum {α : Type} (s : Finset α) (f : α → Polynomial ℝ) :
    mass (∑ i ∈ s, f i) ≤ ∑ i ∈ s, mass (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mass]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (mass_add ..).trans (add_le_add (le_refl _) ih)

private lemma mass_mul (P Q : Polynomial ℝ) : mass (P * Q) ≤ mass P * mass Q := by
  rw [mul_eq_sum_sum]
  refine (mass_sum _ _).trans ?_
  unfold Polynomial.sum
  calc
    _ ≤ _ := Finset.sum_le_sum fun i _ => mass_sum _ _
    _ = _ := by
      have hm (n : ℕ) (a : ℝ) : mass (monomial n a) = |a| := by simp [mass]
      simp only [hm, abs_mul]
      rw [mass, mass, Polynomial.sum_def, Polynomial.sum_def, Finset.sum_mul]
      simp only [Finset.mul_sum]

private lemma mass_C (a : ℝ) : mass (C a) = |a| := by simp [mass]
private lemma mass_one : mass 1 = 1 := by simpa using mass_C 1
private lemma mass_X : mass X = 1 := by simp [mass]

private lemma mass_T_comp (A : Polynomial ℝ) (hA : mass A ≤ 7) (d : ℕ) :
    mass ((T ℝ (d : ℤ)).comp A) ≤ 16 ^ d := by
  induction d using Nat.twoStepInduction with
  | zero => simp [mass_one]
  | one => simpa using hA.trans (by norm_num : (7:ℝ) ≤ 16)
  | more n h₀ h₁ =>
    push_cast
    rw [T_add_two, sub_comp, mul_comp, mul_comp, X_comp]
    have htwo : mass ((2 : Polynomial ℝ).comp A) = 2 := by
      rw [show (2 : Polynomial ℝ) = C (2:ℝ) by exact (map_ofNat (Polynomial.C : ℝ →+* Polynomial ℝ) 2).symm, C_comp, mass_C]; norm_num
    have hmul : mass ((2 : Polynomial ℝ).comp A * A) ≤ 14 :=
      (mass_mul ..).trans (by rw [htwo]; linarith)
    refine (mass_sub ..).trans ((add_le_add ((mass_mul ..).trans
      (mul_le_mul hmul h₁ (mass_nonneg _) (by norm_num))) h₀).trans ?_)
    simp only [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 16) n]


private noncomputable def termT (j : ℕ) : Polynomial ℝ :=
  Polynomial.C ((-1:ℝ)^j) * T ℝ (2*(j:ℤ))

private noncomputable def avgT (d : ℕ) : Polynomial ℝ :=
  Polynomial.C (1/((d:ℝ)+1)) * ∑ j ∈ Finset.range (d+1), termT j

private lemma termT_zero (j : ℕ) : (termT j).eval 0 = 1 := by
  induction j with
  | zero => simp [termT]
  | succ j ih =>
    have h := congrArg (fun p : Polynomial ℝ => p.eval 0) (T_add_two ℝ (2*(j:ℤ)))
    simp only [eval_sub, eval_mul, eval_X, eval_ofNat, mul_zero, zero_mul, zero_sub] at h
    simp only [termT, eval_mul, eval_C] at ih ⊢
    rw [Nat.cast_succ, mul_add, mul_one, h, pow_succ]
    linarith

private lemma avgT_zero (d : ℕ) : (avgT d).eval 0 = 1 := by
  simp [avgT, eval_finsetSum, termT_zero, show (d:ℝ)+1 ≠ 0 by positivity]

private lemma avgT_deg (d : ℕ) : (avgT d).natDegree ≤ 2*d := by
  refine (natDegree_C_mul_le ..).trans (natDegree_sum_le_of_forall_le _ _ (fun i hi => ?_))
  refine (natDegree_C_mul_le ..).trans ?_
  rw [natDegree_T]
  simp only [Int.natAbs_mul, Int.natAbs_natCast, show (2:ℤ).natAbs=2 by decide]
  have hi' := Finset.mem_range.mp hi
  omega

private lemma avgT_mass (d : ℕ) : mass (avgT d) ≤ 16^(2*d) := by
  have hd : 0 < (d:ℝ)+1 := by positivity
  refine (mass_mul ..).trans ?_
  rw [mass_C, abs_of_pos (by positivity : 0 < 1/((d:ℝ)+1))]
  have hsum : mass (∑ j ∈ Finset.range (d+1), termT j) ≤
      ∑ _ ∈ Finset.range (d+1), (16:ℝ)^(2*d) := by
    refine (mass_sum ..).trans (Finset.sum_le_sum fun j hj => ?_)
    have hh := mass_T_comp X (mass_X.le.trans (by norm_num)) (2*j)
    simp only [comp_X, Nat.cast_mul, Nat.cast_ofNat] at hh
    refine (mass_mul ..).trans ?_
    simp only [mass_C, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hh.trans (pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hj; omega))
  have := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 1/((d:ℝ)+1))
  simpa [← mul_assoc, hd.ne'] using this

private lemma termT_abs {x : ℝ} (hx : |x| ≤ 1) (j : ℕ) : |(termT j).eval x| ≤ 1 := by
  simpa [termT, abs_mul] using abs_eval_T_real_le_one (2*(j:ℤ)) hx

private lemma avgT_abs {x : ℝ} (hx : |x| ≤ 1) (d : ℕ) : |(avgT d).eval x| ≤ 1 := by
  have hd : 0 < (d:ℝ)+1 := by positivity
  simp only [avgT, eval_mul, eval_C, eval_finsetSum, abs_mul, abs_of_pos (one_div_pos.mpr hd)]
  rw [one_div, inv_mul_le_iff₀ hd, mul_one]
  exact (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (fun j _ => termT_abs hx j)).trans_eq (by simp))

private lemma avgT_decay {x : ℝ} (hx : |x| ≤ 1) (d : ℕ) : |x*(avgT d).eval x| ≤ 1/((d:ℝ)+1) := by
  let B (d : ℕ) := ∑ j ∈ Finset.range (d+1), (termT j).eval x
  have telescope : ∀ k : ℕ, 2*x*B k = x + (-1:ℝ)^k * (T ℝ (2*(k:ℤ)+1)).eval x := by
    intro k
    induction k with
    | zero => simp [B, termT]; ring
    | succ k ih =>
      have h := congrArg (fun p : Polynomial ℝ => p.eval x) (T_add_two ℝ (2*(k:ℤ)+1))
      simp only [eval_sub, eval_mul, eval_X, eval_ofNat] at h
      have hh : B (k+1) = B k + (termT (k+1)).eval x := Finset.sum_range_succ ..
      rw [hh, mul_add, ih]
      simp only [termT, eval_mul, eval_C, Nat.cast_succ, mul_add, mul_one, pow_succ]
      rw [show 2*(k:ℤ)+2+1 = 2*(k:ℤ)+1+2 by ring, h,
          show 2*(k:ℤ)+1+1=2*(k:ℤ)+2 by ring]
      ring
  have hB : |B d * x| ≤ 1 := by
    have ht' : |x + (-1:ℝ)^d*(T ℝ (2*(d:ℤ)+1)).eval x| ≤ 2 :=
      (abs_add_le ..).trans (by simpa [abs_mul, show (1:ℝ)+1=2 by norm_num] using add_le_add hx (abs_eval_T_real_le_one (2*(d:ℤ)+1) hx))
    rw [← telescope] at ht'
    rw [show 2*x*B d=2*(B d*x) by ring, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at ht'
    linarith
  have hd : 0 < (d:ℝ)+1 := by positivity
  change |x*((Polynomial.C _ * _).eval x)| ≤ _
  simp only [eval_mul, eval_C, eval_finsetSum]
  change |x*(1/((d:ℝ)+1)*B d)| ≤ _
  rw [show x*(1/((d:ℝ)+1)*B d)=1/((d:ℝ)+1)*(B d*x) by ring, abs_mul,
      abs_of_pos (one_div_pos.mpr hd)]
  simpa using mul_le_mul_of_nonneg_left hB (one_div_nonneg.mpr hd.le)
end FilterTools

namespace MatrixTools
open DeMorganApprox.Main Matrix Polynomial
open scoped Matrix.Norms.L2Operator

private noncomputable def en {ι : Type} [Fintype ι] (y : ι → ℝ) := Real.sqrt (∑ i, y i ^ 2)

private lemma en_sq {ι : Type} [Fintype ι] (y : ι → ℝ) :
    en y ^ 2 = ∑ i, y i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private lemma en_mono {ι : Type} [Fintype ι] {v w : ι → ℝ} (hv : ∀ i, 0 ≤ v i)
    (h : ∀ i, v i ≤ w i) : en v ≤ en w :=
  Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => by gcongr <;> first | exact hv i | exact h i)

private lemma en_scale {ι : Type} [Fintype ι] (v : ι → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    en (fun i => c*v i) = c*en v := by
  simp only [en, mul_pow, ← Finset.mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

private lemma en_triangle {ι : Type} [Fintype ι] (v w : ι → ℝ) :
    en (fun i => v i+w i) ≤ en v+en w := by
  have h := norm_add_le (WithLp.toLp 2 v : EuclideanSpace ℝ ι) (WithLp.toLp 2 w)
  simpa [en, EuclideanSpace.norm_eq, Real.norm_eq_abs] using h

private lemma transpose_bound {ι J : Type} [Fintype ι] [Fintype J]
    (V : J → ι → ℝ) (K : ℝ) (hK : 0 ≤ K) (h : AbsNormLE V K) (x : ι → ℝ) :
    en (fun j => ∑ i, |V j i| * x i) ≤ K*en x := by
  let z := fun j => ∑ i, |V j i| * x i
  let u := fun i => ∑ j, |V j i| * z j
  have he : en z ^ 2 = ∑ i, x i*u i := by
    rw [en_sq]
    simp_rw [pow_two]
    conv_lhs => enter [2,j,1]; change ∑ i, |V j i| *x i
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [u, Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc]
  have hcs : ∑ i, x i * u i ≤ en x*en u := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hu : en u ≤ K * en z := h z
  have h0 : 0 ≤ en x := Real.sqrt_nonneg _
  have h1 : 0 ≤ en z := Real.sqrt_nonneg _
  by_cases hz : en z = 0
  · change en z ≤ _
    rw [hz]
    positivity
  · change en z ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hu h0, mul_self_pos.mpr hz]

private lemma en_norm {N : Type} [Fintype N] (y : N → ℝ) :
    en y = ‖(WithLp.toLp 2 y : EuclideanSpace ℝ N)‖ := by
  simp [en, EuclideanSpace.norm_eq, Real.norm_eq_abs]

private lemma en_op {N : Type} [Fintype N] [DecidableEq N] (B : Matrix N N ℝ) (y : N → ℝ) :
    en (B *ᵥ y) ≤ ‖B‖*en y := by
  rw [en_norm, en_norm]
  exact B.l2_opNorm_mulVec (WithLp.toLp 2 y)

private lemma abs_le_en {N : Type} [Fintype N] (y : N → ℝ) (i : N) : |y i| ≤ en y := by
  rw [en_norm]
  exact PiLp.norm_apply_le (WithLp.toLp 2 y : EuclideanSpace ℝ N) i

private lemma filter_op {N : Type} [Fintype N] [DecidableEq N] [Nonempty N]
    (A : Matrix N N ℝ) (hA : IsSelfAdjoint A) (h : ‖A‖ ≤ 1) (p : Polynomial ℝ)
    (c : ℝ) (hc : 0 ≤ c) (hp : ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ c) :
    ‖aeval A p‖ ≤ c := by
  rw [← cfc_polynomial p A hA]
  apply norm_cfc_le hc
  intro x hx
  exact hp x ((spectrum.norm_le_norm_of_mem hx).trans h)

private lemma filter_accept {N : Type} [Fintype N] [DecidableEq N]
    (A : Matrix N N ℝ) (p : Polynomial ℝ) (o : N) (k : N → ℝ)
    (hk : A *ᵥ k = 0) (hk₀ : k o = 1) (he : en (Pi.single o 1 - k) ≤ 1/10)
    (hp : p.eval 0 = 1) (hop : ‖aeval A p‖ ≤ 1) :
    |(aeval A p) o o - 1| ≤ 1/10 := by
  let B := aeval A p
  have hp₀ : p.coeff 0 = 1 := by simpa only [coeff_zero_eq_eval_zero] using hp
  have hBk : B *ᵥ k = k := by
    change (aeval A p) *ᵥ k = k
    conv_lhs => enter [1,2]; rw [← p.divX_mul_X_add]
    simp [hp₀, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hk]
  have hnorm := en_op B (Pi.single o 1 - k)
  have hh := (abs_le_en (B *ᵥ (Pi.single o 1 - k)) o).trans hnorm
  rw [Matrix.mulVec_sub, hBk, Matrix.mulVec_single_one] at hh
  simp only [Pi.sub_apply, hk₀] at hh
  exact hh.trans ((mul_le_mul hop he (Real.sqrt_nonneg _) zero_le_one).trans_eq (one_mul _))

private lemma filter_reject {N : Type} [Fintype N] [DecidableEq N]
    (A : Matrix N N ℝ) (p : Polynomial ℝ) (o : N) (w : N → ℝ) (g : ℝ)
    (hw : A *ᵥ w = Pi.single o 1) (hw' : en w ≤ g)
    (L : ℝ) (hL : 0 ≤ L) (hop : ‖aeval A (p*X)‖ ≤ L) :
    |(aeval A p) o o| ≤ L*g := by
  have hh := (abs_le_en ((aeval A (p*X)) *ᵥ w) o).trans (en_op _ w)
  simp only [map_mul, aeval_X, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_single_one] at hh
  simp only [map_mul, aeval_X] at hop
  exact hh.trans (mul_le_mul hop hw' (Real.sqrt_nonneg _) hL)

private lemma en_abs {N : Type} [Fintype N] (y : N → ℝ) :
    en (fun i => |y i|) = en y := by simp [en]

private lemma en_dot {N : Type} [Fintype N] (x y : N → ℝ) :
    |∑ i, x i*y i| ≤ en x*en y := by
  refine (Finset.abs_sum_le_sum_abs ..).trans ?_
  simpa [abs_mul, en] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => |x i|) (fun i => |y i|)

private lemma block_sq {ι J : Type} [Fintype ι] [Fintype J] (y : Unit ⊕ ι ⊕ J → ℝ) :
    (en y)^2 = (y (.inl ()))^2 + (en (fun i => y (.inr (.inl i))))^2 +
                                     (en (fun j => y (.inr (.inr j))))^2 := by
  simp [en_sq, Fintype.sum_sum_type, add_assoc]

private lemma block_bounds {ι J : Type} [Fintype ι] [Fintype J] (y : Unit ⊕ ι ⊕ J → ℝ) :
    |y (.inl ())| ≤ en y ∧ en (fun i => y (.inr (.inl i))) ≤ en y ∧
      en (fun j => y (.inr (.inr j))) ≤ en y ∧
      en y ≤ |y (.inl ())| + en (fun i => y (.inr (.inl i))) + en (fun j => y (.inr (.inr j))) := by
  let a := en (fun i => y (.inr (.inl i)))
  let b := en (fun j => y (.inr (.inr j)))
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hy : 0 ≤ en y := Real.sqrt_nonneg _
  have hz := abs_nonneg (y (.inl ()))
  have he : (en y)^2 = |y (.inl ())|^2 + a^2 + b^2 := by rw [sq_abs, block_sq]
  refine ⟨abs_le_en y _, ?_, ?_, ?_⟩
  · change a ≤ en y
    nlinarith [sq_nonneg (y (.inl ())),sq_nonneg b, sq_abs (y (.inl ()))]
  · change b ≤ en y
    nlinarith [sq_nonneg (y (.inl ())),sq_nonneg a, sq_abs (y (.inl ()))]
  · change en y ≤ |y (.inl ())| + a + b
    nlinarith [mul_nonneg hz ha, mul_nonneg hz hb, mul_nonneg ha hb]

private lemma label_eval {m : ℕ} (l : Label m) (x : Fin m → Bool) :
    MvPolynomial.eval (boolPoint x) (labelPoly l) = (if l.avail x then 1 else 0) := by
  cases l with
  | always => simp [labelPoly, Label.avail]
  | pos i => cases h : x i <;> simp [labelPoly, boolPoint, Label.avail, h]
  | neg i => cases h : x i <;> simp [labelPoly, boolPoint, Label.avail, h]

private noncomputable def linBlock {ι J : Type} (t : ι → ℝ) (W : J → ι → ℝ) :
    Matrix (Unit ⊕ ι ⊕ J) (Unit ⊕ ι ⊕ J) ℝ := fun a b =>
  match a, b with
  | .inl _, .inr (.inl i) | .inr (.inl i), .inl _ => t i
  | .inr (.inl i), .inr (.inr j) | .inr (.inr j), .inr (.inl i) => W j i
  | _, _ => 0

private lemma evaluate_block {ι J : Type} {m : ℕ} (P : SpanProgram m ι J) (S c : ℝ)
    (x : Fin m → Bool) :
    (scaledSymbolicMatrix P S c).map (MvPolynomial.eval (boolPoint x)) =
      c⁻¹ • linBlock (fun i => P.target i / (10*Real.sqrt S))
        (fun j i => if (P.label j).avail x then P.vec j i else 0) := by
  ext a b
  rcases a with u|(i|j) <;> rcases b with v|(i'|j') <;>
    simp [scaledSymbolicMatrix, symbolicMatrix, Matrix.smul_apply, linBlock, label_eval,
      MvPolynomial.smul_eq_C_mul, mul_ite]

private lemma block_symm {ι J : Type} (t : ι → ℝ) (W : J → ι → ℝ) (c : ℝ) :
    IsSelfAdjoint (c • linBlock t W) := by
  change (c • linBlock t W).conjTranspose = _
  ext a b
  rcases a with u|(i|j) <;> rcases b with v|(i'|j') <;> rfl

private lemma block_norm {ι J : Type} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
    (t : ι → ℝ) (W V : J → ι → ℝ) (K : ℝ) (hK : 0 ≤ K) (hV : AbsNormLE V K)
    (ht : en t ≤ 1) (hW : ∀ j i, |W j i| ≤ |V j i|) :
    ‖linBlock t W‖ ≤ 2+2*K := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) ?_
  intro Y
  let y := WithLp.ofLp Y
  let yI := fun i => y (.inr (.inl i))
  let yJ := fun j => y (.inr (.inr j))
  let z := linBlock t W *ᵥ y
  change ‖(WithLp.toLp 2 z : EuclideanSpace ℝ _)‖ ≤ (2+2*K)*‖(WithLp.toLp 2 y : EuclideanSpace ℝ _)‖
  rw [← en_norm, ← en_norm]
  obtain ⟨ho,hI,hJ,_⟩ := block_bounds y
  change en yI ≤ en y at hI
  change en yJ ≤ en y at hJ
  have bo : |z (.inl ())| ≤ en y := by
    have hform : z (.inl ()) = ∑ i, t i*yI i := by
      simp [z, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, linBlock, yI]
    rw [hform]
    exact (en_dot ..).trans ((mul_le_mul ht hI (Real.sqrt_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hmat {A B : Type} [Fintype A] [Fintype B] (M N : A → B → ℝ)
      (hb : ∀ i j, |M i j| ≤ |N i j|) (x : A → ℝ) :
      en (fun j => ∑ i, M i j*x i) ≤ en (fun j => ∑ i, |N i j| * |x i|) := by
    rw [← en_abs (fun j => ∑ i, M i j*x i)]
    apply en_mono (fun _ => abs_nonneg _)
    intro j
    refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hb i j) (abs_nonneg _)
  have bI : en (fun i => z (.inr (.inl i))) ≤ en y + K*en y := by
    let u := fun i => ∑ j, W j i*yJ j
    have hu : en u ≤ K*en y := by
      refine (hmat W V hW yJ).trans ((hV _).trans ?_)
      change K*en (fun i => |yJ i|) ≤ _
      rw [en_abs]
      exact mul_le_mul_of_nonneg_left hJ hK
    have he : (fun i => z (.inr (.inl i))) = fun i => (y (.inl ()))*t i + u i := by
      funext i
      simp [z, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, linBlock, u, yJ, mul_comm]
    rw [he]
    refine (en_triangle ..).trans (add_le_add ?_ hu)
    have hs : en (fun i => y (.inl ()) * t i) = |y (.inl ())| * en t := by
      rw [← en_abs (fun i => y (.inl ()) * t i)]
      simp only [abs_mul, en_scale _ _ (abs_nonneg _), en_abs]
    rw [hs]
    simpa using mul_le_mul ho ht (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have bJ : en (fun j => z (.inr (.inr j))) ≤ K*en y := by
    have he : (fun j => z (.inr (.inr j))) = fun j => ∑ i, W j i*yI i := by
      funext j
      simp [z, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, linBlock, yI]
    rw [he]
    refine (hmat (fun i j => W j i) (fun i j => V j i) (fun i j => hW j i) yI).trans ?_
    refine (transpose_bound V K hK hV (fun i => |yI i|)).trans ?_
    rw [en_abs]
    exact mul_le_mul_of_nonneg_left hI hK
  have hz := (block_bounds z).2.2.2
  linarith

private lemma eval_contract {m : ℕ} {ι J : Type} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
    (P : SpanProgram m ι J) (S c K : ℝ) (hS : 1 ≤ S) (hK : 0 ≤ K) (hc : 2+2*K ≤ c)
    (ht : sqNorm P.target = 1) (hV : AbsNormLE P.vec K) (x : Fin m → Bool) :
    let A := (scaledSymbolicMatrix P S c).map (MvPolynomial.eval (boolPoint x))
    IsSelfAdjoint A ∧ ‖A‖ ≤ 1 := by
  dsimp only
  rw [evaluate_block]
  refine ⟨block_symm .., ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg_of_nonneg (by linarith))]
  have hcpos : 0 < c := by linarith
  apply (inv_mul_le_iff₀ hcpos).mpr
  rw [mul_one]
  apply le_trans _ hc
  apply block_norm _ _ P.vec K hK hV
  · have hd : 0 < 10*Real.sqrt S := by positivity
    have he : en P.target = 1 := by simpa [en, sqNorm] using congrArg Real.sqrt ht
    simp only [div_eq_inv_mul, en_scale _ _ (inv_nonneg_of_nonneg hd.le), he, mul_one]
    exact inv_le_one_of_one_le₀ (by have := Real.one_le_sqrt.mpr hS; linarith)
  · intro j i
    split <;> simp
end MatrixTools


open DeMorganApprox.Main DeMorganApprox.Main.SpanProgram
open scoped Matrix

namespace BooleanWitness

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
abbrev D (I J : Type) := Unit ⊕ I ⊕ J
abbrev o : D I J := .inl ()
noncomputable abbrev en {K : Type} [Fintype K] (v : K → ℝ) := Real.sqrt (sqNorm v)
noncomputable abbrev A (P : SpanProgram m I J) (S c : ℝ) (x : Fin m → Bool) :
    Matrix (D I J) (D I J) ℝ :=
  (scaledSymbolicMatrix P S c).map (MvPolynomial.eval (boolPoint x))

private theorem eval_label (l : Label m) (x : Fin m → Bool) :
    MvPolynomial.eval (boolPoint x) (labelPoly l) = if l.avail x then 1 else 0 := by
  cases l with
  | always => simp [labelPoly,Label.avail]
  | pos i | neg i => cases he : x i <;> simp [labelPoly,Label.avail,boolPoint,he]

private noncomputable def raw (P : SpanProgram m I J) (S : ℝ) (x : Fin m → Bool) :
    Matrix (D I J) (D I J) ℝ :=
  fun k l => match k,l with
    | .inl _,.inr (.inl i) | .inr (.inl i),.inl _ => P.target i/(10*Real.sqrt S)
    | .inr (.inl i),.inr (.inr j) | .inr (.inr j),.inr (.inl i) =>
        if (P.label j).avail x then P.vec j i else 0
    | _,_ => 0

private theorem numeric (P : SpanProgram m I J) (S c : ℝ) (x : Fin m → Bool) :
    A P S c x = c⁻¹ • raw P S x := by
  ext i j
  rcases i with u|i|j₁ <;> rcases j with v|k|l <;>
    simp [A,scaledSymbolicMatrix,symbolicMatrix,raw,Matrix.map_apply,MvPolynomial.smul_eq_C_mul,
      eval_label,mul_ite]

theorem accept (P : SpanProgram m I J) (S c : ℝ) (x : Fin m → Bool)
    (hS : 1 ≤ S) (a : J → ℝ) (ha : P.IsOneWitness x a) (hn : sqNorm a ≤ S) :
    ∃ k : D I J → ℝ, A P S c x *ᵥ k = 0 ∧ k o = 1 ∧ en (Pi.single o 1 - k) ≤ 1/10 := by
  let r := 10 * Real.sqrt S
  have hSp : 0 < S := by linarith
  have hr : 0 < r := mul_pos (by norm_num) (Real.sqrt_pos.mpr hSp)
  let k : D I J → ℝ := Sum.elim (fun _ => 1) (Sum.elim 0 ((-r⁻¹) • a))
  refine ⟨k,?_,rfl,?_⟩
  · rw [numeric,Matrix.smul_mulVec]
    suffices hz : raw P S x *ᵥ k = 0 by rw [hz,smul_zero]
    funext b
    rcases b with u|i|j
    · simp [Matrix.mulVec,dotProduct,raw,Fintype.sum_sum_type,k]
    · have he (j : J) :
          (if (P.label j).avail x then P.vec j i else 0) * (-r⁻¹ * a j) =
            (-r⁻¹) * (if (P.label j).avail x then a j * P.vec j i else 0) := by
          split_ifs <;> ring
      have hh : (∑ j, if (P.label j).avail x then a j * P.vec j i else 0) = P.target i := congrFun ha i
      simp only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fintype.sum_unique,raw,k,Sum.elim_inl,
        Sum.elim_inr, Pi.zero_apply,Pi.smul_apply,smul_eq_mul,mul_one,mul_zero,Finset.sum_const_zero,zero_add]
      change P.target i/r + (∑ j, (if (P.label j).avail x then P.vec j i else 0) * (-r⁻¹*a j)) = 0
      simp_rw [he]
      rw [← Finset.mul_sum,hh]
      ring
    · simp [Matrix.mulVec,dotProduct,raw,Fintype.sum_sum_type,k]
  · have hh : sqNorm (Pi.single o 1-k) = r⁻¹^2 * sqNorm a := by
      simp [sqNorm,Fintype.sum_sum_type,k,o,Pi.single_apply,mul_pow,Finset.mul_sum]
    rw [en,hh,Real.sqrt_le_left (by norm_num : 0 ≤ (1:ℝ)/10)]
    calc
      _ ≤ r⁻¹^2 * S := mul_le_mul_of_nonneg_left hn (sq_nonneg _)
      _ = (1/10:ℝ)^2 := by
        field_simp [hr.ne']
        dsimp [r]; nlinarith [Real.sq_sqrt hSp.le]

theorem reject (P : SpanProgram m I J) (S c : ℝ) (x : Fin m → Bool)
    (hS : 1 ≤ S) (hc : 1 ≤ c) (w : I → ℝ) (hw : P.IsZeroWitness x w) (hn : sqNorm w ≤ S) :
    ∃ h : D I J → ℝ, A P S c x *ᵥ h = Pi.single o 1 ∧ en h ≤ 10*c*S := by
  let r := 10 * Real.sqrt S
  have hSp : 0 < S := by linarith
  have hcp : 0 < c := by linarith
  have hr : 0 < r := mul_pos (by norm_num) (Real.sqrt_pos.mpr hSp)
  let h : D I J → ℝ := Sum.elim 0 (Sum.elim ((c*r) • w) 0)
  refine ⟨h, ?_, ?_⟩
  · rw [numeric,Matrix.smul_mulVec]
    funext k
    rcases k with u|i|j
    · have he (i : I) : P.target i/(10*Real.sqrt S)*(c*r*w i) = c*(w i * P.target i) := by
        change P.target i/r*(c*r*w i) = _; field_simp [hr.ne']
      cases u
      simp [Matrix.mulVec,dotProduct,raw,Fintype.sum_sum_type,h,he,← Finset.mul_sum,hw.1,
        hcp.ne',Pi.single_apply,o]
    · simp [Matrix.mulVec,dotProduct,raw,Fintype.sum_sum_type,h,Pi.single_apply,o]
    · by_cases ha : (P.label j).avail x = true
      · have he (i : I) : P.vec j i * (c*r*w i) = c*r*(w i * P.vec j i) := by ring
        simp [Matrix.mulVec,dotProduct,raw,Fintype.sum_sum_type,h,ha,he,← Finset.mul_sum,hw.2 j ha,
          Pi.single_apply,o]
      · simp [Matrix.mulVec,dotProduct,raw,Fintype.sum_sum_type,h,ha,Pi.single_apply,o]
  · have hh : sqNorm h = (c*r)^2 * sqNorm w := by
      simp [sqNorm,Fintype.sum_sum_type,h,mul_pow,Finset.mul_sum,mul_assoc]
    rw [en,hh,Real.sqrt_le_left (by positivity : 0 ≤ 10*c*S)]
    calc
      _ ≤ (c*r)^2 * S := mul_le_mul_of_nonneg_left hn (sq_nonneg _)
      _ = (10*c*S)^2 := by dsimp [r]; linear_combination 100*c^2*S*(Real.sq_sqrt hSp.le)
end BooleanWitness


open DeMorganApprox.Main MvPolynomial

namespace SymbolicAssembly

private lemma Lpos {σ : Type} (p : MvPolynomial σ ℝ) : 0 ≤ coeffL1 p :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private lemma Ladd {σ : Type} (p q : MvPolynomial σ ℝ) :
    coeffL1 (p + q) ≤ coeffL1 p + coeffL1 q := by
  classical
  let U := p.support ∪ q.support
  have h (r : MvPolynomial σ ℝ) (hr : r.support ⊆ U) :
      coeffL1 r = ∑ i ∈ U, |r.coeff i| := by
    apply Finset.sum_subset hr
    exact fun i _ hi => by simp [notMem_support_iff.mp hi]
  rw [h _ support_add, h _ Finset.subset_union_left, h _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun _ _ => by simpa using abs_add_le _ _

private lemma Lsum {σ α : Type} (s : Finset α) (f : α → MvPolynomial σ ℝ) :
    coeffL1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coeffL1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeffL1]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (Ladd ..).trans (add_le_add (le_refl _) ih)

private lemma Lmono {σ : Type} (i : σ →₀ ℕ) (a : ℝ) :
    coeffL1 (monomial i a) = |a| := by
  classical
  by_cases ha : a = 0 <;> simp [coeffL1, support_monomial, ha]

private lemma Lmul {σ : Type} (p q : MvPolynomial σ ℝ) :
    coeffL1 (p*q) ≤ coeffL1 p * coeffL1 q := by
  classical
  have he : p*q = ∑ i ∈ p.support, ∑ j ∈ q.support,
      monomial (i+j) (p.coeff i*q.coeff j) := by
    conv_lhs => rw [p.as_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    conv_lhs => enter [2]; rw [q.as_sum]
    simp only [Finset.mul_sum, monomial_mul]
  rw [he]
  refine (Lsum _ _).trans ?_
  calc
    _ ≤ _ := Finset.sum_le_sum fun i _ => Lsum _ _
    _ = _ := by
      simp only [Lmono, abs_mul]
      rw [coeffL1, coeffL1, Finset.sum_mul]
      simp only [Finset.mul_sum]

private lemma LC {σ : Type} (a : ℝ) : coeffL1 (C a : MvPolynomial σ ℝ) = |a| :=
  Lmono 0 a

private lemma Lsmul {σ : Type} (c : ℝ) (p : MvPolynomial σ ℝ) :
    coeffL1 (c • p) ≤ |c| * coeffL1 p := by
  simpa [← C_mul', LC] using Lmul (C c) p


variable {m : ℕ} {ι J : Type} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

noncomputable def assembled (P : SpanProgram m ι J) (S c : ℝ) (p : Polynomial ℝ) :
    MvPolynomial (Fin m) ℝ :=
    ∑ j ∈ Finset.range (p.natDegree+1), p.coeff j • (scaledSymbolicMatrix P S c ^ j) (.inl ()) (.inl ())

lemma assembled_coeffL1 (P : SpanProgram m ι J) (S c : ℝ) (p : Polynomial ℝ)
    (h : ∀ j : ℕ, coeffL1 ((scaledSymbolicMatrix P S c ^ j) (.inl ()) (.inl ())) ≤ 1) :
    coeffL1 (assembled P S c p) ≤ ∑ j ∈ Finset.range (p.natDegree+1), |p.coeff j| := by
  refine (Lsum _ _).trans (Finset.sum_le_sum fun j _ => (Lsmul _ _).trans ?_)
  exact (mul_le_mul_of_nonneg_left (h j) (abs_nonneg _)).trans_eq (mul_one _)

private lemma deg_sum {σ α : Type} (s : Finset α) (f : α → MvPolynomial σ ℝ) (d : ℕ)
    (h : ∀ j ∈ s, (f j).totalDegree ≤ d) : (∑ j ∈ s, f j).totalDegree ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (MvPolynomial.totalDegree_add ..).trans (max_le (h a (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))))

private lemma deg_label (l : Label m) : (labelPoly l).totalDegree ≤ 1 := by
  cases l with
  | always => simp [labelPoly]
  | pos i => simp [labelPoly]
  | neg i => simpa [labelPoly] using (MvPolynomial.totalDegree_sub (1 : MvPolynomial (Fin m) ℝ) (X i))

private lemma deg_entry (P : SpanProgram m ι J) (S c : ℝ) (a b : Unit ⊕ ι ⊕ J) :
    ((scaledSymbolicMatrix P S c) a b).totalDegree ≤ 1 := by
  refine (MvPolynomial.totalDegree_smul_le c⁻¹ _).trans ?_
  have hb (z : ℝ) (l : Label m) : (MvPolynomial.C z * labelPoly l).totalDegree ≤ 1 :=
    (MvPolynomial.totalDegree_mul ..).trans (by simpa using deg_label l)
  rcases a with _ | i | j <;> rcases b with _ | i' | j' <;>
    simp [symbolicMatrix,hb]

lemma assembled_degree (P : SpanProgram m ι J) (S c : ℝ) (p : Polynomial ℝ) :
    (assembled P S c p).totalDegree ≤ p.natDegree := by
  let M := scaledSymbolicMatrix P S c
  have hp (j : ℕ) (a b : Unit ⊕ ι ⊕ J) : ((M^j) a b).totalDegree ≤ j := by
    induction j generalizing a b with
    | zero => simp [Matrix.one_apply]; split <;> simp
    | succ j ih =>
      rw [pow_succ,Matrix.mul_apply]
      exact deg_sum _ _ _ fun i _ => (MvPolynomial.totalDegree_mul ..).trans
        (Nat.add_le_add (ih _ _) (deg_entry P S c _ _))
  exact deg_sum _ _ _ fun j hj => (MvPolynomial.totalDegree_smul_le _ _).trans
    ((hp j _ _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))

lemma assembled_eval (P : SpanProgram m ι J) (S c : ℝ) (p : Polynomial ℝ) (x : Fin m → Bool) :
    MvPolynomial.eval (boolPoint x) (assembled P S c p) =
      (Polynomial.aeval ((scaledSymbolicMatrix P S c).map (MvPolynomial.eval (boolPoint x))) p) (.inl ()) (.inl ()) := by
  classical
  let ev := MvPolynomial.eval (boolPoint x)
  let M := scaledSymbolicMatrix P S c
  have hmap (j : ℕ) (a b : Unit ⊕ ι ⊕ J) : ev ((M^j) a b) = ((M.map ev)^j) a b :=
    congrFun (congrFun (map_pow ev.mapMatrix M j) a) b
  rw [Polynomial.aeval_eq_sum_range]
  simp only [assembled,map_sum,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  change ev (p.coeff j • ((M^j) _ _)) = _
  rw [← MvPolynomial.C_mul',map_mul]
  have hc : ev (C (p.coeff j)) = p.coeff j := MvPolynomial.eval_C _
  rw [hc,hmap]

end SymbolicAssembly


open DeMorganApprox.Main DeMorganApprox.Main.Supplement MvPolynomial

theorem booleanMultilinearization {m : ℕ} (p : MvPolynomial (Fin m) ℝ) :
    IsMultilinear (multilinearize p) ∧
    (∀ x, eval (boolPoint x) (multilinearize p) = eval (boolPoint x) p) ∧
    (multilinearize p).totalDegree ≤ p.totalDegree ∧ coeffL1 (multilinearize p) ≤ coeffL1 p := by
  classical
  let clip (s : Fin m →₀ ℕ) := s.mapRange (fun k => min k 1) (by simp)
  have supp {s : Fin m →₀ ℕ} (hs : s ∈ (multilinearize p).support) :
      ∃ t ∈ p.support, s = clip t := by
    obtain ⟨t,ht,hs'⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hs)
    exact ⟨t,ht,Finset.mem_singleton.mp (support_monomial_subset hs')⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro s hs i
    obtain ⟨t,_,rfl⟩ := supp hs
    exact min_le_right _ _
  · intro x
    conv_rhs => rw [p.as_sum]
    rw [multilinearize, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [eval_monomial,eval_monomial]
    congr 1
    rw [Finsupp.prod_fintype _ _ (by simp),Finsupp.prod_fintype _ _ (by simp)]
    apply Finset.prod_congr rfl
    intro i _
    simp only [Finsupp.mapRange_apply]
    cases h : t i <;> cases h' : x i <;> simp [boolPoint,h,h']
  · apply Finset.sup_le
    intro s hs
    obtain ⟨t,ht,rfl⟩ := supp hs
    apply le_trans _ (le_totalDegree ht)
    rw [Finsupp.sum_fintype _ _ (by simp),Finsupp.sum_fintype _ _ (by simp)]
    exact Finset.sum_le_sum (fun _ _ => min_le_left _ _)
  · let q := multilinearize p
    change ∑ s ∈ q.support, |q.coeff s| ≤ _
    calc
      _ ≤ ∑ s ∈ q.support, ∑ t ∈ p.support, |(monomial (clip t) (p.coeff t)).coeff s| := by
        apply Finset.sum_le_sum
        intro s _
        change |(∑ t ∈ p.support, monomial (clip t) (p.coeff t)).coeff s| ≤ _
        rw [coeff_sum]
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ t ∈ p.support, ∑ s ∈ q.support, |(monomial (clip t) (p.coeff t)).coeff s| := Finset.sum_comm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro t _
        by_cases h : clip t ∈ q.support <;> simp [coeff_monomial, h, eq_comm, apply_ite abs]

open DeMorganApprox.Main DeMorganApprox.Main.Supplement
open scoped Matrix.Norms.L2Operator

theorem solution (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) {ι J : Type} [Fintype ι] [Fintype J] (P : SpanProgram m ι J)
        (f : (Fin m → Bool) → Bool) (S : ℝ), 1 ≤ S →
        P.IsVectorForm → P.Computes f → P.HasBalancedBound S → AbsNormLE P.vec K →
        ∃ Q : MvPolynomial (Fin m) ℝ, IsMultilinear Q ∧
          (∀ x : Fin m → Bool, |MvPolynomial.eval (boolPoint x) Q - boolVal (f x)| ≤ 1 / 3) ∧
          (Q.totalDegree : ℝ) ≤ C * S ∧
          coeffL1 Q ≤ (2 : ℝ) ^ (C * S) := by
  obtain ⟨c₀, hmom⟩ := claim_4_1_1 K hK
  let c := max c₀ (2+2*K)
  have hc : 2+2*K ≤ c := le_max_right .. 
  have hc₁ : 1 ≤ c := by linarith
  refine ⟨8*(100*c+1), by positivity, ?_⟩
  intro m ι J _ _ P f S hS hv hf hw hV
  classical
  let d := ⌈100*c*S⌉₊
  let p := FilterTools.avgT d
  let Q := SymbolicAssembly.assembled P S c p
  have hdlo : 100*c*S ≤ (d:ℝ) := Nat.le_ceil _
  have hdhi : (d:ℝ) ≤ (100*c+1)*S := by
    have hlt : (d:ℝ) < 100*c*S+1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  obtain ⟨hmul, heval, hdeg, hL⟩ := booleanMultilinearization Q
  refine ⟨multilinearize Q, hmul, fun x => ?_, ?_, ?_⟩
  · rw [heval, show MvPolynomial.eval (boolPoint x) Q = _ from SymbolicAssembly.assembled_eval P S c p x]
    let A := BooleanWitness.A P S c x
    obtain ⟨hadj, hA⟩ := MatrixTools.eval_contract P S c K hS hK hc hv.1 hV x
    have hop : ‖Polynomial.aeval A p‖ ≤ 1 :=
      MatrixTools.filter_op A hadj hA p 1 zero_le_one (fun x hx => FilterTools.avgT_abs hx d)
    cases hx : f x with
    | true =>
      obtain ⟨a,ha,hn⟩ := (hw.2.2 x).1 ((hf x).mpr hx)
      obtain ⟨k,hk,hko,hdist⟩ := BooleanWitness.accept P S c x hS a ha hn
      exact (MatrixTools.filter_accept A p _ k hk hko hdist (FilterTools.avgT_zero d) hop).trans (by norm_num)
    | false =>
      obtain ⟨w,hwz,hn⟩ := (hw.2.2 x).2 (fun ha => by simpa [hx] using (hf x).mp ha)
      obtain ⟨v,hv₁,hv₂⟩ := BooleanWitness.reject P S c x hS hc₁ w hwz hn
      have hδ : 0 ≤ 1/((d:ℝ)+1) := by positivity
      have hdec : ‖Polynomial.aeval A (p*Polynomial.X)‖ ≤ 1/((d:ℝ)+1) :=
        MatrixTools.filter_op A hadj hA _ _ hδ (fun x hx => by simpa [p,mul_comm] using FilterTools.avgT_decay hx d)
      have hh := MatrixTools.filter_reject A p _ v _ hv₁ hv₂ _ hδ hdec
      simp only [boolVal, Bool.false_eq_true, ↓reduceIte, sub_zero]
      refine hh.trans ?_
      rw [one_div, inv_mul_le_iff₀ (by positivity : 0 < (d:ℝ)+1)]
      nlinarith
  · have hnat := hdeg.trans ((SymbolicAssembly.assembled_degree P S c p).trans (FilterTools.avgT_deg d))
    have hreal : ((multilinearize Q).totalDegree : ℝ) ≤ 2*(d:ℝ) := by exact_mod_cast hnat
    nlinarith
  · refine hL.trans ((SymbolicAssembly.assembled_coeffL1 P S c p (hmom c (le_max_left ..) m P hv.1 hV S hS)).trans ?_)
    rw [← p.sum_over_range (f := fun _ t => |t|) (fun _ => abs_zero)]
    refine (FilterTools.avgT_mass d).trans ?_
    calc
      (16:ℝ)^(2*d) = (2:ℝ)^(8*d) := by
        rw [show (16:ℝ) = 2^4 by norm_num, ← pow_mul]
        congr 1; omega
      _ = (2:ℝ)^(8*(d:ℝ)) := by norm_cast
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

