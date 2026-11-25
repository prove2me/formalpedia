-- Prove2me | solution 1 for DeMorganApprox.Main.Supplement.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:25:20.354012+00:00
-- url     : https://prove2.me/submissions/e06f8e0f-3ebf-44c4-9d70-89279f9c6423

import Definitions.Def_DeMorganApprox_Main_Supplement_Multilinearize

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
namespace ParityLower
open DeMorganApprox.Main DeMorganApprox.Main.Supplement MvPolynomial

private def flip {m : ℕ} : Formula m → Formula m
  | .lit i b => .lit i (!b)
  | .and p q => .or (flip p) (flip q)
  | .or p q => .and (flip p) (flip q)

@[simp] private lemma flip_size {m} (p : Formula m) : (flip p).leaves = p.leaves := by
  induction p <;> simp_all [flip, Formula.leaves]

@[simp] private lemma flip_eval {m} (p : Formula m) (x : Fin m → Bool) :
    (flip p).eval x = !(p.eval x) := by
  induction p with
  | lit i b => cases b <;> simp [flip,Formula.eval]
  | and p q hp hq | or p q hp hq => simp [flip, Formula.eval,hp,hq]

private def xorF {m} (p q : Formula m) := Formula.or (.and p (flip q)) (.and (flip p) q)
private def sgn (b : Bool) : ℝ := if b then -1 else 1

private lemma parityFormula (k m : ℕ) (v : Fin (2^k) → Fin m) : ∃ F : Formula m,
    F.leaves = 4^k ∧ ∀ x, sgn (F.eval x) = ∏ i, sgn (x (v i)) := by
  classical
  induction k with
  | zero =>
    refine ⟨.lit (v 0) true,rfl,?_⟩
    intro x
    simp [Formula.eval]
  | succ k ih =>
    let e : Bool × Fin (2^k) ≃ Fin (2^(k+1)) := Fintype.equivFinOfCardEq (by simp [pow_succ, Nat.mul_comm])
    obtain ⟨p,hp,ep⟩ := ih (fun i => v (e (true,i)))
    obtain ⟨q,hq,eq⟩ := ih (fun i => v (e (false,i)))
    refine ⟨xorF p q,?_,?_⟩
    · simp [xorF,Formula.leaves,hp,hq,pow_succ]; omega
    · intro x
      rw [← e.prod_comp (fun i => sgn (x (v i))), Fintype.prod_prod_type,Fintype.prod_bool,← ep,← eq]
      cases ha : p.eval x <;> cases hb : q.eval x <;> simp [xorF,Formula.eval,ha,hb,sgn]

private noncomputable def mask {m} (x : Fin m → Bool) : ℝ := ∏ i, sgn (x i)

private lemma mask_moment {m} (s : Fin m →₀ ℕ) :
    |∑ x : Fin m → Bool, mask x * ∏ i, boolPoint x i ^ s i| ≤ 1 := by
  classical
  simp only [mask, ← Finset.prod_mul_distrib, boolPoint]
  rw [← Fintype.prod_sum (fun (i : Fin m) (b : Bool) => sgn b * (if b then (1:ℝ) else 0) ^ s i),
      Finset.abs_prod]
  apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
  intro i _
  cases h : s i <;> norm_num [Fintype.sum_bool,sgn]

private theorem corrBound {m} (p : MvPolynomial (Fin m) ℝ) :
    |∑ x, mask x * eval (boolPoint x) p| ≤ coeffL1 p := by
  classical
  have hex (x : Fin m → Bool) : mask x * eval (boolPoint x) p =
      ∑ s ∈ p.support, p.coeff s * (mask x * ∏ i, boolPoint x i ^ s i) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [eval_monomial,Finsupp.prod_fintype _ _ (by simp)]
    ring
  simp only [hex]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro s _
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (mask_moment s)

private lemma lowerBound {m : ℕ} (hm : 1 ≤ m) (F : Formula m)
    (hF : ∀ x, sgn (F.eval x) = mask x) (Q : MvPolynomial (Fin m) ℝ)
    (hq : ∀ x, |eval (boolPoint x) Q - boolVal (F.eval x)| ≤ 1/3) :
    (2 : ℝ)^m ≤ 6 * coeffL1 Q := by
  classical
  have h (x : Fin m → Bool) : (1/3 : ℝ) ≤ mask x * (1 - 2 * eval (boolPoint x) Q) := by
    rw [← hF]
    have he := abs_le.mp (hq x)
    cases ha : F.eval x <;> simp [sgn,boolVal,ha] at * <;> linarith
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun x _ => h x)
  have hmask : (∑ x : Fin m → Bool, mask x) = 0 := by
    change (∑ x : Fin m → Bool, ∏ i, sgn (x i)) = _
    rw [← Fintype.prod_sum (fun (_ : Fin m) (b : Bool) => sgn b)]
    have : Nonempty (Fin m) := ⟨⟨0,by omega⟩⟩
    simp [Fintype.sum_bool,sgn,show m ≠ 0 by omega]
  have hlin (x : Fin m → Bool) : mask x * (1 - 2 * eval (boolPoint x) Q) =
      mask x - 2 * (mask x * eval (boolPoint x) Q) := by ring
  simp only [hlin, Finset.sum_sub_distrib, ← Finset.mul_sum, hmask] at hsum
  simp [Fintype.card_fun] at hsum
  have hcorr := abs_le.mp (corrBound Q)
  linarith

end ParityLower
open DeMorganApprox.Main DeMorganApprox.Main.Supplement MvPolynomial ParityLower

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (m : ℕ) (φ : Formula m), φ.leaves ≤ n ∧
        ∀ P : MvPolynomial (Fin m) ℝ,
          (∀ x : Fin m → Bool, |MvPolynomial.eval (boolPoint x) P - boolVal (φ.eval x)| ≤ 1 / 3) →
            (2 : ℝ) ^ (c * Real.sqrt (n : ℝ)) ≤ coeffL1 (multilinearize P) := by
  refine ⟨1/4,by norm_num,64,?_⟩
  intro n hn
  let k := Nat.log 4 n
  let m := 2^k
  obtain ⟨F,hsize,hval⟩ := parityFormula k m id
  refine ⟨m,F,hsize.le.trans (Nat.pow_log_le_self 4 (by omega)),?_⟩
  intro P hP
  have hk : 3 ≤ k := Nat.le_log_of_pow_le (by decide) (by simpa using hn)
  have hm : 8 ≤ m := (Nat.pow_le_pow_right (by decide : 0 < 2) hk)
  have hsq : m^2 = 4^k := by dsimp [m]; rw [←pow_mul, Nat.mul_comm, pow_mul]; norm_num
  have hN : n ≤ (2*m)^2 := by
    have hh := Nat.lt_pow_succ_log_self (by decide : 1<4) n
    change n < 4^(k+1) at hh
    rw [pow_succ,←hsq] at hh
    nlinarith
  have hroot : Real.sqrt (n : ℝ) ≤ 2 * (m : ℝ) := by
    have h := Real.sqrt_le_sqrt (show (n : ℝ) ≤ (2*(m:ℝ))^2 by exact_mod_cast hN)
    rwa [Real.sqrt_sq (by positivity)] at h
  have hlow := lowerBound (show 1 ≤ m by omega) F hval (multilinearize P)
    (fun x => by rw [(booleanMultilinearization P).2.1 x]; exact hP x)
  have hmr : (8 : ℝ) ≤ m := by exact_mod_cast hm
  calc
    _ ≤ (2 : ℝ)^((m : ℝ)-3) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = (2 : ℝ)^m / 8 := by rw [Real.rpow_sub (by norm_num),Real.rpow_natCast]; norm_num
    _ ≤ _ := by linarith [show 0 ≤ (2:ℝ)^m by positivity]
