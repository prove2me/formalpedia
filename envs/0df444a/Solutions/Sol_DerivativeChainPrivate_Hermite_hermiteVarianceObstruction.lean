-- Prove2me | solution 1 for DerivativeChainPrivate.Hermite.hermiteVarianceObstruction
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T08:19:10.180711+00:00
-- url     : https://prove2.me/submissions/8100b5c4-aa8e-4291-b044-22bdebf769ca

import Mathlib
import Definitions.Def_DerivativeChainPrivate_hermite_closed

set_option autoImplicit false
set_option maxHeartbeats 1600000
open Polynomial
namespace DerivativeChainPrivate.Hermite





lemma root2 {x : ℝ} (h : (H 2).eval x = 0) : |x| = 1 := by
  have he : x^2 - 1 = 0 := by simpa [H] using h
  have ha := sq_abs x
  have hp := abs_nonneg x
  nlinarith

lemma root3 {x : ℝ} (h : (H 3).eval x = 0) :
    x = 0 ∨ (173/100 : ℝ) ≤ |x| := by
  have he : x * (x^2-3) = 0 := by
    have he : x^3 - 3*x = 0 := by simpa [H] using h
    nlinarith
  rcases mul_eq_zero.mp he with hx | hx
  · exact Or.inl hx
  · right
    have ha := sq_abs x
    have hp := abs_nonneg x
    nlinarith

lemma root4 {x : ℝ} (h : (H 4).eval x = 0) :
    ((74/100 : ℝ) ≤ |x| ∧ |x| ≤ 75/100) ∨
    ((233/100 : ℝ) ≤ |x| ∧ |x| ≤ 234/100) := by
  have he : x^4 - 6*x^2 + 3 = 0 := by simpa [H] using h
  have hs : (Real.sqrt 6)^2 = 6 := Real.sq_sqrt (by norm_num)
  have hs0 := Real.sqrt_nonneg (6 : ℝ)
  have hslo : (244/100 : ℝ) < Real.sqrt 6 := by nlinarith
  have hshi : Real.sqrt 6 < (245/100 : ℝ) := by nlinarith
  have hh : (x^2-3)^2 = (Real.sqrt 6)^2 := by nlinarith
  have ha := sq_abs x
  have hp := abs_nonneg x
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hh with hl | hr
  · right; constructor <;> nlinarith
  · left; constructor <;> nlinarith

lemma root5 {x : ℝ} (h : (H 5).eval x = 0) :
    x = 0 ∨ ((135/100 : ℝ) ≤ |x| ∧ |x| ≤ 136/100) ∨
      (285/100 : ℝ) ≤ |x| := by
  have he : x*(x^4-10*x^2+15) = 0 := by
    have he : x^5-10*x^3+15*x = 0 := by simpa [H] using h
    nlinarith [he]
  rcases mul_eq_zero.mp he with hx | hx
  · exact Or.inl hx
  · right
    have hs : (Real.sqrt 10)^2 = 10 := Real.sq_sqrt (by norm_num)
    have hs0 := Real.sqrt_nonneg (10 : ℝ)
    have hslo : (316/100 : ℝ) < Real.sqrt 10 := by nlinarith
    have hshi : Real.sqrt 10 < (317/100 : ℝ) := by nlinarith
    have hh : (x^2-5)^2 = (Real.sqrt 10)^2 := by nlinarith
    have ha := sq_abs x
    have hp := abs_nonneg x
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hh with hl | hr
    · right; nlinarith
    · left; constructor <;> nlinarith

lemma root6 {x : ℝ} (h : (H 6).eval x = 0) : (3/5 : ℝ) ≤ |x| := by
  have he : x^6-15*x^4+45*x^2-15 = 0 := by simpa [H] using h
  have ha := sq_abs x
  have hp := abs_nonneg x
  by_contra hn
  have ht : x^2 < (9/25 : ℝ) := by nlinarith
  have ht0 : 0 ≤ x^2 := sq_nonneg x
  have hc : 0 ≤ (x^2)^2 + (9/25-15 : ℝ)*x^2 + ((9/25 : ℝ)^2-15*(9/25)+45) := by
    nlinarith [sq_nonneg (x^2)]
  have hm := mul_nonpos_of_nonpos_of_nonneg (show x^2-(9/25 : ℝ) ≤ 0 by linarith) hc
  nlinarith [hm]

end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite

lemma lower_six {x2 x3 x4 x5 x6 : ℝ}
    (h2 : (H 2).eval x2 = 0) (h3 : (H 3).eval x3 = 0)
    (h4 : (H 4).eval x4 = 0) (h5 : (H 5).eval x5 = 0)
    (h6 : (H 6).eval x6 = 0) :
    (93/20 : ℝ) ≤ |x2| + |x3-x2| + |x4-x3| + |x5-x4| + |x6-x5| + |x6| := by
  have r2 := root2 h2
  have t23 := abs_sub_abs_le_abs_sub x3 x2
  have t34 := abs_sub_abs_le_abs_sub x4 x3
  have t43 := abs_sub_abs_le_abs_sub x3 x4
  have t45 := abs_sub_abs_le_abs_sub x5 x4
  have t54 := abs_sub_abs_le_abs_sub x4 x5
  have t56 := abs_sub_abs_le_abs_sub x5 x6
  have a23 := abs_nonneg (x3-x2)
  have a34 := abs_nonneg (x4-x3)
  have a45 := abs_nonneg (x5-x4)
  have a56 := abs_nonneg (x6-x5)
  have sym34 : |x3-x4| = |x4-x3| := abs_sub_comm _ _
  have sym45 : |x4-x5| = |x5-x4| := abs_sub_comm _ _
  have sym56 : |x5-x6| = |x6-x5| := abs_sub_comm _ _
  have d3 : |x3| ≤ |x2| + |x3-x2| := by linarith
  have d4 : |x4| ≤ |x2| + |x3-x2| + |x4-x3| := by linarith
  have d5 : |x5| ≤ |x2| + |x3-x2| + |x4-x3| + |x5-x4| := by linarith
  have inner4 : (74/100 : ℝ) ≤ |x4| → |x4| ≤ 75/100 →
      (271/100 : ℝ) ≤ |x2|+|x3-x2|+|x4-x3| := by
    intro hlarge hsmall
    rcases root3 h3 with hz | hz
    · subst x3; simp only [zero_sub, abs_neg, sub_zero] at *; linarith [abs_nonneg x4]
    · linarith
  rcases root5 h5 with hz | hi | ho
  · subst x5
    simp only [zero_sub, abs_neg, sub_zero] at *
    have hcost : (345/100 : ℝ) ≤ |x2|+|x3-x2|+|x4-x3|+|x4| := by
      rcases root4 h4 with hi | ho
      · have := inner4 hi.1 hi.2; linarith [hi.1]
      · linarith [ho.1]
    have := root6 h6
    linarith
  · have hcost : (330/100 : ℝ) ≤ |x2|+|x3-x2|+|x4-x3|+|x5-x4| := by
      rcases root4 h4 with hinner | houter
      · have := inner4 hinner.1 hinner.2; linarith [hinner.2,hi.1]
      · linarith [houter.1,hi.2]
    linarith [hi.1]
  · linarith





lemma closed_six_lower {z : Fin 6 → ℝ} (h : Chain 6 z) :
    (93/20 : ℝ) ≤ ClosedCost z 6 := by
  have h0 : z 0 = 0 := by simpa [H] using h 0 (by decide)
  have := lower_six (h 1 (by decide)) (h 2 (by decide)) (h 3 (by decide))
    (h 4 (by decide)) (h 5 (by decide))
  simpa [ClosedCost, cost, Finset.sum_range_succ, h0] using this

end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite

lemma derivative_rows (m : ℕ) (hm : m ∈ Finset.Icc 1 5) :
    derivative (H (m+1)) = (m+1 : ℝ) • H m := by
  have hm1 := (Finset.mem_Icc.mp hm).1
  have hm5 := (Finset.mem_Icc.mp hm).2
  interval_cases m <;>
    norm_num [H, derivative_add, derivative_sub, derivative_mul, derivative_pow,
      Polynomial.smul_eq_C_mul, Polynomial.C_ofNat] <;> ring

lemma sqrt_data :
    1 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 2 ∧
    0 ≤ Real.sqrt (3-Real.sqrt 6) ∧
    Real.sqrt (3-Real.sqrt 6) ≤ Real.sqrt 3 ∧
    (Real.sqrt (3-Real.sqrt 6))^2 = 3-Real.sqrt 6 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have ht := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have hp := Real.sqrt_nonneg (3:ℝ)
  have hq := Real.sqrt_nonneg (6:ℝ)
  have ht3 : Real.sqrt 6 ≤ (3:ℝ) := by nlinarith
  have ha := Real.sq_sqrt (show 0 ≤ 3-Real.sqrt 6 by linarith)
  have hap := Real.sqrt_nonneg (3-Real.sqrt 6)
  refine ⟨by nlinarith, by nlinarith, hap, ?_, ha⟩
  nlinarith



lemma witness5_chain : Chain 5 witness5 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have ht := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have ha := sqrt_data.2.2.2.2
  intro i hi
  fin_cases i
  · norm_num [H,witness5]
  · norm_num [H,witness5]
  · norm_num [H,witness5]
    nlinarith [congrArg (fun t : ℝ => t * Real.sqrt 3) hs]
  · norm_num [H,witness5]; nlinarith
  · norm_num [H,witness5]
  · norm_num at hi

lemma witness5_cost : ClosedCost witness5 5 = 2*Real.sqrt 3 := by
  obtain ⟨hs1,hs2,ha0,has,ha⟩ := sqrt_data
  norm_num [ClosedCost,cost,witness5,Finset.sum_range_succ]
  rw [abs_of_nonneg (by linarith : 0 ≤ Real.sqrt 3 - 1),
    abs_of_nonpos (by linarith : Real.sqrt (3-Real.sqrt 6)-Real.sqrt 3 ≤ 0),
    abs_of_nonneg ha0]
  ring



lemma closed_nonneg (m : ℕ) (z : Fin 6 → ℝ) : 0 ≤ ClosedCost z m := by
  apply add_nonneg _ (abs_nonneg _)
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma budget5_bounds : 0 ≤ Budget 5 ∧ Budget 5 ≤ 2*Real.sqrt 3 := by
  have hmem : ClosedCost witness5 5 ∈ {c : ℝ | ∃ z, Chain 5 z ∧ c = ClosedCost z 5} :=
    ⟨witness5,witness5_chain,rfl⟩
  have hb : BddBelow {c : ℝ | ∃ z, Chain 5 z ∧ c = ClosedCost z 5} := by
    refine ⟨0, ?_⟩
    rintro c ⟨z,hz,rfl⟩
    exact closed_nonneg _ _
  exact ⟨le_csInf ⟨_,hmem⟩ (by rintro c ⟨z,hz,rfl⟩; exact closed_nonneg _ _),
    witness5_cost ▸ csInf_le hb hmem⟩

lemma exists_root6 : ∃ x : ℝ, (H 6).eval x = 0 := by
  have hm : (0:ℝ) ∈ Set.Icc ((H 6).eval 0) ((H 6).eval 1) := by norm_num [H]
  obtain ⟨x,hx,hroot⟩ := intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num)
    (H 6).continuous.continuousOn hm
  exact ⟨x,hroot⟩

lemma budget6_lower : (93/20 : ℝ) ≤ Budget 6 := by
  obtain ⟨x,hx⟩ := exists_root6
  let z : Fin 6 → ℝ := ![0,1,Real.sqrt 3,Real.sqrt (3-Real.sqrt 6),0,x]
  have hz : Chain 6 z := by
    intro i hi
    by_cases hi5 : i.val < 5
    · have hh := witness5_chain i hi5
      fin_cases i <;> simp_all [z,witness5]
    · have hi : i = 5 := by ext; simp; omega
      subst i; simpa [z] using hx
  change (93/20 : ℝ) ≤ sInf {c : ℝ | ∃ z, Chain 6 z ∧ c = ClosedCost z 6}
  apply le_csInf
  · exact ⟨ClosedCost z 6, z, hz, rfl⟩
  · rintro c ⟨w,hw,rfl⟩
    exact closed_six_lower hw

theorem realHermiteLocalObstruction :
    9 < Budget 6 ^ 2 - Budget 5 ^ 2 := by
  have hb5 := budget5_bounds
  have hb6 := budget6_lower
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hs0 := Real.sqrt_nonneg (3:ℝ)
  nlinarith

end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite

lemma root_between (p : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (ha : p.eval a < 0) (hb : 0 < p.eval b) :
    ∃ x ∈ Set.Ioo a b, p.eval x = 0 := by
  obtain ⟨x,hx,hroot⟩ := intermediate_value_Icc hab.le p.continuous.continuousOn
    (show (0:ℝ) ∈ Set.Icc (p.eval a) (p.eval b) from ⟨ha.le,hb.le⟩)
  refine ⟨x,⟨?_,?_⟩,hroot⟩
  · by_contra hn
    have he : x = a := by linarith [hx.1]
    subst x; linarith
  · by_contra hn
    have he : x = b := by linarith [hx.2]
    subst x; linarith

lemma hermite6_splits : (H 6).Splits := by
  obtain ⟨a,ha,hra⟩ := root_between (H 6) (show (0:ℝ) < 1 by norm_num)
    (by norm_num [H]) (by norm_num [H])
  obtain ⟨b,hb,hrb⟩ := root_between (-H 6) (show (1:ℝ) < 2 by norm_num)
    (by norm_num [H]) (by norm_num [H])
  have hrb : (H 6).eval b = 0 := by simpa using hrb
  obtain ⟨c,hc,hrc⟩ := root_between (H 6) (show (3:ℝ) < 4 by norm_num)
    (by norm_num [H]) (by norm_num [H])
  let r : Fin 6 → ℝ := ![-c,-b,-a,a,b,c]
  have hinj : Function.Injective r := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [r] at hij ⊢ <;>
      linarith [ha.1,ha.2,hb.1,hb.2,hc.1,hc.2]
  have hr : ∀ i, (H 6).eval (r i) = 0 := by
    intro i
    have hneg (x : ℝ) (hx : (H 6).eval x = 0) : (H 6).eval (-x) = 0 := by
      have he : (H 6).eval (-x) = (H 6).eval x := by
        simp only [H,eval_add,eval_sub,eval_pow,eval_X,eval_mul,eval_ofNat]
        ring
      exact he.trans hx
    fin_cases i
    · exact hneg c hrc
    · exact hneg b hrb
    · exact hneg a hra
    · exact hra
    · exact hrb
    · exact hrc
  let s := Finset.univ.image r
  have hs : s.card = 6 := by simp [s,Finset.card_image_of_injective _ hinj]
  have hdeg : (H 6).natDegree = 6 := by
    have hlow : ((-15 : Polynomial ℝ)*X^4 + 45*X^2 - 15).natDegree ≤ 4 := by
      compute_degree!
    have he : H 6 = X^6 + ((-15 : Polynomial ℝ)*X^4 + 45*X^2 - 15) := by
      simp only [H]; ring
    rw [he, natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · simp only [natDegree_X_pow]; omega
  have hn : H 6 ≠ 0 := by
    intro he
    have := congrArg (fun p : Polynomial ℝ => p.eval 0) he
    norm_num [H] at this
  have heq : (H 6).roots = s.val := by
    apply roots_eq_of_natDegree_le_card_of_ne_zero
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact hr i
    · omega
    · exact hn
  apply Polynomial.splits_iff_card_roots.mpr
  simpa [heq,hdeg] using hs



lemma variances : Variance 5 = 4 ∧ Variance 6 = 5 := by
  norm_num [Variance,H,coeff_sub,coeff_add,coeff_mul,coeff_X_pow,coeff_X]



end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite

lemma esymm_one (s : Multiset ℝ) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]

lemma esymm_cons_two (a : ℝ) (s : Multiset ℝ) :
    (a ::ₘ s).esymm 2 = s.esymm 2 + a*s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one,
    Multiset.map_map]
  simpa using (Multiset.sum_map_mul_left (s := s) (a := a) (f := fun x : ℝ => x))

lemma sumsq_esymm (s : Multiset ℝ) :
    (s.map (fun x => x^2)).sum = s.sum^2 - 2*s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm,Multiset.powersetCard_zero_right]
  | @cons a s ih => simp [esymm_cons_two, ih]; ring

lemma hermite5_splits : (H 5).Splits := by
  obtain ⟨a,ha,hra⟩ := root_between (-H 5) (show (1:ℝ) < 2 by norm_num)
    (by norm_num [H]) (by norm_num [H])
  have hra : (H 5).eval a = 0 := by simpa using hra
  obtain ⟨b,hb,hrb⟩ := root_between (H 5) (show (2:ℝ) < 3 by norm_num)
    (by norm_num [H]) (by norm_num [H])
  let r : Fin 5 → ℝ := ![-b,-a,0,a,b]
  have hinj : Function.Injective r := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [r] at hij ⊢ <;>
      linarith [ha.1,ha.2,hb.1,hb.2]
  have hr : ∀ i, (H 5).eval (r i) = 0 := by
    intro i
    have hneg (x : ℝ) (hx : (H 5).eval x = 0) : (H 5).eval (-x) = 0 := by
      have hh : x^5-10*x^3+15*x = 0 := by simpa [H] using hx
      simp only [H,eval_add,eval_sub,eval_pow,eval_X,eval_mul,eval_ofNat]
      nlinarith only [hh]
    fin_cases i
    · exact hneg b hrb
    · exact hneg a hra
    · norm_num [r,H]
    · exact hra
    · exact hrb
  let s := Finset.univ.image r
  have hs : s.card = 5 := by simp [s,Finset.card_image_of_injective _ hinj]
  have hdeg : (H 5).natDegree = 5 := by
    have hlow : ((-10 : Polynomial ℝ)*X^3 + 15*X).natDegree ≤ 3 := by compute_degree!
    have he : H 5 = X^5 + ((-10 : Polynomial ℝ)*X^3 + 15*X) := by simp only [H]; ring
    rw [he, natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · simp only [natDegree_X_pow]; omega
  have hn : H 5 ≠ 0 := by
    intro he
    have := congrArg (fun p : Polynomial ℝ => p.eval 1) he
    norm_num [H] at this
  have heq : (H 5).roots = s.val := by
    apply roots_eq_of_natDegree_le_card_of_ne_zero
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact hr i
    · omega
    · exact hn
  apply Polynomial.splits_iff_card_roots.mpr
  simpa [heq,hdeg] using hs



lemma uniform_variance_of_coeffs {p : Polynomial ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hsplit : p.Splits) (hdeg : p.natDegree = n)
    (hm : p.Monic) (hc : p.coeff (n-1) = 0) :
    ((p.roots.map (fun x => (x-p.roots.sum/(n:ℝ))^2)).sum)/(n:ℝ) =
      -2*p.coeff (n-2)/(n:ℝ) := by
  have h1 := coeff_eq_esymm_roots_of_splits hsplit (k := n-1) (by omega)
  have h2 := coeff_eq_esymm_roots_of_splits hsplit (k := n-2) (by omega)
  have hn1 : n-(n-1)=1 := by omega
  have hn2 : n-(n-2)=2 := by omega
  simp only [hdeg, hm.leadingCoeff, one_mul, hn1, hn2, pow_one, even_two,
    Even.neg_pow, one_pow, esymm_one] at h1 h2
  have hsum : p.roots.sum = 0 := by linarith [hc]
  simp only [hsum,zero_div,sub_zero]
  rw [sumsq_esymm,hsum]
  rw [h2]
  ring

end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite

lemma uniform_variances : UniformVariance 5 = 4 ∧ UniformVariance 6 = 5 := by
  have h5 : UniformVariance 5 = Variance 5 := by
    apply uniform_variance_of_coeffs (by norm_num) hermite5_splits
    · norm_num only [H]; compute_degree!
    · norm_num only [H]; monicity!
    · norm_num [H,coeff_sub,coeff_add,coeff_mul,coeff_X_pow,coeff_X]
  have h6 : UniformVariance 6 = Variance 6 := by
    apply uniform_variance_of_coeffs (by norm_num) hermite6_splits
    · norm_num only [H]; compute_degree!
    · norm_num only [H]; monicity!
    · norm_num [H,coeff_sub,coeff_add,coeff_mul,coeff_X_pow,coeff_X]
  exact ⟨h5.trans variances.1,h6.trans variances.2⟩



end DerivativeChainPrivate.Hermite

open Polynomial DerivativeChainPrivate.Hermite in

theorem solution :
    (H 5).Splits ∧ (H 6).Splits ∧
    (∀ m ∈ Finset.Icc 1 5, derivative (H (m+1)) = (m+1 : ℝ) • H m) ∧
    UniformVariance 5 = 4 ∧ UniformVariance 6 = 5 ∧
    9 * (UniformVariance 6 - UniformVariance 5) < Budget 6 ^ 2 - Budget 5 ^ 2 := by
  refine ⟨hermite5_splits,hermite6_splits,derivative_rows,
    uniform_variances.1,uniform_variances.2,?_⟩
  rw [uniform_variances.1,uniform_variances.2]
  convert realHermiteLocalObstruction using 1; norm_num
