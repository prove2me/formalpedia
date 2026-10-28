-- Prove2me | solution 1 for BBBV.RandomOracle.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-24T09:11:00.209988+00:00
-- url     : https://prove2.me/submissions/e2e7a9e3-4271-44b5-b1f9-be6e2ccf812f

import Mathlib
import Definitions.Def_BBBV_RandomOracle_QueryModel

noncomputable section
open Classical Finset BBBV.RandomOracle
namespace BQProof
variable {X R W : Type} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
  [AddCommGroup R] [Fintype W] [DecidableEq W]

omit [DecidableEq X] [DecidableEq R] [DecidableEq W] in
lemma oracle_some (f : X → R) (φ : State X R W) (x : X) (z : R) (w : W) :
    oracleOp f φ (some x,z,w) = φ (some x,z-f x,w) := by
  rfl
omit [DecidableEq X] [DecidableEq R] [DecidableEq W] in
lemma oracle_none (f : X → R) (φ : State X R W) (z : R) (w : W) :
    oracleOp f φ (none,z,w) = φ (none,z,w) := by
  rfl

lemma norm_sub_sq (a b : ℂ) : ‖a-b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have h := norm_sub_le a b
  nlinarith [norm_nonneg (a-b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖-‖b‖)]

omit [Fintype X] [DecidableEq X] [DecidableEq R] [DecidableEq W] in
lemma answer_translate (φ : State X R W) (y : X) (r : R) :
    (∑ z : R, ∑ w : W, ‖φ (some y,z-r,w)‖^2) = queryMag y φ := by
  unfold queryMag
  exact Fintype.sum_equiv (Equiv.subRight r) _ _ (fun _ => rfl)

omit [DecidableEq R] [DecidableEq W] in
lemma oracle_change_sq (f : X → R) (y : X) (r : R) (φ : State X R W) :
    ‖oracleOp f φ-oracleOp (Function.update f y r) φ‖^2 ≤ 4*queryMag y φ := by
  have he : ‖oracleOp f φ-oracleOp (Function.update f y r) φ‖^2 =
      ∑ z : R, ∑ w : W, ‖φ (some y,z-f y,w)-φ (some y,z-r,w)‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fintype.sum_prod_type, PiLp.sub_apply, Fintype.sum_option]
    simp only [oracle_none, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sum_const_zero, zero_add, oracle_some]
    rw [sum_eq_single y]
    · simp
    · intro x _ hxy
      simp [Function.update_of_ne hxy]
    · simp
  rw [he]
  calc
    _ ≤ ∑ z : R, ∑ w : W, (2*‖φ (some y,z-f y,w)‖^2+2*‖φ (some y,z-r,w)‖^2) := by
      apply sum_le_sum; intro z _; apply sum_le_sum; intro w _; exact norm_sub_sq _ _
    _ = 4*queryMag y φ := by
      simp_rw [sum_add_distrib, ← mul_sum]
      rw [answer_translate, answer_translate]
      ring

lemma measurement_bound {ι : Type} [Fintype ι] (u v : EuclideanSpace ℂ ι)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (S : Finset ι) :
    |(∑ c∈S, ‖u c‖^2)-(∑ c∈S, ‖v c‖^2)| ≤ 4*‖u-v‖ := by
  let a := fun c => ‖u c-v c‖
  let b := fun c => ‖u c‖+‖v c‖
  have hab : ∀ c, |‖u c‖^2-‖v c‖^2| ≤ a c*b c := by
    intro c
    have hf : ‖u c‖^2-‖v c‖^2 = (‖u c‖-‖v c‖)*(‖u c‖+‖v c‖) := by ring
    rw [hf,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le _ _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have htotal : |(∑ c∈S, ‖u c‖^2)-(∑ c∈S, ‖v c‖^2)| ≤ ∑ c,a c*b c := by
    rw [← sum_sub_distrib]
    exact (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (fun c _ => hab c)).trans
      (sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun c _ _ => mul_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)))))
  have ha : (∑ c,a c^2)=‖u-v‖^2 := by simp [a,EuclideanSpace.norm_sq_eq,PiLp.sub_apply]
  have hb : (∑ c,b c^2)≤4 := by
    calc
      _ ≤ ∑ c,(2*‖u c‖^2+2*‖v c‖^2) := by
        apply sum_le_sum; intro c _; dsimp [b]; nlinarith [sq_nonneg (‖u c‖-‖v c‖)]
      _ = 4 := by rw [sum_add_distrib,←mul_sum,←mul_sum,←EuclideanSpace.norm_sq_eq,←EuclideanSpace.norm_sq_eq,hu,hv]; norm_num
  have hc := sum_mul_sq_le_sq_mul_sq (univ : Finset ι) a b
  rw [ha] at hc
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖u-v‖)
  have hn : 0 ≤ ∑ c,a c*b c := sum_nonneg fun c _ => mul_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have hlin : (∑ c,a c*b c)≤2*‖u-v‖ := by nlinarith [norm_nonneg (u-v)]
  exact htotal.trans (hlin.trans (by nlinarith [norm_nonneg (u-v)]))
end BQProof

noncomputable section
open Classical Finset BBBV.RandomOracle
namespace BQProof
variable {X R W : Type} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
  [AddCommGroup R] [Fintype W] [DecidableEq W] {T : ℕ}

lemma state_norm (M : QueryAlg X R W T) (g : Fin T → X → R) (i : ℕ) :
    ‖state M g i‖=1 := by
  induction i with
  | zero => exact M.init_norm
  | succ i ih =>
    simp only [state]
    split_ifs <;> simp [ih]

omit [Fintype X] [DecidableEq X] [DecidableEq R] [DecidableEq W] [AddCommGroup R] in
lemma queryMag_nonneg (y : X) (φ : State X R W) : 0≤queryMag y φ := by
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq X] [DecidableEq R] [DecidableEq W] [AddCommGroup R] in
lemma queryMag_sum_le (φ : State X R W) : (∑ y,queryMag y φ)≤‖φ‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type,Fintype.sum_option,queryMag]
  exact le_add_of_nonneg_left (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)

lemma time_query_mass (M : QueryAlg X R W T) (A : X → R) :
    (∑ t : Fin T, ∑ y,queryMag y (state M (fun _=>A) t.val))≤(T:ℝ) := by
  calc
    _ ≤ ∑ t : Fin T,(1:ℝ) := by
      apply sum_le_sum; intro t _
      simpa [state_norm] using queryMag_sum_le (state M (fun _=>A) t.val)
    _ = T := by simp

lemma fails_close {n : ℕ} {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    (M : QueryAlg (Str n) (Str n) W T) (A : Str n → Str n)
    (hA : NoInverse A) (y : Str n)
    (h : ‖final M (fun _=>A)-final M (fun _=>Function.update A y (ones n))‖≤1/13) :
    ¬(Decides M (fun _=>A) (∃ x,A x=ones n) ∧
      Decides M (fun _=>Function.update A y (ones n))
        (∃ x,Function.update A y (ones n) x=ones n)) := by
  rintro ⟨ha,hb⟩
  have hno : ¬∃ x,A x=ones n := by rintro ⟨x,hx⟩; exact hA x hx
  have hyes : ∃ x,Function.update A y (ones n) x=ones n := ⟨y,Function.update_self ..⟩
  have hlo := hb.1 hyes
  have hhi := ha.2 hno
  have hm := measurement_bound (final M (fun _=>A))
    (final M (fun _=>Function.update A y (ones n)))
    (state_norm M _ T) (state_norm M _ T) M.accept
  change |acceptProb M (fun _=>A)-acceptProb M (fun _=>Function.update A y (ones n))|≤_ at hm
  have hh := (abs_le.mp hm).1
  linarith
end BQProof

noncomputable section
open Classical Finset BBBV.RandomOracle
namespace BQProof
variable {X R W : Type} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
  [AddCommGroup R] [Fintype W] [DecidableEq W] {T : ℕ}
omit [DecidableEq R] [DecidableEq W] in
lemma oracle_change_le (f : X → R) (y : X) (r : R) (φ : State X R W) :
    ‖oracleOp f φ-oracleOp (Function.update f y r) φ‖ ≤ 2*Real.sqrt (queryMag y φ) := by
  have h := oracle_change_sq f y r φ
  have hs := Real.sq_sqrt (queryMag_nonneg y φ)
  nlinarith [Real.sqrt_nonneg (queryMag y φ),norm_nonneg (oracleOp f φ-oracleOp (Function.update f y r) φ)]
lemma hybrid_prefix (M : QueryAlg X R W T) (A : X → R) (y : X) (r : R)
    (i : ℕ) (hi : i≤T) :
    ‖state M (fun _=>A) i-state M (fun _=>Function.update A y r) i‖ ≤
      2*∑ t∈range i,Real.sqrt (queryMag y (state M (fun _=>A) t)) := by
  induction i with
  | zero => simp [state]
  | succ i ih =>
    have hit : i<T := by omega
    have ih' := ih (by omega)
    simp only [state, dif_pos hit]
    rw [← map_sub, (M.U ⟨i,hit⟩).norm_map]
    have ht := norm_sub_le_norm_sub_add_norm_sub (oracleOp A (state M (fun _=>A) i))
      (oracleOp (Function.update A y r) (state M (fun _=>A) i))
      (oracleOp (Function.update A y r) (state M (fun _=>Function.update A y r) i))
    rw [← map_sub, (oracleOp (Function.update A y r)).norm_map] at ht
    have hc := oracle_change_le A y r (state M (fun _=>A) i)
    rw [sum_range_succ]
    linarith
lemma single_update_sq (M : QueryAlg X R W T) (A : X → R) (y : X) (r : R) :
    ‖final M (fun _=>A)-final M (fun _=>Function.update A y r)‖^2 ≤
      4*(T:ℝ)*∑ t : Fin T,queryMag y (state M (fun _=>A) t.val) := by
  have h := hybrid_prefix M A y r T le_rfl
  rw [← Fin.sum_univ_eq_sum_range] at h
  have hc := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin T))
    (fun _=>(1:ℝ)) (fun t=>Real.sqrt (queryMag y (state M (fun _=>A) t.val)))
  simp only [one_mul,one_pow,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hc
  simp_rw [Real.sq_sqrt (queryMag_nonneg _ _)] at hc
  have hn : 0≤∑ t : Fin T,Real.sqrt (queryMag y (state M (fun _=>A) t.val)) := sum_nonneg fun _ _=>Real.sqrt_nonneg _
  change ‖final M (fun _=>A)-final M (fun _=>Function.update A y r)‖≤_ at h
  nlinarith [norm_nonneg (final M (fun _=>A)-final M (fun _=>Function.update A y r))]
lemma sum_update_sq (M : QueryAlg X R W T) (A : X → R) (r : R) :
    (∑ y,‖final M (fun _=>A)-final M (fun _=>Function.update A y r)‖^2)≤4*(T:ℝ)^2 := by
  calc
    _ ≤ ∑ y,4*(T:ℝ)*∑ t : Fin T,queryMag y (state M (fun _=>A) t.val) := sum_le_sum fun y _=>single_update_sq M A y r
    _ = 4*(T:ℝ)*∑ t : Fin T,∑ y,queryMag y (state M (fun _=>A) t.val) := by rw [← mul_sum,sum_comm]
    _ ≤ 4*(T:ℝ)*(T:ℝ) := mul_le_mul_of_nonneg_left (time_query_mass M A) (by positivity)
    _ = _ := by ring
lemma many_bad_updates {n : ℕ} {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    (M : QueryAlg (Str n) (Str n) W T) (hn : 1≤n)
    (hT : (T:ℝ)≤(1/100)*Real.sqrt (2^n)) (A : Str n → Str n)
    (hA : NoInverse A) (hdec : Decides M (fun _=>A) (∃ x,A x=ones n)) :
    2^(n-1) ≤ (univ.filter fun y : Str n => ¬ Decides M
      (fun _=>Function.update A y (ones n)) (∃ x,Function.update A y (ones n) x=ones n)).card := by
  let d := fun y : Str n => ‖final M (fun _=>A)-final M (fun _=>Function.update A y (ones n))‖
  let bad := univ.filter fun y => (1/13:ℝ)<d y
  let close := univ.filter fun y => d y≤(1/13:ℝ)
  have hsum := sum_update_sq M A (ones n)
  change (∑ y,d y^2)≤4*(T:ℝ)^2 at hsum
  have hb : (bad.card:ℝ)/169 ≤ ∑ y,d y^2 := by
    calc
      _ = ∑ y∈bad,(1/169:ℝ) := by simp [div_eq_mul_inv]
      _ ≤ ∑ y∈bad,d y^2 := by
        apply sum_le_sum; intro y hy
        have hd := (mem_filter.mp hy).2
        dsimp [bad] at hy
        change (1/13:ℝ)<d y at hd
        nlinarith
      _ ≤ ∑ y,d y^2 := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>sq_nonneg _)
  have hs := Real.sq_sqrt (show (0:ℝ)≤2^n by positivity)
  have ht0 : (0:ℝ)≤T := Nat.cast_nonneg _
  have ht : (T:ℝ)^2≤(2:ℝ)^n/10000 := by nlinarith [Real.sqrt_nonneg ((2:ℝ)^n)]
  have hbc : (bad.card:ℝ)≤(2:ℝ)^n/2 := by nlinarith
  have heq : (2:ℕ)^n=2*2^(n-1) := by
    conv_lhs => rw [show n=(n-1)+1 by omega]
    rw [pow_succ]; omega
  have hbcard : bad.card≤2^(n-1) := by
    have heqr : (2:ℝ)^n=2*(2:ℝ)^(n-1) := by exact_mod_cast heq
    rw [heqr] at hbc
    exact_mod_cast (show (bad.card:ℝ)≤(2:ℝ)^(n-1) by linarith)
  have hcards : bad.card+close.card=2^n := by
    have hh := card_filter_add_card_filter_not (s:=(univ : Finset (Str n))) (fun y=>(1/13:ℝ)<d y)
    simpa [bad,close,not_lt,Str] using hh
  have hc : 2^(n-1)≤close.card := by omega
  apply hc.trans
  apply card_le_card
  intro y hy
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  intro hgood
  exact fails_close M A hA y (mem_filter.mp hy).2 ⟨hdec,hgood⟩
end BQProof

set_option autoImplicit false
open scoped BigOperators
open Finset BBBV.RandomOracle
namespace BQProof
attribute [local instance] Classical.propDecidable
 theorem update_unique {n : ℕ} {A : Str n → Str n} (hA : NoInverse A) (y : Str n) :
    UniqueInverse (Function.update A y (ones n)) := by
  refine ⟨y, by simp, ?_⟩
  intro z hz
  by_contra h
  exact hA z (by simpa [Function.update_of_ne h] using hz)
 theorem failure_count (n : ℕ) (hn : 1 ≤ n) (Good : (Str n → Str n) → Prop)
    (h : ∀ A, NoInverse A → Good A → 2^(n-1) ≤
      (univ.filter fun y => ¬ Good (Function.update A y (ones n))).card) :
    (univ.filter (NoInverse (n:=n))).card ≤
      2*(univ.filter fun A => ¬ Good A).card := by
  classical
  let G := {A : Str n → Str n // NoInverse A ∧ Good A}
  let B := {A : Str n → Str n // UniqueInverse A ∧ ¬ Good A}
  let P := (Σ A : G, {y : Str n // ¬ Good (Function.update A.val y (ones n))})
  let f : P → B × Str n := fun p =>
    (⟨Function.update p.1.val p.2.val (ones n), update_unique p.1.property.1 p.2.val,
      p.2.property⟩, p.1.val p.2.val)
  have hf : Function.Injective f := by
    intro p q hpq
    have he : Function.update p.1.val p.2.val (ones n) =
        Function.update q.1.val q.2.val (ones n) := congrArg (fun z : B × Str n => z.1.val) hpq
    have hv : p.1.val p.2.val = q.1.val q.2.val := congrArg Prod.snd hpq
    have hy : p.2.val = q.2.val := by
      have hu := update_unique q.1.property.1 q.2.val
      exact hu.unique (by rw [← he]; simp) (by simp)
    have ha : p.1.val = q.1.val := by
      funext x
      by_cases hx : x = p.2.val
      · subst x
        simpa only [hy] using hv
      · have hxq : x ≠ q.2.val := by simpa only [← hy] using hx
        simpa [Function.update_of_ne hx, Function.update_of_ne hxq] using congrFun he x
    cases p with
    | mk a y =>
      cases q with
      | mk b z =>
        have hab : a = b := Subtype.ext ha
        subst b
        have hyz : y = z := Subtype.ext hy
        subst z
        rfl
  have hcard : Fintype.card P ≤ Fintype.card B * (2^n) := by
    have hc := Fintype.card_le_of_injective f hf
    simpa [Fintype.card_prod, Str] using hc
  have hlow : Fintype.card G * (2^(n-1)) ≤ Fintype.card P := by
    rw [Fintype.card_sigma]
    calc
      Fintype.card G * 2^(n-1) = ∑ _a : G, 2^(n-1) := by simp
      _ ≤ ∑ a : G, Fintype.card {y : Str n // ¬ Good (Function.update a.val y (ones n))} := by
        apply sum_le_sum
        intro a _
        simpa only [Fintype.card_subtype] using h a.val a.property.1 a.property.2
  have hp : 0 < (2:ℕ)^(n-1) := pow_pos (by omega) _
  have heq : (2:ℕ)^n = 2 * 2^(n-1) := by
    conv_lhs => rw [show n = (n-1)+1 by omega]
    rw [pow_succ]; omega
  have hgb : Fintype.card G ≤ 2*Fintype.card B := by
    rw [heq] at hcard
    nlinarith
  let NG := univ.filter fun A : Str n → Str n => NoInverse A ∧ ¬ Good A
  let BG := univ.filter fun A : Str n → Str n => UniqueInverse A ∧ ¬ Good A
  have hd : Disjoint NG BG := by
    rw [disjoint_left]
    intro A ha hb
    have ha' : NoInverse A := (mem_filter.1 ha).2.1
    obtain ⟨y,hy,_⟩ := (mem_filter.1 hb).2.1
    exact ha' y hy
  have hu : NG ∪ BG ⊆ univ.filter fun A : Str n → Str n => ¬Good A := by
    intro A ha
    rcases mem_union.1 ha with ha | ha <;> exact mem_filter.2 ⟨mem_univ _,(mem_filter.1 ha).2.2⟩
  have hsum : NG.card + BG.card ≤ (univ.filter fun A : Str n → Str n => ¬Good A).card := by
    rw [← card_union_of_disjoint hd]
    exact card_le_card hu
  have hbcard : Fintype.card B = BG.card := by simp [B, BG, Fintype.card_subtype]
  have hsplit : (univ.filter (NoInverse (n:=n))).card = Fintype.card G + NG.card := by
    have hc := card_filter_add_card_filter_not (s:=univ.filter (NoInverse (n:=n))) Good
    simpa [filter_filter, G, NG, Fintype.card_subtype] using hc.symm
  rw [hbcard] at hgb
  rw [hsplit]
  omega
end BQProof

set_option autoImplicit false
open scoped BigOperators
open Finset Filter Topology BBBV.RandomOracle
namespace BQProof
attribute [local instance] Classical.propDecidable
 theorem card_str (n : ℕ) : Fintype.card (Str n) = 2 ^ n := by
  simp [Str]
 theorem card_nohit (n : ℕ) :
    (univ.filter (NoInverse (n := n))).card = (2 ^ n - 1) ^ (2 ^ n) := by
  classical
  have hs : univ.filter (NoInverse (n := n)) =
      Fintype.piFinset (fun _ : Str n => univ.erase (ones n)) := by
    ext A
    simp [NoInverse]
  rw [hs, Fintype.card_piFinset]
  simp
 theorem nohit_fraction (n : ℕ) (_hn : 1 ≤ n) :
    ((univ.filter (NoInverse (n := n))).card : ℝ) /
      (Fintype.card (Str n → Str n) : ℝ) = (1 - 1 / (2 : ℝ)^n) ^ (2^n) := by
  classical
  rw [card_nohit, Fintype.card_fun, card_str]
  have hp : 1 ≤ (2 : ℕ)^n := Nat.one_le_pow n 2 (by omega)
  push_cast [Nat.cast_sub hp]
  rw [← div_pow]
  congr 1
  field_simp
 theorem exists_nohit_threshold : ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    (1/4 : ℝ) ≤ ((univ.filter (NoInverse (n := n))).card : ℝ) /
      (Fintype.card (Str n → Str n) : ℝ) := by
  have ht : Tendsto (fun n : ℕ => (2 : ℕ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hl := (Real.tendsto_one_add_div_pow_exp (-1)).comp ht
  have he : (1/4 : ℝ) < Real.exp (-1) := by
    rw [Real.exp_neg]
    have hp := Real.exp_pos 1
    have hb := Real.exp_one_lt_three
    rw [show (Real.exp 1)⁻¹ = 1 / Real.exp 1 by simp]
    apply (div_lt_div_iff₀ (by norm_num : (0:ℝ)<4) hp).2
    linarith
  have hev : ∀ᶠ n : ℕ in atTop, (1/4 : ℝ) <
      (1 + (-1 : ℝ) / ((2 : ℕ)^n : ℝ)) ^ (2^n) :=
    by simpa only [Function.comp_apply, Nat.cast_pow] using hl.eventually (eventually_gt_nhds he)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨max N 1, le_max_right _ _, fun n hn => ?_⟩
  rw [nohit_fraction n (le_trans (le_max_right _ _) hn)]
  simpa only [Nat.cast_pow, Nat.cast_ofNat, neg_div, one_div, sub_eq_add_neg] using
    (hN n (le_trans (le_max_left _ _) hn)).le
end BQProof

noncomputable section
namespace BBBV.RandomOracle

open Classical in
theorem theorem_3_5 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (T : ℕ), (T : ℝ) ≤ c * Real.sqrt (2 ^ n) →
      ∀ M : QueryAlg (Str n) (Str n) W T,
        (1 / 8 : ℝ) ≤
          ((Finset.univ.filter fun A : Str n → Str n =>
              ¬ Decides M (fun _ => A) (∃ x, A x = ones n)).card : ℝ) /
            (Fintype.card (Str n → Str n) : ℝ) := by
  obtain ⟨N,hN,hfrac⟩ := BQProof.exists_nohit_threshold
  refine ⟨1/100,by norm_num,N,?_⟩
  intro n hn W _ _ T hT M
  have hn1 : 1≤n := hN.trans hn
  have hc := BQProof.failure_count n hn1
    (fun A=>Decides M (fun _=>A) (∃ x,A x=ones n))
    (fun A hA hgood=>BQProof.many_bad_updates M hn1 hT A hA hgood)
  have hcr : ((Finset.univ.filter (NoInverse (n:=n))).card:ℝ) ≤
      2*((Finset.univ.filter fun A : Str n → Str n => ¬Decides M (fun _=>A) (∃ x,A x=ones n)).card:ℝ) := by exact_mod_cast hc
  have hp : (0:ℝ)<Fintype.card (Str n → Str n) := by exact_mod_cast Fintype.card_pos
  have hf := hfrac n hn
  rw [le_div_iff₀ hp] at hf ⊢
  linarith

end BBBV.RandomOracle

open Classical BBBV.RandomOracle in
theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (T : ℕ), (T : ℝ) ≤ c * Real.sqrt (2 ^ n) →
      ∀ M : QueryAlg (Str n) (Str n) W T,
        (1 / 8 : ℝ) ≤
          ((Finset.univ.filter fun A : Str n → Str n =>
              ¬ Decides M (fun _ => A) (∃ x, A x = ones n)).card : ℝ) /
            (Fintype.card (Str n → Str n) : ℝ) := BBBV.RandomOracle.theorem_3_5

