-- Prove2me | solution 1 for FourExp.norm_to_polynomial_alg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T13:31:38.430934+00:00
-- url     : https://prove2.me/submissions/7e5bc291-7d8f-41a4-ad91-cd8dbf87b1f8

import Mathlib

open Finset

namespace FourExpAux

/-- The exponential polynomial with coefficients indexed by `ℕ`; only `i < S` is used. -/
noncomputable def expP (S T : ℕ) (β : Fin T → Fin T → ℂ) (c : ℕ → Fin T → Fin T → ℂ) (z : ℂ) : ℂ :=
  ∑ i ∈ range S, ∑ j : Fin T, ∑ k : Fin T, c i j k * z ^ i * Complex.exp (β j k * z)

/-- One differentiation step on the coefficients. -/
noncomputable def dstep (S T : ℕ) (β : Fin T → Fin T → ℂ) (c : ℕ → Fin T → Fin T → ℂ) :
    ℕ → Fin T → Fin T → ℂ :=
  fun i j k => (if i + 1 < S then ((i : ℂ) + 1) * c (i + 1) j k else 0) + β j k * c i j k

lemma hasDerivAt_finsum' {ι : Type*} (s : Finset ι) (g g' : ι → ℂ → ℂ) (z : ℂ)
    (h : ∀ i, HasDerivAt (g i) (g' i z) z) :
    HasDerivAt (fun y => ∑ i ∈ s, g i y) (∑ i ∈ s, g' i z) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDerivAt_const z (0 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a).add ih

lemma hasDerivAt_term (a β z : ℂ) (i : ℕ) :
    HasDerivAt (fun y => a * y ^ i * Complex.exp (β * y))
      (a * ((i : ℂ) * z ^ (i - 1)) * Complex.exp (β * z) + a * z ^ i * (Complex.exp (β * z) * β)) z := by
  have h1 : HasDerivAt (fun y => a * y ^ i) (a * ((i : ℂ) * z ^ (i - 1))) z :=
    (hasDerivAt_pow i z).const_mul a
  have h2 : HasDerivAt (fun y => Complex.exp (β * y)) (Complex.exp (β * z) * β) z := by
    simpa using ((hasDerivAt_id z).const_mul β).cexp
  exact h1.mul h2

/-- The shift identity behind one differentiation step. -/
lemma shift_sum (S : ℕ) (f : ℕ → ℂ) (w : ℕ → ℂ) :
    ∑ i ∈ range S, f i * ((i : ℂ) * w (i - 1))
      = ∑ i ∈ range S, (if i + 1 < S then ((i : ℂ) + 1) * f (i + 1) else 0) * w i := by
  rcases S with _ | n
  · simp
  · rw [Finset.sum_range_succ', Finset.sum_range_succ]
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, lt_self_iff_false, if_false, zero_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i + 1 < n + 1 := by simpa using hi
    rw [if_pos hi']
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

lemma deriv_expP (S T : ℕ) (β : Fin T → Fin T → ℂ) (c : ℕ → Fin T → Fin T → ℂ) :
    deriv (expP S T β c) = expP S T β (dstep S T β c) := by
  funext z
  have hd : HasDerivAt (expP S T β c)
      (∑ i ∈ range S, ∑ j : Fin T, ∑ k : Fin T,
        (c i j k * ((i : ℂ) * z ^ (i - 1)) * Complex.exp (β j k * z)
          + c i j k * z ^ i * (Complex.exp (β j k * z) * β j k))) z := by
    unfold expP
    refine hasDerivAt_finsum' (range S)
      (fun i y => ∑ j : Fin T, ∑ k : Fin T, c i j k * y ^ i * Complex.exp (β j k * y))
      (fun i y => ∑ j : Fin T, ∑ k : Fin T,
        (c i j k * ((i : ℂ) * y ^ (i - 1)) * Complex.exp (β j k * y)
          + c i j k * y ^ i * (Complex.exp (β j k * y) * β j k))) z fun i => ?_
    refine hasDerivAt_finsum' Finset.univ
      (fun j y => ∑ k : Fin T, c i j k * y ^ i * Complex.exp (β j k * y))
      (fun j y => ∑ k : Fin T,
        (c i j k * ((i : ℂ) * y ^ (i - 1)) * Complex.exp (β j k * y)
          + c i j k * y ^ i * (Complex.exp (β j k * y) * β j k))) z fun j => ?_
    refine hasDerivAt_finsum' Finset.univ
      (fun k y => c i j k * y ^ i * Complex.exp (β j k * y))
      (fun k y => c i j k * ((i : ℂ) * y ^ (i - 1)) * Complex.exp (β j k * y)
          + c i j k * y ^ i * (Complex.exp (β j k * y) * β j k)) z fun k => ?_
    exact hasDerivAt_term _ _ z i
  rw [hd.deriv]
  unfold expP dstep
  simp only [Finset.sum_add_distrib]
  have hA : ∑ i ∈ range S, ∑ j : Fin T, ∑ k : Fin T,
        c i j k * ((i : ℂ) * z ^ (i - 1)) * Complex.exp (β j k * z)
      = ∑ i ∈ range S, ∑ j : Fin T, ∑ k : Fin T,
        (if i + 1 < S then ((i : ℂ) + 1) * c (i + 1) j k else 0) * z ^ i * Complex.exp (β j k * z) := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := shift_sum S (fun i => c i j k * Complex.exp (β j k * z)) (fun i => z ^ i)
    calc ∑ i ∈ range S, c i j k * ((i : ℂ) * z ^ (i - 1)) * Complex.exp (β j k * z)
        = ∑ i ∈ range S, (c i j k * Complex.exp (β j k * z)) * ((i : ℂ) * z ^ (i - 1)) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i ∈ range S, (if i + 1 < S then ((i : ℂ) + 1) * (c (i + 1) j k * Complex.exp (β j k * z)) else 0) * z ^ i := this
      _ = _ := Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
  rw [hA, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma iteratedDeriv_expP (S T : ℕ) (β : Fin T → Fin T → ℂ) :
    ∀ (m : ℕ) (c : ℕ → Fin T → Fin T → ℂ),
      iteratedDeriv m (expP S T β c) = expP S T β ((dstep S T β)^[m] c)
  | 0, c => by simp
  | m + 1, c => by
    rw [iteratedDeriv_succ', deriv_expP, iteratedDeriv_expP S T β m, Function.iterate_succ_apply]

section Majorant

open Polynomial

/-- `ph` majorizes `p` coefficientwise. -/
def Maj1 (p : ℤ[X]) (ph : ℕ[X]) : Prop := ∀ i, (p.coeff i).natAbs ≤ ph.coeff i

lemma maj1_zero : Maj1 0 0 := fun i => by simp

lemma maj1_add {p q : ℤ[X]} {ph qh : ℕ[X]} (hp : Maj1 p ph) (hq : Maj1 q qh) :
    Maj1 (p + q) (ph + qh) := fun i => by
  simp only [coeff_add]
  exact (Int.natAbs_add_le _ _).trans (add_le_add (hp i) (hq i))

lemma maj1_neg {p : ℤ[X]} {ph : ℕ[X]} (hp : Maj1 p ph) : Maj1 (-p) ph := fun i => by
  simpa using hp i

lemma maj1_sub {p q : ℤ[X]} {ph qh : ℕ[X]} (hp : Maj1 p ph) (hq : Maj1 q qh) :
    Maj1 (p - q) (ph + qh) := by
  rw [sub_eq_add_neg]; exact maj1_add hp (maj1_neg hq)

lemma maj1_mul {p q : ℤ[X]} {ph qh : ℕ[X]} (hp : Maj1 p ph) (hq : Maj1 q qh) :
    Maj1 (p * q) (ph * qh) := fun n => by
  rw [coeff_mul, coeff_mul]
  refine (Int.natAbs_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul (hp _) (hq _)

lemma maj1_C (a : ℤ) : Maj1 (C a) (C a.natAbs) := fun i => by
  rw [coeff_C, coeff_C]; split_ifs <;> simp

lemma maj1_X : Maj1 X X := fun i => by
  rw [coeff_X, coeff_X]; split_ifs <;> simp

lemma maj1_one : Maj1 1 1 := by simpa using maj1_C 1

lemma maj1_pow {p : ℤ[X]} {ph : ℕ[X]} (hp : Maj1 p ph) : ∀ n : ℕ, Maj1 (p ^ n) (ph ^ n)
  | 0 => by simpa using maj1_one
  | n + 1 => by rw [pow_succ, pow_succ]; exact maj1_mul (maj1_pow hp n) hp

lemma maj1_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) (g : ι → ℕ[X])
    (h : ∀ i ∈ s, Maj1 (f i) (g i)) : Maj1 (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using maj1_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact maj1_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma coeff_le_eval_one (q : ℕ[X]) (i : ℕ) : q.coeff i ≤ q.eval 1 := by
  rw [eval_eq_sum_range]
  simp only [one_pow, mul_one]
  by_cases hi : i ≤ q.natDegree
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact Nat.zero_le _

lemma maj1_natDegree {p : ℤ[X]} {ph : ℕ[X]} (hp : Maj1 p ph) : p.natDegree ≤ ph.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  have := hp i
  rw [coeff_eq_zero_of_natDegree_lt hi] at this
  exact Int.natAbs_eq_zero.1 (Nat.le_zero.1 this)

/-- `Ph` majorizes `P` coefficientwise in both variables. -/
def Maj2 (P : ℤ[X][X]) (Ph : ℕ[X][X]) : Prop := ∀ k, Maj1 (P.coeff k) (Ph.coeff k)

lemma maj2_zero : Maj2 0 0 := fun k => by simpa using maj1_zero

lemma maj2_add {P Q : ℤ[X][X]} {Ph Qh : ℕ[X][X]} (hP : Maj2 P Ph) (hQ : Maj2 Q Qh) :
    Maj2 (P + Q) (Ph + Qh) := fun k => by
  simp only [coeff_add]; exact maj1_add (hP k) (hQ k)

lemma maj2_neg {P : ℤ[X][X]} {Ph : ℕ[X][X]} (hP : Maj2 P Ph) : Maj2 (-P) Ph := fun k => by
  simpa using maj1_neg (hP k)

lemma maj2_sub {P Q : ℤ[X][X]} {Ph Qh : ℕ[X][X]} (hP : Maj2 P Ph) (hQ : Maj2 Q Qh) :
    Maj2 (P - Q) (Ph + Qh) := by
  rw [sub_eq_add_neg]; exact maj2_add hP (maj2_neg hQ)

lemma maj2_mul {P Q : ℤ[X][X]} {Ph Qh : ℕ[X][X]} (hP : Maj2 P Ph) (hQ : Maj2 Q Qh) :
    Maj2 (P * Q) (Ph * Qh) := fun n => by
  rw [coeff_mul, coeff_mul]
  exact maj1_sum _ _ _ fun x _ => maj1_mul (hP _) (hQ _)

lemma maj2_C {p : ℤ[X]} {ph : ℕ[X]} (hp : Maj1 p ph) : Maj2 (C p) (C ph) := fun k => by
  rw [coeff_C, coeff_C]; split_ifs
  · exact hp
  · exact maj1_zero

lemma maj2_X : Maj2 X X := fun k => by
  rw [coeff_X, coeff_X]; split_ifs
  · exact maj1_one
  · exact maj1_zero

lemma maj2_one : Maj2 1 1 := by simpa using maj2_C maj1_one

lemma maj2_pow {P : ℤ[X][X]} {Ph : ℕ[X][X]} (hP : Maj2 P Ph) : ∀ n : ℕ, Maj2 (P ^ n) (Ph ^ n)
  | 0 => by simpa using maj2_one
  | n + 1 => by rw [pow_succ, pow_succ]; exact maj2_mul (maj2_pow hP n) hP

lemma maj2_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ[X][X]) (g : ι → ℕ[X][X])
    (h : ∀ i ∈ s, Maj2 (f i) (g i)) : Maj2 (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using maj2_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact maj2_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The double evaluation at `1`, a bound for every coefficient. -/
noncomputable def E2 (Ph : ℕ[X][X]) : ℕ := (Ph.map (evalRingHom 1)).eval 1

lemma E2_mul (Ph Qh : ℕ[X][X]) : E2 (Ph * Qh) = E2 Ph * E2 Qh := by
  simp [E2, Polynomial.map_mul]

lemma E2_add (Ph Qh : ℕ[X][X]) : E2 (Ph + Qh) = E2 Ph + E2 Qh := by
  simp [E2, Polynomial.map_add]

lemma E2_pow (Ph : ℕ[X][X]) (n : ℕ) : E2 (Ph ^ n) = E2 Ph ^ n := by
  simp [E2, Polynomial.map_pow]

lemma maj2_coeff_le {P : ℤ[X][X]} {Ph : ℕ[X][X]} (hP : Maj2 P Ph) (k h : ℕ) :
    ((P.coeff k).coeff h).natAbs ≤ E2 Ph := by
  refine (hP k h).trans ((coeff_le_eval_one _ h).trans ?_)
  have := coeff_le_eval_one (Ph.map (evalRingHom 1)) k
  simpa [E2, coeff_map] using this

lemma maj2_natDegree {P : ℤ[X][X]} {Ph : ℕ[X][X]} (hP : Maj2 P Ph) : P.natDegree ≤ Ph.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  have h1 := maj1_natDegree (hP k)
  rw [coeff_eq_zero_of_natDegree_lt hk, natDegree_zero] at h1
  have h2 : ∀ i, ((P.coeff k).coeff i).natAbs ≤ 0 := fun i => by
    have := hP k i
    rwa [coeff_eq_zero_of_natDegree_lt hk, coeff_zero] at this
  ext i
  simpa using h2 i

end Majorant

section Reduction

open Polynomial

/-- Every coefficient of `Ph` has `X`-degree at most `D`. -/
def DegX (Ph : ℕ[X][X]) (D : ℕ) : Prop := ∀ k, (Ph.coeff k).natDegree ≤ D

lemma degX_mono {Ph : ℕ[X][X]} {D D' : ℕ} (h : DegX Ph D) (hD : D ≤ D') : DegX Ph D' :=
  fun k => (h k).trans hD

lemma degX_add {Ph Qh : ℕ[X][X]} {D : ℕ} (hP : DegX Ph D) (hQ : DegX Qh D) : DegX (Ph + Qh) D :=
  fun k => by rw [coeff_add]; exact (natDegree_add_le _ _).trans (max_le (hP k) (hQ k))

lemma degX_mul {Ph Qh : ℕ[X][X]} {D D' : ℕ} (hP : DegX Ph D) (hQ : DegX Qh D') :
    DegX (Ph * Qh) (D + D') := fun n => by
  rw [coeff_mul]
  refine natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
  exact (natDegree_mul_le).trans (add_le_add (hP _) (hQ _))

lemma degX_C {p : ℕ[X]} : DegX (C p) p.natDegree := fun k => by
  rw [coeff_C]; split_ifs
  · exact le_rfl
  · simp

lemma degX_X : DegX (X : ℕ[X][X]) 0 := fun k => by
  rw [coeff_X]; split_ifs <;> simp

lemma degX_one : DegX (1 : ℕ[X][X]) 0 := fun k => by
  rw [coeff_one]; split_ifs <;> simp

lemma degX_coeff {Ph : ℕ[X][X]} {D : ℕ} (h : DegX Ph D) (k : ℕ) : (Ph.coeff k).natDegree ≤ D := h k

/-- The absolute majorant of an integer polynomial. -/
noncomputable def absPoly1 (p : ℤ[X]) : ℕ[X] :=
  ∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i).natAbs * X ^ i

lemma maj1_absPoly1 (p : ℤ[X]) : Maj1 p (absPoly1 p) := fun i => by
  simp only [absPoly1, finset_sum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro hi
    rw [Finset.mem_range, not_lt] at hi
    simp [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < i)]

lemma natDegree_absPoly1 (p : ℤ[X]) : (absPoly1 p).natDegree ≤ p.natDegree := by
  unfold absPoly1
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (by simpa [Nat.lt_succ_iff] using hi)

/-- The absolute majorant of a polynomial in two variables. -/
noncomputable def absPoly2 (P : ℤ[X][X]) : ℕ[X][X] :=
  ∑ k ∈ Finset.range (P.natDegree + 1), C (absPoly1 (P.coeff k)) * X ^ k

lemma maj2_absPoly2 (P : ℤ[X][X]) : Maj2 P (absPoly2 P) := fun k => by
  simp only [absPoly2, finset_sum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k]
  · simpa using maj1_absPoly1 (P.coeff k)
  · intro b _ hb; simpa [Ne.symm hb] using maj1_zero
  · intro hk
    rw [Finset.mem_range, not_lt] at hk
    rw [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < k)]
    simp [absPoly1]

lemma degX_absPoly2 (P : ℤ[X][X]) (D : ℕ) (hD : ∀ k, (P.coeff k).natDegree ≤ D) :
    DegX (absPoly2 P) D := fun k => by
  simp only [absPoly2, finset_sum_coeff, coeff_C_mul_X_pow]
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  split_ifs
  · exact (natDegree_absPoly1 _).trans (hD _)
  · simp

variable (Q : ℤ[X][X])

/-- `Y^n` reduced modulo the monic `Q`. -/
noncomputable def redY : ℕ → ℤ[X][X]
  | 0 => 1
  | n + 1 => X * redY n - C ((redY n).coeff (Q.natDegree - 1)) * Q

lemma redY_natDegree (hQm : Q.Monic) (hd : 0 < Q.natDegree) :
    ∀ n, (redY Q n).natDegree < Q.natDegree
  | 0 => by simp [redY]; exact hd
  | n + 1 => by
    have ih := redY_natDegree hQm hd n
    show (X * redY Q n - C ((redY Q n).coeff (Q.natDegree - 1)) * Q).natDegree < Q.natDegree
    have hle : (X * redY Q n - C ((redY Q n).coeff (Q.natDegree - 1)) * Q).natDegree
        ≤ Q.natDegree - 1 := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro j hj
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [coeff_sub, coeff_X_mul, coeff_C_mul]
      rcases Nat.lt_or_ge (Q.natDegree) (j' + 1) with hgt | hle
      · rw [coeff_eq_zero_of_natDegree_lt hgt, coeff_eq_zero_of_natDegree_lt (by omega)]; simp
      · have hj' : j' + 1 = Q.natDegree := by omega
        rw [hj', hQm.coeff_natDegree, mul_one, show j' = Q.natDegree - 1 by omega, sub_self]
    omega

lemma redY_eval (φ : ℤ[X][X] →+* ℂ) (hQ : φ Q = 0) : ∀ n, φ (redY Q n) = φ X ^ n
  | 0 => by simp [redY]
  | n + 1 => by
    simp only [redY, map_sub, map_mul, hQ, mul_zero, sub_zero, redY_eval φ hQ n, pow_succ]
    ring

/-- The majorant recursion matching `redY`. -/
noncomputable def redYh (Qh : ℕ[X][X]) (d : ℕ) : ℕ → ℕ[X][X]
  | 0 => 1
  | n + 1 => X * redYh Qh d n + C ((redYh Qh d n).coeff (d - 1)) * Qh

lemma maj2_redY {Qh : ℕ[X][X]} (hQ : Maj2 Q Qh) :
    ∀ n, Maj2 (redY Q n) (redYh Qh Q.natDegree n)
  | 0 => by simpa [redY, redYh] using maj2_one
  | n + 1 => by
    have ih := maj2_redY hQ n
    exact maj2_sub (maj2_mul maj2_X ih) (maj2_mul (maj2_C (ih _)) hQ)

lemma eval_coeff_le_E2 (Ph : ℕ[X][X]) (k : ℕ) : (Ph.coeff k).eval 1 ≤ E2 Ph := by
  have := coeff_le_eval_one (Ph.map (evalRingHom 1)) k
  simpa [E2, coeff_map] using this

lemma E2_redYh (Qh : ℕ[X][X]) (d : ℕ) : ∀ n, E2 (redYh Qh d n) ≤ (1 + E2 Qh) ^ n
  | 0 => by simp [redYh, E2]
  | n + 1 => by
    have ih := E2_redYh Qh d n
    have hc := eval_coeff_le_E2 (redYh Qh d n) (d - 1)
    have hX : E2 (X : ℕ[X][X]) = 1 := by simp [E2]
    have hC : E2 (C ((redYh Qh d n).coeff (d - 1))) = ((redYh Qh d n).coeff (d - 1)).eval 1 := by
      simp [E2]
    calc E2 (redYh Qh d (n + 1))
        = E2 (redYh Qh d n) + ((redYh Qh d n).coeff (d - 1)).eval 1 * E2 Qh := by
          simp only [redYh, E2_add, E2_mul, hX, hC, one_mul]
      _ ≤ E2 (redYh Qh d n) + E2 (redYh Qh d n) * E2 Qh := by gcongr
      _ = E2 (redYh Qh d n) * (1 + E2 Qh) := by ring
      _ ≤ (1 + E2 Qh) ^ n * (1 + E2 Qh) := by gcongr
      _ = (1 + E2 Qh) ^ (n + 1) := (pow_succ _ _).symm

lemma degX_redYh {Qh : ℕ[X][X]} {DQ : ℕ} (hQ : DegX Qh DQ) (d : ℕ) :
    ∀ n, DegX (redYh Qh d n) (n * DQ)
  | 0 => by simpa [redYh] using degX_one
  | n + 1 => by
    have ih := degX_redYh hQ d n
    have h1 : DegX (X * redYh Qh d n) (n * DQ) := by simpa using degX_mul degX_X ih
    have h2 : DegX (C ((redYh Qh d n).coeff (d - 1)) * Qh) (n * DQ + DQ) :=
      degX_mul (degX_mono degX_C (ih _)) hQ
    exact degX_add (degX_mono h1 (by nlinarith)) (degX_mono h2 (by rw [Nat.succ_mul]))

end Reduction

section Algebraic

open Polynomial

lemma maj1_C_le {c : ℤ} {ch : ℕ} (h : c.natAbs ≤ ch) : Maj1 (C c) (C ch) := fun i => by
  rw [coeff_C, coeff_C]; split_ifs
  · exact h
  · simp

/-- A rational polynomial becomes integral after multiplying by a positive integer. -/
lemma exists_int_scaled' (p : ℚ[X]) :
    ∃ n : ℕ, 0 < n ∧ ∃ q : ℤ[X], q.map (Int.castRingHom ℚ) = C (n : ℚ) * p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨n₁, hn₁, q₁, e₁⟩ := hp
    obtain ⟨n₂, hn₂, q₂, e₂⟩ := hq
    refine ⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂, C (n₂ : ℤ) * q₁ + C (n₁ : ℤ) * q₂, ?_⟩
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, e₁, e₂]
    simp only [eq_intCast, Int.cast_natCast, Nat.cast_mul, C_mul]
    ring
  | monomial k a =>
    refine ⟨a.den, a.den_pos, monomial k a.num, ?_⟩
    rw [Polynomial.map_monomial, C_mul_monomial]
    congr 1
    simp [Rat.mul_den_eq_num]

/-- An algebraic number has a non-constant integer annihilator. -/
lemma exists_int_annihilator {α : ℂ} (h : IsAlgebraic ℚ α) :
    ∃ m : ℤ[X], 0 < m.natDegree ∧ aeval α m = 0 := by
  obtain ⟨p, hp0, hpα⟩ := h
  obtain ⟨n, hn, q, hq⟩ := exists_int_scaled' p
  have hqα : aeval α q = 0 := by
    rw [← aeval_map_algebraMap ℚ, show algebraMap ℤ ℚ = Int.castRingHom ℚ from rfl, hq, map_mul,
      hpα, mul_zero]
  refine ⟨q, Nat.pos_of_ne_zero fun h0 => ?_, hqα⟩
  have hq0 : q ≠ 0 := by
    intro h; rw [h, Polynomial.map_zero] at hq
    exact (mul_ne_zero (by simpa using hn.ne') hp0) hq.symm
  rw [eq_C_of_natDegree_eq_zero h0, aeval_C] at hqα
  have hc : q.coeff 0 ≠ 0 := by
    intro hc; apply hq0
    rw [eq_C_of_natDegree_eq_zero h0, hc, map_zero]
  simp [hc] at hqα

variable (m : ℤ[X])

/-- `L^n X^n` reduced modulo the integer polynomial `m` with leading coefficient `L`. -/
noncomputable def redA : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => C m.leadingCoeff * X * redA n - C ((redA n).coeff (m.natDegree - 1)) * m

lemma redA_natDegree (hd : 0 < m.natDegree) : ∀ n, (redA m n).natDegree < m.natDegree
  | 0 => by simp [redA]; exact hd
  | n + 1 => by
    have ih := redA_natDegree hd n
    show (C m.leadingCoeff * X * redA m n - C ((redA m n).coeff (m.natDegree - 1)) * m).natDegree
      < m.natDegree
    have hle : (C m.leadingCoeff * X * redA m n
        - C ((redA m n).coeff (m.natDegree - 1)) * m).natDegree ≤ m.natDegree - 1 := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro j hj
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [coeff_sub, mul_assoc, coeff_C_mul, coeff_X_mul, coeff_C_mul]
      rcases Nat.lt_or_ge m.natDegree (j' + 1) with hgt | hle
      · rw [coeff_eq_zero_of_natDegree_lt hgt, coeff_eq_zero_of_natDegree_lt (by omega)]; simp
      · rw [show j' + 1 = m.natDegree by omega, coeff_natDegree, show j' = m.natDegree - 1 by omega]
        ring
    omega

lemma redA_eval {α : ℂ} (hα : aeval α m = 0) :
    ∀ n, aeval α (redA m n) = ((m.leadingCoeff : ℤ) : ℂ) ^ n * α ^ n
  | 0 => by simp [redA]
  | n + 1 => by
    simp only [redA, map_sub, map_mul, aeval_C, aeval_X, hα, mul_zero, sub_zero, redA_eval hα n,
      algebraMap_int_eq, eq_intCast, map_intCast]
    ring

/-- The majorant recursion matching `redA`. -/
noncomputable def redAh (mh : ℕ[X]) (Lh d : ℕ) : ℕ → ℕ[X]
  | 0 => 1
  | n + 1 => C Lh * X * redAh mh Lh d n + C ((redAh mh Lh d n).coeff (d - 1)) * mh

lemma maj1_redA {mh : ℕ[X]} (hm : Maj1 m mh) :
    ∀ n, Maj1 (redA m n) (redAh mh m.leadingCoeff.natAbs m.natDegree n)
  | 0 => by simpa [redA, redAh] using maj1_one
  | n + 1 => by
    have ih := maj1_redA hm n
    exact maj1_sub (maj1_mul (maj1_mul (maj1_C _) maj1_X) ih) (maj1_mul (maj1_C_le (ih _)) hm)

lemma eval_redAh (mh : ℕ[X]) (Lh d : ℕ) : ∀ n, (redAh mh Lh d n).eval 1 ≤ (Lh + mh.eval 1) ^ n
  | 0 => by simp [redAh]
  | n + 1 => by
    have ih := eval_redAh mh Lh d n
    have hc := coeff_le_eval_one (redAh mh Lh d n) (d - 1)
    calc (redAh mh Lh d (n + 1)).eval 1
        = Lh * (redAh mh Lh d n).eval 1 + (redAh mh Lh d n).coeff (d - 1) * mh.eval 1 := by
          simp [redAh]
      _ ≤ Lh * (redAh mh Lh d n).eval 1 + (redAh mh Lh d n).eval 1 * mh.eval 1 := by gcongr
      _ = (redAh mh Lh d n).eval 1 * (Lh + mh.eval 1) := by ring
      _ ≤ (Lh + mh.eval 1) ^ n * (Lh + mh.eval 1) := by gcongr
      _ = (Lh + mh.eval 1) ^ (n + 1) := (pow_succ _ _).symm

end Algebraic

section Bounds

open Polynomial

/-- Size bound on an integer polynomial in two variables: a majorant with double value at `1`
at most `b` and `X`-degrees at most `dx`, and `Y`-degree at most `dy`. -/
def Sz (P : ℤ[X][X]) (b dx dy : ℕ) : Prop :=
  (∃ Ph : ℕ[X][X], Maj2 P Ph ∧ E2 Ph ≤ b ∧ DegX Ph dx) ∧ P.natDegree ≤ dy

lemma sz_mono {P : ℤ[X][X]} {b b' dx dx' dy dy' : ℕ} (h : Sz P b dx dy) (hb : b ≤ b')
    (hx : dx ≤ dx') (hy : dy ≤ dy') : Sz P b' dx' dy' := by
  obtain ⟨⟨Ph, h1, h2, h3⟩, h4⟩ := h
  exact ⟨⟨Ph, h1, h2.trans hb, degX_mono h3 hx⟩, h4.trans hy⟩

lemma sz_add {P P' : ℤ[X][X]} {b₁ b₂ dx dy : ℕ} (hP : Sz P b₁ dx dy) (hQ : Sz P' b₂ dx dy) :
    Sz (P + P') (b₁ + b₂) dx dy := by
  obtain ⟨⟨Ph, h1, h2, h3⟩, h4⟩ := hP
  obtain ⟨⟨Qh, g1, g2, g3⟩, g4⟩ := hQ
  exact ⟨⟨Ph + Qh, maj2_add h1 g1, by rw [E2_add]; exact add_le_add h2 g2, degX_add h3 g3⟩,
    (natDegree_add_le _ _).trans (max_le h4 g4)⟩

lemma sz_neg {P : ℤ[X][X]} {b dx dy : ℕ} (hP : Sz P b dx dy) : Sz (-P) b dx dy := by
  obtain ⟨⟨Ph, h1, h2, h3⟩, h4⟩ := hP
  exact ⟨⟨Ph, maj2_neg h1, h2, h3⟩, by rwa [natDegree_neg]⟩

lemma sz_mul {P P' : ℤ[X][X]} {b₁ b₂ dx₁ dx₂ dy₁ dy₂ : ℕ} (hP : Sz P b₁ dx₁ dy₁)
    (hQ : Sz P' b₂ dx₂ dy₂) : Sz (P * P') (b₁ * b₂) (dx₁ + dx₂) (dy₁ + dy₂) := by
  obtain ⟨⟨Ph, h1, h2, h3⟩, h4⟩ := hP
  obtain ⟨⟨Qh, g1, g2, g3⟩, g4⟩ := hQ
  exact ⟨⟨Ph * Qh, maj2_mul h1 g1, by rw [E2_mul]; exact Nat.mul_le_mul h2 g2, degX_mul h3 g3⟩,
    natDegree_mul_le.trans (add_le_add h4 g4)⟩

lemma sz_zero : Sz 0 0 0 0 := ⟨⟨0, maj2_zero, by simp [E2], fun k => by simp⟩, by simp⟩

lemma sz_one : Sz 1 1 0 0 := ⟨⟨1, maj2_one, by simp [E2], degX_one⟩, by simp⟩

lemma sz_X : Sz X 1 0 1 := ⟨⟨X, maj2_X, by simp [E2], degX_X⟩, natDegree_X_le⟩

lemma sz_CC (a : ℤ) : Sz (C (C a)) a.natAbs 0 0 :=
  ⟨⟨C (C a.natAbs), maj2_C (maj1_C a), by simp [E2], by simpa using (degX_C (p := C a.natAbs))⟩,
    by simp⟩

lemma sz_CX : Sz (C X) 1 1 0 :=
  ⟨⟨C X, maj2_C maj1_X, by simp [E2], degX_mono degX_C natDegree_X_le⟩, by simp⟩

lemma sz_pow {P : ℤ[X][X]} {b dx dy : ℕ} (h : Sz P b dx dy) :
    ∀ n : ℕ, Sz (P ^ n) (b ^ n) (n * dx) (n * dy)
  | 0 => by simpa using sz_one
  | n + 1 => by
    rw [pow_succ, pow_succ, Nat.succ_mul, Nat.succ_mul]
    exact sz_mul (sz_pow h n) h

lemma sz_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ[X][X]) {b dx dy : ℕ}
    (h : ∀ i ∈ s, Sz (f i) b dx dy) : Sz (∑ i ∈ s, f i) (s.card * b) dx dy := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sz_mono sz_zero le_rfl (Nat.zero_le dx) (Nat.zero_le dy)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Nat.succ_mul, add_comm (s.card * b)]
    exact sz_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma sz_monomial (μ ν : ℕ) : Sz (C (X ^ μ) * X ^ ν) 1 μ ν := by
  have h := sz_mul (sz_pow sz_CX μ) (sz_pow sz_X ν)
  simpa [C_pow] using h

lemma sz_coeff {P : ℤ[X][X]} {b dx dy : ℕ} (h : Sz P b dx dy) (k i : ℕ) :
    ((P.coeff k).coeff i).natAbs ≤ b ∧ (P.coeff k).natDegree ≤ dx := by
  obtain ⟨⟨Ph, h1, h2, h3⟩, -⟩ := h
  exact ⟨(maj2_coeff_le h1 k i).trans h2, (maj1_natDegree (h1 k)).trans (h3 k)⟩

lemma sz_C_coeff {P : ℤ[X][X]} {b dx dy : ℕ} (h : Sz P b dx dy) (n : ℕ) :
    Sz (C (P.coeff n)) b dx 0 := by
  obtain ⟨⟨Ph, h1, h2, h3⟩, -⟩ := h
  refine ⟨⟨C (Ph.coeff n), maj2_C (h1 n), ?_, degX_mono degX_C (h3 n)⟩, by simp⟩
  have : E2 (C (Ph.coeff n)) = (Ph.coeff n).eval 1 := by simp [E2]
  rw [this]; exact (eval_coeff_le_E2 Ph n).trans h2

lemma sz_exists (P : ℤ[X][X]) : ∃ c, Sz P c c c := by
  set Dx := ∑ k ∈ Finset.range (P.natDegree + 1), (P.coeff k).natDegree with hDx
  have hD : ∀ k, (P.coeff k).natDegree ≤ Dx := by
    intro k
    by_cases hk : k ≤ P.natDegree
    · exact Finset.single_le_sum (f := fun k => (P.coeff k).natDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (by omega))
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  refine ⟨E2 (absPoly2 P) + Dx + P.natDegree, ⟨⟨absPoly2 P, maj2_absPoly2 P, by omega,
    degX_mono (degX_absPoly2 P Dx hD) (by omega)⟩, by omega⟩⟩

end Bounds

section AuxArrays

open Polynomial

/-- `dstep` scaled by `D`, on arrays of integer polynomials in two variables. -/
noncomputable def dstepZ (S T : ℕ) (Dp : ℤ[X][X]) (Bp : Fin T → Fin T → ℤ[X][X])
    (p : ℕ → Fin T → Fin T → ℤ[X][X]) : ℕ → Fin T → Fin T → ℤ[X][X] :=
  fun i j k => (if i + 1 < S then C (C ((i : ℤ) + 1)) * Dp * p (i + 1) j k else 0) + Bp j k * p i j k

lemma dstep_smul (S T : ℕ) (β : Fin T → Fin T → ℂ) (a : ℂ) (c : ℕ → Fin T → Fin T → ℂ) :
    dstep S T β (fun i j k => a * c i j k) = fun i j k => a * dstep S T β c i j k := by
  funext i j k; simp only [dstep]; split_ifs <;> ring

lemma dstepZ_eval {S T : ℕ} (φ : ℤ[X][X] →+* ℂ) (Dp : ℤ[X][X]) (Bp : Fin T → Fin T → ℤ[X][X])
    (β : Fin T → Fin T → ℂ) (hB : ∀ j k, φ (Bp j k) = β j k * φ Dp)
    (p : ℕ → Fin T → Fin T → ℤ[X][X]) :
    (fun i j k => φ (dstepZ S T Dp Bp p i j k))
      = fun i j k => φ Dp * dstep S T β (fun i j k => φ (p i j k)) i j k := by
  funext i j k
  simp only [dstepZ, dstep]
  split_ifs
  · simp only [map_add, map_mul, hB, eq_intCast, map_intCast]; push_cast; ring
  · simp only [map_add, map_mul, hB, map_zero]; ring

lemma dstepZ_iter_eval {S T : ℕ} (φ : ℤ[X][X] →+* ℂ) (Dp : ℤ[X][X]) (Bp : Fin T → Fin T → ℤ[X][X])
    (β : Fin T → Fin T → ℂ) (hB : ∀ j k, φ (Bp j k) = β j k * φ Dp) :
    ∀ (m : ℕ) (p : ℕ → Fin T → Fin T → ℤ[X][X]),
      (fun i j k => φ ((dstepZ S T Dp Bp)^[m] p i j k))
        = fun i j k => φ Dp ^ m * (dstep S T β)^[m] (fun i j k => φ (p i j k)) i j k
  | 0, p => by simp
  | m + 1, p => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', dstepZ_eval φ Dp Bp β hB,
      dstepZ_iter_eval φ Dp Bp β hB m p, dstep_smul]
    funext i j k
    ring

lemma sz_dstepZ {S T : ℕ} {Dp : ℤ[X][X]} {Bp : Fin T → Fin T → ℤ[X][X]} {bD bB dx dy b ex ey : ℕ}
    (hD : Sz Dp bD dx dy) (hB : ∀ j k, Sz (Bp j k) bB dx dy)
    {p : ℕ → Fin T → Fin T → ℤ[X][X]} (hp : ∀ i j k, Sz (p i j k) b ex ey) :
    ∀ i j k, Sz (dstepZ S T Dp Bp p i j k) ((S * bD + bB) * b) (dx + ex) (dy + ey) := by
  intro i j k
  simp only [dstepZ]
  have h2 : Sz (Bp j k * p i j k) (bB * b) (dx + ex) (dy + ey) := sz_mul (hB j k) (hp i j k)
  have h1 : Sz (if i + 1 < S then C (C ((i : ℤ) + 1)) * Dp * p (i + 1) j k else 0) (S * bD * b)
      (dx + ex) (dy + ey) := by
    split_ifs with hi
    · have := sz_mul (sz_mul (sz_CC ((i : ℤ) + 1)) hD) (hp (i + 1) j k)
      refine sz_mono this ?_ (by simp) (by simp)
      have e : ((i : ℤ) + 1).natAbs = i + 1 := by omega
      rw [e]; gcongr
    · exact sz_mono sz_zero (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  exact sz_mono (sz_add h1 h2) (by ring_nf; exact le_rfl) le_rfl le_rfl

lemma sz_dstepZ_iter {S T : ℕ} {Dp : ℤ[X][X]} {Bp : Fin T → Fin T → ℤ[X][X]} {bD bB dx dy : ℕ}
    (hD : Sz Dp bD dx dy) (hB : ∀ j k, Sz (Bp j k) bB dx dy) :
    ∀ (m : ℕ) {p : ℕ → Fin T → Fin T → ℤ[X][X]} {b ex ey : ℕ},
      (∀ i j k, Sz (p i j k) b ex ey) →
      ∀ i j k, Sz ((dstepZ S T Dp Bp)^[m] p i j k) ((S * bD + bB) ^ m * b) (ex + m * dx) (ey + m * dy)
  | 0, p, b, ex, ey, hp => by simpa using hp
  | m + 1, p, b, ex, ey, hp => by
    intro i j k
    rw [Function.iterate_succ_apply']
    have := sz_dstepZ (S := S) hD hB (sz_dstepZ_iter (S := S) hD hB m hp) i j k
    refine sz_mono this (by rw [pow_succ]; ring_nf; exact le_rfl) (by ring_nf; omega) (by ring_nf; omega)

end AuxArrays

section RedP

open Polynomial

/-- Reduce the `Y`-degree of `P` below `deg Q`. -/
noncomputable def redP (Q P : ℤ[X][X]) : ℤ[X][X] :=
  ∑ n ∈ Finset.range (P.natDegree + 1), C (P.coeff n) * redY Q n

lemma redP_eval (Q P : ℤ[X][X]) (φ : ℤ[X][X] →+* ℂ) (hQ : φ Q = 0) : φ (redP Q P) = φ P := by
  conv_rhs => rw [P.as_sum_range_C_mul_X_pow]
  simp only [redP, map_sum, map_mul, map_pow, redY_eval Q φ hQ]

lemma sz_redY {Q : ℤ[X][X]} (hQm : Q.Monic) (hd : 0 < Q.natDegree) {qb DQ dQ : ℕ}
    (hQ : Sz Q qb DQ dQ) (n : ℕ) : Sz (redY Q n) ((1 + qb) ^ n) (n * DQ) (Q.natDegree - 1) := by
  obtain ⟨⟨Qh, h1, h2, h3⟩, -⟩ := hQ
  refine ⟨⟨redYh Qh Q.natDegree n, maj2_redY Q h1 n, (E2_redYh Qh _ n).trans ?_,
    degX_redYh h3 _ n⟩, ?_⟩
  · gcongr
  · have := redY_natDegree Q hQm hd n; omega

lemma sz_redP {Q : ℤ[X][X]} (hQm : Q.Monic) (hd : 0 < Q.natDegree) {qb DQ dQ : ℕ}
    (hQ : Sz Q qb DQ dQ) {P : ℤ[X][X]} {b dx dy : ℕ} (hP : Sz P b dx dy) :
    Sz (redP Q P) ((dy + 1) * (b * (1 + qb) ^ dy)) (dx + dy * DQ) (Q.natDegree - 1) := by
  have hdeg : P.natDegree ≤ dy := hP.2
  have h := sz_sum (Finset.range (P.natDegree + 1)) (fun n => C (P.coeff n) * redY Q n)
    (b := b * (1 + qb) ^ dy) (dx := dx + dy * DQ) (dy := Q.natDegree - 1) (fun n hn => by
      have hn' : n ≤ dy := by rw [Finset.mem_range] at hn; omega
      refine sz_mono (sz_mul (sz_C_coeff hP n) (sz_redY hQm hd hQ n)) ?_ ?_ (by simp)
      · gcongr; omega
      · gcongr)
  refine sz_mono h ?_ le_rfl le_rfl
  rw [Finset.card_range]; gcongr

end RedP

section Presentations

open Polynomial

lemma dstep_sum {ι : Type*} (S T : ℕ) (β : Fin T → Fin T → ℂ) (s : Finset ι) (a : ι → ℂ)
    (f : ι → ℕ → Fin T → Fin T → ℂ) :
    dstep S T β (fun i j k => ∑ x ∈ s, a x * f x i j k)
      = fun i j k => ∑ x ∈ s, a x * dstep S T β (f x) i j k := by
  funext i j k
  simp only [dstep]
  split_ifs
  · simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  · simp only [Finset.mul_sum, zero_add]
    exact Finset.sum_congr rfl fun x _ => by ring

lemma dstep_iter_sum {ι : Type*} (S T : ℕ) (β : Fin T → Fin T → ℂ) (s : Finset ι) (a : ι → ℂ) :
    ∀ (m : ℕ) (f : ι → ℕ → Fin T → Fin T → ℂ),
    (dstep S T β)^[m] (fun i j k => ∑ x ∈ s, a x * f x i j k)
      = fun i j k => ∑ x ∈ s, a x * (dstep S T β)^[m] (f x) i j k
  | 0, f => rfl
  | m + 1, f => by
    rw [Function.iterate_succ_apply', dstep_iter_sum S T β s a m f, dstep_sum]
    funext i j k
    simp only [Function.iterate_succ_apply']

lemma expP_sum {ι : Type*} (S T : ℕ) (β : Fin T → Fin T → ℂ) (s : Finset ι) (a : ι → ℂ)
    (f : ι → ℕ → Fin T → Fin T → ℂ) (z : ℂ) :
    expP S T β (fun i j k => ∑ x ∈ s, a x * f x i j k) z = ∑ x ∈ s, a x * expP S T β (f x) z := by
  simp only [expP, Finset.mul_sum, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `δ^{ℓ-1} L^n e^n` as an integer polynomial in two variables. -/
noncomputable def expPres (m : ℤ[X]) (Hp Dp : ℤ[X][X]) (n : ℕ) : ℤ[X][X] :=
  ∑ l ∈ Finset.range m.natDegree, C (C ((redA m n).coeff l)) * Hp ^ l * Dp ^ (m.natDegree - 1 - l)

lemma expPres_eval (m : ℤ[X]) (hd : 0 < m.natDegree) {e : ℂ} (he : aeval e m = 0)
    (φ : ℤ[X][X] →+* ℂ) (Hp Dp : ℤ[X][X]) (hH : φ Hp = e * φ Dp) (n : ℕ) :
    φ (expPres m Hp Dp n) = φ Dp ^ (m.natDegree - 1) * ((m.leadingCoeff : ℂ) ^ n * e ^ n) := by
  rw [← redA_eval m he n, aeval_eq_sum_range' (redA_natDegree m hd n), Finset.mul_sum]
  simp only [expPres, map_sum, map_mul, map_pow, hH, eq_intCast, map_intCast, zsmul_eq_mul]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.mem_range] at hl
  have : φ Dp ^ (m.natDegree - 1) = φ Dp ^ l * φ Dp ^ (m.natDegree - 1 - l) := by
    rw [← pow_add]; congr 1; omega
  rw [this, mul_pow]; ring

lemma sz_expPres (m : ℤ[X]) {Hp Dp : ℤ[X][X]} {c : ℕ} (hH : Sz Hp c c c) (hD : Sz Dp c c c) (n : ℕ) :
    Sz (expPres m Hp Dp n)
      (m.natDegree * ((m.leadingCoeff.natAbs + (absPoly1 m).eval 1) ^ n * c ^ (m.natDegree - 1)))
      ((m.natDegree - 1) * c) ((m.natDegree - 1) * c) := by
  have h := sz_sum (Finset.range m.natDegree)
    (fun l => C (C ((redA m n).coeff l)) * Hp ^ l * Dp ^ (m.natDegree - 1 - l))
    (b := (m.leadingCoeff.natAbs + (absPoly1 m).eval 1) ^ n * c ^ (m.natDegree - 1))
    (dx := (m.natDegree - 1) * c) (dy := (m.natDegree - 1) * c) (fun l hl => by
      rw [Finset.mem_range] at hl
      have hc : ((redA m n).coeff l).natAbs ≤ (m.leadingCoeff.natAbs + (absPoly1 m).eval 1) ^ n :=
        (maj1_redA m (maj1_absPoly1 m) n l).trans ((coeff_le_eval_one _ _).trans (eval_redAh _ _ _ n))
      have h1 := sz_mul (sz_mul (sz_CC ((redA m n).coeff l)) (sz_pow hH l)) (sz_pow hD (m.natDegree - 1 - l))
      have hsplit : m.natDegree - 1 = l + (m.natDegree - 1 - l) := by omega
      refine sz_mono h1 ?_ ?_ ?_
      · rw [hsplit, pow_add]
        calc ((redA m n).coeff l).natAbs * c ^ l * c ^ (l + (m.natDegree - 1 - l) - l)
            = ((redA m n).coeff l).natAbs * (c ^ l * c ^ (m.natDegree - 1 - l)) := by
              rw [show l + (m.natDegree - 1 - l) - l = m.natDegree - 1 - l by omega]; ring
          _ ≤ _ := Nat.mul_le_mul_right _ hc
      · rw [zero_add, ← add_mul]; gcongr; omega
      · rw [zero_add, ← add_mul]; gcongr; omega)
  rw [Finset.card_range] at h
  exact h

/-- `(a G₀ + b G₁)^i D^{S-i}`, presenting `δ^S w^i`. -/
noncomputable def zpow (S a b : ℕ) (G0 G1 Dp : ℤ[X][X]) (i : ℕ) : ℤ[X][X] :=
  (C (C (a : ℤ)) * G0 + C (C (b : ℤ)) * G1) ^ i * Dp ^ (S - i)

lemma zpow_eval (S a b : ℕ) (φ : ℤ[X][X] →+* ℂ) {G0 G1 Dp : ℤ[X][X]} {y₁ y₂ : ℂ}
    (h0 : φ G0 = y₁ * φ Dp) (h1 : φ G1 = y₂ * φ Dp) {i : ℕ} (hi : i ≤ S) :
    φ (zpow S a b G0 G1 Dp i) = φ Dp ^ S * ((a : ℂ) * y₁ + (b : ℂ) * y₂) ^ i := by
  simp only [zpow, map_mul, map_pow, map_add, h0, h1, eq_intCast, map_intCast, map_natCast]
  push_cast
  have : φ Dp ^ S = φ Dp ^ i * φ Dp ^ (S - i) := by rw [← pow_add]; congr 1; omega
  rw [this, show (a : ℂ) * (y₁ * φ Dp) + b * (y₂ * φ Dp) = φ Dp * ((a : ℂ) * y₁ + b * y₂) by ring, mul_pow]
  ring

lemma sz_zpow (S a b : ℕ) {G0 G1 Dp : ℤ[X][X]} {c : ℕ} (h0 : Sz G0 c c c) (h1 : Sz G1 c c c)
    (hD : Sz Dp c c c) {i : ℕ} (hi : i ≤ S) :
    Sz (zpow S a b G0 G1 Dp i) (((a + b + 1) * c) ^ S) (S * c) (S * c) := by
  have hl : Sz (C (C (a : ℤ)) * G0 + C (C (b : ℤ)) * G1) ((a + b + 1) * c) c c := by
    have := sz_add (sz_mul (sz_CC (a : ℤ)) h0) (sz_mul (sz_CC (b : ℤ)) h1)
    refine sz_mono this ?_ (by simp) (by simp)
    simp only [Int.natAbs_natCast]; nlinarith
  have hD' : Sz Dp ((a + b + 1) * c) c c := sz_mono hD (Nat.le_mul_of_pos_left c (by omega)) le_rfl le_rfl
  have := sz_mul (sz_pow hl i) (sz_pow hD' (S - i))
  have hsplit : S = i + (S - i) := by omega
  refine sz_mono this ?_ ?_ ?_
  · conv_rhs => rw [hsplit, pow_add]
  · rw [← add_mul, ← hsplit]
  · rw [← add_mul, ← hsplit]

end Presentations

section Identity

open Polynomial

lemma phi_CC (φ : ℤ[X][X] →+* ℂ) (z : ℤ) : φ (C (C z)) = (z : ℂ) := by
  have : (C (C z) : ℤ[X][X]) = (z : ℤ[X][X]) := by simp
  rw [this, map_intCast]

/-- `δ^{ℓ-1} L^{Nm} e^n`. -/
noncomputable def fac (mm : ℤ[X]) (Hp Dp : ℤ[X][X]) (Nm n : ℕ) : ℤ[X][X] :=
  C (C (mm.leadingCoeff ^ (Nm - n))) * expPres mm Hp Dp n

lemma fac_eval (mm : ℤ[X]) (hd : 0 < mm.natDegree) {e : ℂ} (he : aeval e mm = 0)
    (φ : ℤ[X][X] →+* ℂ) (Hp Dp : ℤ[X][X]) (hH : φ Hp = e * φ Dp) {Nm n : ℕ} (hn : n ≤ Nm) :
    φ (fac mm Hp Dp Nm n) = φ Dp ^ (mm.natDegree - 1) * (mm.leadingCoeff : ℂ) ^ Nm * e ^ n := by
  rw [fac, map_mul, expPres_eval mm hd he φ Hp Dp hH n, phi_CC, Int.cast_pow]
  have : ((mm.leadingCoeff : ℂ)) ^ Nm = (mm.leadingCoeff : ℂ) ^ (Nm - n) * (mm.leadingCoeff : ℂ) ^ n := by
    rw [← pow_add]; congr 1; omega
  rw [this]; ring

/-- The product of the four exponential factors for `e^{(j x₁ + k x₂)(a y₁ + b y₂)}`. -/
noncomputable def epart (mm : Fin 2 → Fin 2 → ℤ[X]) (H : Fin 2 → Fin 2 → ℤ[X][X]) (Dp : ℤ[X][X])
    (Nm a b j k : ℕ) : ℤ[X][X] :=
  fac (mm 0 0) (H 0 0) Dp Nm (j * a) * fac (mm 0 1) (H 0 1) Dp Nm (j * b) *
    fac (mm 1 0) (H 1 0) Dp Nm (k * a) * fac (mm 1 1) (H 1 1) Dp Nm (k * b)

/-- The constant produced by `epart`. -/
noncomputable def epartConst (mm : Fin 2 → Fin 2 → ℤ[X]) (δ : ℂ) (Nm : ℕ) : ℂ :=
  ∏ i : Fin 2, ∏ j : Fin 2, (δ ^ ((mm i j).natDegree - 1) * ((mm i j).leadingCoeff : ℂ) ^ Nm)

lemma epart_eval (x₁ x₂ y₁ y₂ : ℂ) (mm : Fin 2 → Fin 2 → ℤ[X])
    (hm : ∀ i j, 0 < (mm i j).natDegree ∧
      aeval (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j)) (mm i j) = 0)
    (φ : ℤ[X][X] →+* ℂ) (H : Fin 2 → Fin 2 → ℤ[X][X]) (Dp : ℤ[X][X])
    (hH : ∀ i j, φ (H i j) = Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) * φ Dp)
    {Nm a b j k : ℕ} (h1 : j * a ≤ Nm) (h2 : j * b ≤ Nm) (h3 : k * a ≤ Nm) (h4 : k * b ≤ Nm) :
    φ (epart mm H Dp Nm a b j k)
      = epartConst mm (φ Dp) Nm * Complex.exp (((j : ℂ) * x₁ + (k : ℂ) * x₂) * ((a : ℂ) * y₁ + (b : ℂ) * y₂)) := by
  simp only [epart, map_mul]
  rw [fac_eval _ (hm 0 0).1 (hm 0 0).2 φ _ Dp (hH 0 0) h1, fac_eval _ (hm 0 1).1 (hm 0 1).2 φ _ Dp (hH 0 1) h2,
    fac_eval _ (hm 1 0).1 (hm 1 0).2 φ _ Dp (hH 1 0) h3, fac_eval _ (hm 1 1).1 (hm 1 1).2 φ _ Dp (hH 1 1) h4]
  have hexp : Complex.exp (((j : ℂ) * x₁ + (k : ℂ) * x₂) * ((a : ℂ) * y₁ + (b : ℂ) * y₂))
      = Complex.exp (x₁ * y₁) ^ (j * a) * Complex.exp (x₁ * y₂) ^ (j * b) *
        Complex.exp (x₂ * y₁) ^ (k * a) * Complex.exp (x₂ * y₂) ^ (k * b) := by
    simp only [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [hexp]
  simp only [epartConst, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  ring

/-- The elementary coefficient array of the unknown `(i₀, j₀, k₀, μ, ν)`. -/
noncomputable def pu (T : ℕ) (i0 : ℕ) (j0 k0 : Fin T) (μ ν : ℕ) : ℕ → Fin T → Fin T → ℤ[X][X] :=
  fun i j k => if i = i0 ∧ j = j0 ∧ k = k0 then C (X ^ μ) * X ^ ν else 0

/-- The integer polynomial presenting the contribution of one unknown. -/
noncomputable def piU (S T : ℕ) (Dp : ℤ[X][X]) (Bp : Fin T → Fin T → ℤ[X][X]) (zp : ℕ → ℤ[X][X])
    (ep : Fin T → Fin T → ℤ[X][X]) (m : ℕ) (p : ℕ → Fin T → Fin T → ℤ[X][X]) : ℤ[X][X] :=
  ∑ i ∈ range S, ∑ j : Fin T, ∑ k : Fin T, (dstepZ S T Dp Bp)^[m] p i j k * zp i * ep j k

lemma piU_eval {S T : ℕ} (φ : ℤ[X][X] →+* ℂ) (Dp : ℤ[X][X]) (Bp : Fin T → Fin T → ℤ[X][X])
    (β : Fin T → Fin T → ℂ) (hB : ∀ j k, φ (Bp j k) = β j k * φ Dp) (zp : ℕ → ℤ[X][X])
    (ep : Fin T → Fin T → ℤ[X][X]) (w Λ : ℂ) (hz : ∀ i < S, φ (zp i) = φ Dp ^ S * w ^ i)
    (he : ∀ j k, φ (ep j k) = Λ * Complex.exp (β j k * w)) (m : ℕ) (p : ℕ → Fin T → Fin T → ℤ[X][X]) :
    φ (piU S T Dp Bp zp ep m p)
      = φ Dp ^ m * φ Dp ^ S * Λ * expP S T β ((dstep S T β)^[m] (fun i j k => φ (p i j k))) w := by
  have hit := dstepZ_iter_eval (S := S) φ Dp Bp β hB m p
  simp only [piU, expP, map_sum, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mem_range] at hi
  rw [show φ ((dstepZ S T Dp Bp)^[m] p i j k) = _ from congrFun (congrFun (congrFun hit i) j) k,
    hz i hi, he j k]
  ring

end Identity

section Unknowns

open Polynomial

lemma phi_mono (φ : ℤ[X][X] →+* ℂ) {ω ω₁ : ℂ} (h0 : φ (C X) = ω) (h1 : φ X = ω₁) (μ ν : ℕ) :
    φ (C (X ^ μ) * X ^ ν) = ω ^ μ * ω₁ ^ ν := by
  rw [map_mul, C_pow, map_pow, map_pow, h0, h1]

lemma coeff_sum_unknowns {S T M d : ℕ} (φ : ℤ[X][X] →+* ℂ) {ω ω₁ : ℂ} (h0 : φ (C X) = ω) (h1 : φ X = ω₁)
    (q : Fin S → Fin T → Fin T → Fin M → Fin d → ℤ) (i : Fin S) (j k : Fin T) :
    ∑ u : Fin S × Fin T × Fin T × Fin M × Fin d,
        ((q u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 : ℤ) : ℂ) *
          φ (pu T u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 (i : ℕ) j k)
      = ∑ μ : Fin M, ∑ ν : Fin d, ((q i j k μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ) := by
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j, Finset.sum_eq_single k]
  · refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    simp only [pu, true_and, if_true, phi_mono φ h0 h1]; ring
  · intro k' _ hk; refine Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun ν _ => ?_
    simp [pu, Ne.symm hk]
  · simp
  · intro j' _ hj; refine Finset.sum_eq_zero fun k' _ => Finset.sum_eq_zero fun μ _ =>
      Finset.sum_eq_zero fun ν _ => ?_
    simp [pu, Ne.symm hj]
  · simp
  · intro i' _ hi; refine Finset.sum_eq_zero fun j' _ => Finset.sum_eq_zero fun k' _ =>
      Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun ν _ => ?_
    have : (i : ℕ) ≠ (i' : ℕ) := fun h => hi (Fin.ext h).symm
    simp [pu, this]
  · simp

lemma deriv_identity {S T M d : ℕ} (φ : ℤ[X][X] →+* ℂ) {ω ω₁ : ℂ} (h0 : φ (C X) = ω) (h1 : φ X = ω₁)
    (x₁ x₂ : ℂ) (q : Fin S → Fin T → Fin T → Fin M → Fin d → ℤ) (m : ℕ) (w : ℂ) :
    ∑ u : Fin S × Fin T × Fin T × Fin M × Fin d,
        ((q u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 : ℤ) : ℂ) *
          expP S T (fun j k => ((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂)
            ((dstep S T (fun j k => ((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂))^[m]
              (fun i j k => φ (pu T u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 i j k))) w
      = iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k' : Fin T,
          (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin d, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k'
            * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z)) w := by
  set β : Fin T → Fin T → ℂ := fun j k => ((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂ with hβ
  set cq : ℕ → Fin T → Fin T → ℂ := fun i j k => ∑ u : Fin S × Fin T × Fin T × Fin M × Fin d,
        ((q u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 : ℤ) : ℂ) *
          φ (pu T u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 i j k) with hcq
  have hF : (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k' : Fin T,
          (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin d, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k'
            * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z))
      = expP S T β cq := by
    funext z
    simp only [expP]
    rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin T, ∑ k : Fin T, cq i j k * z ^ i * Complex.exp (β j k * z))]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hcq]
    simp only
    rw [coeff_sum_unknowns φ h0 h1 q i j k]
  rw [hF, iteratedDeriv_expP, hcq, dstep_iter_sum S T β Finset.univ
    (fun u : Fin S × Fin T × Fin T × Fin M × Fin d => ((q u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 : ℤ) : ℂ)) m
    (fun u i j k => φ (pu T u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 i j k)), expP_sum]

end Unknowns

section Sizes

open Polynomial

lemma sz_fac (mm : ℤ[X]) {Hp Dp : ℤ[X][X]} {c K : ℕ} (hH : Sz Hp c c c) (hD : Sz Dp c c c) (hc : 1 ≤ c)
    (hℓ : mm.natDegree ≤ K) (hA : mm.leadingCoeff.natAbs + (absPoly1 mm).eval 1 ≤ K) {Nm n : ℕ}
    (hn : n ≤ Nm) : Sz (fac mm Hp Dp Nm n) (K * K ^ Nm * c ^ K) (K * c) (K * c) := by
  have h := sz_mul (sz_CC (mm.leadingCoeff ^ (Nm - n))) (sz_expPres mm hH hD n)
  set A := mm.leadingCoeff.natAbs + (absPoly1 mm).eval 1 with hAdef
  have hL : mm.leadingCoeff.natAbs ≤ A := Nat.le_add_right _ _
  refine sz_mono h ?_ ?_ ?_
  · rw [Int.natAbs_pow]
    calc mm.leadingCoeff.natAbs ^ (Nm - n) * (mm.natDegree * (A ^ n * c ^ (mm.natDegree - 1)))
        ≤ A ^ (Nm - n) * (K * (A ^ n * c ^ K)) := by
          gcongr
          omega
      _ = K * (A ^ (Nm - n + n) * c ^ K) := by rw [pow_add]; ring
      _ ≤ K * (K ^ Nm * c ^ K) := by rw [Nat.sub_add_cancel hn]; gcongr
      _ = K * K ^ Nm * c ^ K := by ring
  · rw [zero_add]; gcongr; omega
  · rw [zero_add]; gcongr; omega

lemma sz_epart (mm : Fin 2 → Fin 2 → ℤ[X]) {H : Fin 2 → Fin 2 → ℤ[X][X]} {Dp : ℤ[X][X]} {c K : ℕ}
    (hH : ∀ i j, Sz (H i j) c c c) (hD : Sz Dp c c c) (hc : 1 ≤ c)
    (hℓ : ∀ i j, (mm i j).natDegree ≤ K)
    (hA : ∀ i j, (mm i j).leadingCoeff.natAbs + (absPoly1 (mm i j)).eval 1 ≤ K)
    {Nm a b j k : ℕ} (h1 : j * a ≤ Nm) (h2 : j * b ≤ Nm) (h3 : k * a ≤ Nm) (h4 : k * b ≤ Nm) :
    Sz (epart mm H Dp Nm a b j k) ((K * K ^ Nm * c ^ K) ^ 4) (4 * (K * c)) (4 * (K * c)) := by
  have h := sz_mul (sz_mul (sz_mul (sz_fac (mm 0 0) (hH 0 0) hD hc (hℓ 0 0) (hA 0 0) h1)
    (sz_fac (mm 0 1) (hH 0 1) hD hc (hℓ 0 1) (hA 0 1) h2))
    (sz_fac (mm 1 0) (hH 1 0) hD hc (hℓ 1 0) (hA 1 0) h3))
    (sz_fac (mm 1 1) (hH 1 1) hD hc (hℓ 1 1) (hA 1 1) h4)
  exact sz_mono h (by ring_nf; exact le_rfl) (by omega) (by omega)

lemma sz_Bp {E0 E1 : ℤ[X][X]} {c : ℕ} (h0 : Sz E0 c c c) (h1 : Sz E1 c c c) (j k : ℕ) :
    Sz (C (C (j : ℤ)) * E0 + C (C (k : ℤ)) * E1) ((j + k) * c) c c := by
  have := sz_add (sz_mul (sz_CC (j : ℤ)) h0) (sz_mul (sz_CC (k : ℤ)) h1)
  exact sz_mono this (by simp [add_mul]) (by simp) (by simp)

lemma sz_pu (T : ℕ) (i0 : ℕ) (j0 k0 : Fin T) {μ ν M d : ℕ} (hμ : μ ≤ M) (hν : ν ≤ d) (i : ℕ) (j k : Fin T) :
    Sz (pu T i0 j0 k0 μ ν i j k) 1 M d := by
  unfold pu
  split_ifs
  · exact sz_mono (sz_monomial μ ν) le_rfl hμ hν
  · exact sz_mono sz_zero (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

lemma sz_piU {S T : ℕ} {Dp : ℤ[X][X]} {Bp : Fin T → Fin T → ℤ[X][X]} {zp : ℕ → ℤ[X][X]}
    {ep : Fin T → Fin T → ℤ[X][X]} {p : ℕ → Fin T → Fin T → ℤ[X][X]} {c bB bz be ex M d m : ℕ}
    (hD : Sz Dp c c c) (hB : ∀ j k, Sz (Bp j k) bB c c) (hp : ∀ i j k, Sz (p i j k) 1 M d)
    (hz : ∀ i < S, Sz (zp i) bz (S * c) (S * c)) (he : ∀ j k, Sz (ep j k) be ex ex) (hm : m ≤ S)
    (h1 : 1 ≤ S * c + bB) :
    Sz (piU S T Dp Bp zp ep m p) (S * (T * (T * ((S * c + bB) ^ S * bz * be))))
      (M + S * c + S * c + ex) (d + S * c + S * c + ex) := by
  have hit := sz_dstepZ_iter (S := S) hD hB m hp
  unfold piU
  have := sz_sum (Finset.range S) _ (b := T * (T * ((S * c + bB) ^ S * bz * be)))
    (dx := M + S * c + S * c + ex) (dy := d + S * c + S * c + ex) (fun i hi => by
      rw [Finset.mem_range] at hi
      have := sz_sum (Finset.univ : Finset (Fin T)) _ (b := T * ((S * c + bB) ^ S * bz * be))
        (dx := M + S * c + S * c + ex) (dy := d + S * c + S * c + ex) (fun j _ => by
          have := sz_sum (Finset.univ : Finset (Fin T)) _ (b := (S * c + bB) ^ S * bz * be)
            (dx := M + S * c + S * c + ex) (dy := d + S * c + S * c + ex) (fun k _ => by
              have h := sz_mul (sz_mul (hit i j k) (hz i hi)) (he j k)
              refine sz_mono h ?_ ?_ ?_
              · rw [mul_one]; gcongr
              · gcongr
              · gcongr)
          simpa using this)
      simpa using this)
  simpa using this

end Sizes

section System

open Polynomial

theorem system_exists (φ : ℤ[X][X] →+* ℂ) {ω ω₁ : ℂ} (h0 : φ (C X) = ω) (h1 : φ X = ω₁)
    (x₁ x₂ y₁ y₂ : ℂ) (Q : ℤ[X][X]) (hQm : Q.Monic) (hQd : 0 < Q.natDegree) (hQ0 : φ Q = 0)
    (D : ℤ[X][X]) (E G : Fin 2 → ℤ[X][X]) (H : Fin 2 → Fin 2 → ℤ[X][X]) (hD : φ D ≠ 0)
    (hE : ∀ i, ![x₁, x₂] i * φ D = φ (E i)) (hG : ∀ j, ![y₁, y₂] j * φ D = φ (G j))
    (hH : ∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) * φ D = φ (H i j))
    (mm : Fin 2 → Fin 2 → ℤ[X])
    (hm : ∀ i j, 0 < (mm i j).natDegree ∧
      aeval (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j)) (mm i j) = 0)
    {c K : ℕ} (hc : 1 ≤ c) (hcD : Sz D c c c) (hcE : ∀ i, Sz (E i) c c c) (hcG : ∀ j, Sz (G j) c c c)
    (hcH : ∀ i j, Sz (H i j) c c c) (hcQ : Sz Q c c c) (hℓ : ∀ i j, (mm i j).natDegree ≤ K)
    (hA : ∀ i j, (mm i j).leadingCoeff.natAbs + (absPoly1 (mm i j)).eval 1 ≤ K)
    (S T t₁ t₂ M : ℕ) (hT : 1 ≤ T) :
    ∃ B : Fin t₁ × Fin t₂ × Fin S ×
        Fin (M + S * c + S * c + 4 * (K * c) + (Q.natDegree + S * c + S * c + 4 * (K * c)) * c + 1) ×
        Fin Q.natDegree → Fin S → Fin T → Fin T → Fin M → Fin Q.natDegree → ℤ,
      (∀ e i j k μ ν, (B e i j k μ ν).natAbs ≤
        (Q.natDegree + S * c + S * c + 4 * (K * c) + 1) *
          (S * (T * (T * ((S * c + 2 * T * c) ^ S * ((t₁ + t₂ + 1) * c) ^ S *
            (K * K ^ (T * (t₁ + t₂)) * c ^ K) ^ 4))) *
            (1 + c) ^ (Q.natDegree + S * c + S * c + 4 * (K * c)))) ∧
      ∀ q : Fin S → Fin T → Fin T → Fin M → Fin Q.natDegree → ℤ,
        (∀ e, ∑ i : Fin S, ∑ j : Fin T, ∑ k' : Fin T, ∑ μ : Fin M, ∑ ν : Fin Q.natDegree,
          B e i j k' μ ν * q i j k' μ ν = 0) →
        ∀ a b m : ℕ, a < t₁ → b < t₂ → m < S →
          iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k' : Fin T,
            (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree,
              ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' * z ^ (i : ℕ) *
              Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z))
            ((a : ℂ) * y₁ + (b : ℂ) * y₂) = 0 := by
  classical
  let Bp : Fin T → Fin T → ℤ[X][X] := fun j k => C (C ((j : ℕ) : ℤ)) * E 0 + C (C ((k : ℕ) : ℤ)) * E 1
  let P : ℕ → ℕ → ℕ → Fin S × Fin T × Fin T × Fin M × Fin Q.natDegree → ℤ[X][X] := fun a b m u =>
    redP Q (piU S T D Bp (zpow S a b (G 0) (G 1) D) (fun j k => epart mm H D (T * (t₁ + t₂)) a b j k) m
      (pu T u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2))
  have hsz : ∀ a b m, a ≤ t₁ → b ≤ t₂ → m ≤ S → ∀ u, Sz (P a b m u)
      ((Q.natDegree + S * c + S * c + 4 * (K * c) + 1) *
          (S * (T * (T * ((S * c + 2 * T * c) ^ S * ((t₁ + t₂ + 1) * c) ^ S *
            (K * K ^ (T * (t₁ + t₂)) * c ^ K) ^ 4))) *
            (1 + c) ^ (Q.natDegree + S * c + S * c + 4 * (K * c))))
      (M + S * c + S * c + 4 * (K * c) + (Q.natDegree + S * c + S * c + 4 * (K * c)) * c)
      (Q.natDegree - 1) := by
    intro a b m ha hb hm u
    have hB' : ∀ j k : Fin T, Sz (Bp j k) (2 * T * c) c c := fun j k =>
      sz_mono (sz_Bp (hcE 0) (hcE 1) j k) (by have := j.2; have := k.2; nlinarith) le_rfl le_rfl
    have hp : ∀ i j k, Sz (pu T u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 i j k) 1 M Q.natDegree :=
      sz_pu T _ _ _ u.2.2.2.1.2.le u.2.2.2.2.2.le
    have hz : ∀ i < S, Sz (zpow S a b (G 0) (G 1) D i) (((t₁ + t₂ + 1) * c) ^ S) (S * c) (S * c) :=
      fun i hi => sz_mono (sz_zpow S a b (hcG 0) (hcG 1) hcD hi.le) (by gcongr) le_rfl le_rfl
    have he : ∀ j k : Fin T, Sz (epart mm H D (T * (t₁ + t₂)) a b j k)
        ((K * K ^ (T * (t₁ + t₂)) * c ^ K) ^ 4) (4 * (K * c)) (4 * (K * c)) := fun j k => by
      have hj := j.2; have hk := k.2
      exact sz_epart mm hcH hcD hc hℓ hA (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
    have hP := sz_piU hcD hB' hp hz he hm (by nlinarith)
    exact sz_redP hQm hQd hcQ hP
  refine ⟨fun e i j k μ ν => (((P e.1 e.2.1 e.2.2.1 (i, j, k, μ, ν)).coeff e.2.2.2.2).coeff e.2.2.2.1),
    fun e i j k μ ν => (sz_coeff (hsz _ _ _ e.1.2.le e.2.1.2.le e.2.2.1.2.le _) _ _).1, ?_⟩
  intro q hq a b m ha hb hmS
  have hV : ∑ u : Fin S × Fin T × Fin T × Fin M × Fin Q.natDegree,
      C (C (q u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2)) * P a b m u = 0 := by
    ext r h
    simp only [finset_sum_coeff, coeff_C_mul, coeff_zero]
    by_cases hr : r < Q.natDegree
    · by_cases hh : h < M + S * c + S * c + 4 * (K * c) + (Q.natDegree + S * c + S * c + 4 * (K * c)) * c + 1
      · have := hq (⟨a, ha⟩, ⟨b, hb⟩, ⟨m, hmS⟩, ⟨h, hh⟩, ⟨r, hr⟩)
        simpa [Fintype.sum_prod_type, mul_comm] using this
      · refine Finset.sum_eq_zero fun u _ => ?_
        have := (sz_coeff (hsz a b m ha.le hb.le hmS.le u) r 0).2
        rw [coeff_eq_zero_of_natDegree_lt (p := (P a b m u).coeff r) (by omega), mul_zero]
    · refine Finset.sum_eq_zero fun u _ => ?_
      have := (hsz a b m ha.le hb.le hmS.le u).2
      rw [coeff_eq_zero_of_natDegree_lt (p := P a b m u) (by omega), coeff_zero, mul_zero]
  have hB : ∀ j k : Fin T, φ (Bp j k) = (((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * φ D := by
    intro j k
    simp only [Bp, map_add, map_mul, phi_CC, ← hE]
    simp; ring
  have hz : ∀ i < S, φ (zpow S a b (G 0) (G 1) D i) = φ D ^ S * ((a : ℂ) * y₁ + (b : ℂ) * y₂) ^ i :=
    fun i hi => zpow_eval S a b φ (by simpa using (hG 0).symm) (by simpa using (hG 1).symm) hi.le
  have he : ∀ j k : Fin T, φ (epart mm H D (T * (t₁ + t₂)) a b j k)
      = epartConst mm (φ D) (T * (t₁ + t₂)) *
        Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * ((a : ℂ) * y₁ + (b : ℂ) * y₂)) := by
    intro j k
    have hj := j.2; have hk := k.2
    exact epart_eval x₁ x₂ y₁ y₂ mm hm φ H D (fun i j => (hH i j).symm) (by nlinarith) (by nlinarith)
      (by nlinarith) (by nlinarith)
  have hΛ : epartConst mm (φ D) (T * (t₁ + t₂)) ≠ 0 := by
    unfold epartConst
    refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
    have hne : (mm i j) ≠ 0 := fun h => by have := (hm i j).1; rw [h] at this; simp at this
    exact mul_ne_zero (pow_ne_zero _ hD) (pow_ne_zero _ (by exact_mod_cast leadingCoeff_ne_zero.2 hne))
  have key := congrArg φ hV
  rw [map_zero, map_sum] at key
  simp only [map_mul, phi_CC, P, redP_eval Q _ φ hQ0] at key
  simp only [piU_eval φ D Bp _ hB _ _ _ _ hz he] at key
  rw [← deriv_identity φ h0 h1 x₁ x₂ q m ((a : ℂ) * y₁ + (b : ℂ) * y₂)]
  have : (φ D ^ m * φ D ^ S * epartConst mm (φ D) (T * (t₁ + t₂))) *
      ∑ u : Fin S × Fin T × Fin T × Fin M × Fin Q.natDegree,
        ((q u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 : ℤ) : ℂ) *
          expP S T (fun j k => ((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂)
            ((dstep S T (fun j k => ((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂))^[m]
              (fun i j k => φ (pu T u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 i j k)))
              ((a : ℂ) * y₁ + (b : ℂ) * y₂) = 0 := by
    rw [Finset.mul_sum, ← key]
    exact Finset.sum_congr rfl fun u _ => by ring
  exact (mul_eq_zero.1 this).resolve_left
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hD) (pow_ne_zero _ hD)) hΛ)

end System

section Asymptotics

/-- The constant base of the height bound. -/
def Gc (c K d : ℕ) : ℕ := d + 2 * c + 4 * K * c + 1 + 5 * c + K + c + 4

lemma bfin_le_nat (c K d N S t₁ t₂ : ℕ) (hc : 1 ≤ c) (hN : 1 ≤ N) (hS : S ≤ N ^ 2) (h1 : t₁ ≤ N ^ 2)
    (h2 : t₂ ≤ N ^ 2) :
    (d + S * c + S * c + 4 * (K * c) + 1) *
          (S * (2 * N * (2 * N * ((S * c + 2 * (2 * N) * c) ^ S * ((t₁ + t₂ + 1) * c) ^ S *
            (K * K ^ (2 * N * (t₁ + t₂)) * c ^ K) ^ 4))) *
            (1 + c) ^ (d + S * c + S * c + 4 * (K * c)))
      ≤ Gc c K d ^ (4 + 4 * (2 * N * (t₁ + t₂)) + 4 * K + (d + S * c + S * c + 4 * (K * c))) *
          (Gc c K d * N) ^ (4 * S + 6) := by
  have hN2 : N ≤ N ^ 2 := by nlinarith
  have hG1 : 1 ≤ Gc c K d := by unfold Gc; omega
  have hGsq : Gc c K d ≤ Gc c K d ^ 2 := by nlinarith
  have hA : d + S * c + S * c + 4 * (K * c) + 1 ≤ (Gc c K d * N) ^ 2 := by
    have : d + S * c + S * c + 4 * (K * c) + 1 ≤ Gc c K d * N ^ 2 := by
      unfold Gc
      have hN1 : 1 ≤ N ^ 2 := by nlinarith
      nlinarith [Nat.mul_le_mul_right c hS, Nat.le_mul_of_pos_right d hN1, Nat.le_mul_of_pos_right (K * c) hN1,
        Nat.zero_le (c * N ^ 2), Nat.zero_le (K * N ^ 2)]
    calc _ ≤ Gc c K d * N ^ 2 := this
      _ ≤ Gc c K d ^ 2 * N ^ 2 := by gcongr
      _ = (Gc c K d * N) ^ 2 := by ring
  have hB : S * (2 * N) * (2 * N) ≤ (Gc c K d * N) ^ 4 := by
    have h4 : 4 ≤ Gc c K d := by unfold Gc; omega
    calc S * (2 * N) * (2 * N) ≤ N ^ 2 * (2 * N) * (2 * N) := by gcongr
      _ = 4 * N ^ 4 := by ring
      _ ≤ Gc c K d ^ 4 * N ^ 4 := by gcongr; nlinarith
      _ = (Gc c K d * N) ^ 4 := by ring
  have hC : S * c + 2 * (2 * N) * c ≤ (Gc c K d * N) ^ 2 := by
    calc S * c + 2 * (2 * N) * c ≤ N ^ 2 * c + 4 * N ^ 2 * c := by nlinarith [Nat.mul_le_mul_right c hS, Nat.mul_le_mul_right c hN2]
      _ ≤ Gc c K d * N ^ 2 := by
        unfold Gc; nlinarith [Nat.zero_le (d * N ^ 2), Nat.zero_le (K * c * N ^ 2), Nat.zero_le (K * N ^ 2), Nat.zero_le (c * N ^ 2), Nat.zero_le (N ^ 2)]
      _ ≤ Gc c K d ^ 2 * N ^ 2 := by gcongr
      _ = (Gc c K d * N) ^ 2 := by ring
  have hD : (t₁ + t₂ + 1) * c ≤ (Gc c K d * N) ^ 2 := by
    have hN1 : 1 ≤ N ^ 2 := by nlinarith
    calc (t₁ + t₂ + 1) * c ≤ (3 * N ^ 2) * c := by gcongr; omega
      _ ≤ Gc c K d * N ^ 2 := by
        unfold Gc; nlinarith [Nat.zero_le (d * N ^ 2), Nat.zero_le (K * c * N ^ 2), Nat.zero_le (K * N ^ 2), Nat.zero_le (c * N ^ 2), Nat.zero_le (N ^ 2)]
      _ ≤ Gc c K d ^ 2 * N ^ 2 := by gcongr
      _ = (Gc c K d * N) ^ 2 := by ring
  have hE : K * K ^ (2 * N * (t₁ + t₂)) * c ^ K ≤
      Gc c K d * Gc c K d ^ (2 * N * (t₁ + t₂)) * Gc c K d ^ K := by
    have hK : K ≤ Gc c K d := by unfold Gc; omega
    have hc' : c ≤ Gc c K d := by unfold Gc; omega
    gcongr
  have hF : 1 + c ≤ Gc c K d := by unfold Gc; omega
  calc _ = (d + S * c + S * c + 4 * (K * c) + 1) * (S * (2 * N) * (2 * N)) *
          (S * c + 2 * (2 * N) * c) ^ S * ((t₁ + t₂ + 1) * c) ^ S *
          (K * K ^ (2 * N * (t₁ + t₂)) * c ^ K) ^ 4 * (1 + c) ^ (d + S * c + S * c + 4 * (K * c)) := by ring
    _ ≤ (Gc c K d * N) ^ 2 * (Gc c K d * N) ^ 4 * ((Gc c K d * N) ^ 2) ^ S * ((Gc c K d * N) ^ 2) ^ S *
          (Gc c K d * Gc c K d ^ (2 * N * (t₁ + t₂)) * Gc c K d ^ K) ^ 4 *
          Gc c K d ^ (d + S * c + S * c + 4 * (K * c)) := by gcongr
    _ = _ := by ring

lemma one_le_log_nat {N : ℕ} (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have := Real.exp_one_lt_d9
  linarith

lemma log_le_nat (N : ℕ) : Real.log N ≤ N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · have := Real.log_le_sub_one_of_pos (by exact_mod_cast h : (0 : ℝ) < N); linarith

/-- The height exponent. -/
noncomputable def kap (c K d : ℕ) : ℝ :=
  ((20 + 4 * K + d + 2 * c + 4 * K * c : ℕ) : ℝ) * Real.log (Gc c K d) + 10 * Real.log (Gc c K d) + 10

lemma kap_nonneg (c K d : ℕ) : 0 ≤ kap c K d := by
  unfold kap
  have : 0 ≤ Real.log (Gc c K d) := Real.log_nonneg (by unfold Gc; exact_mod_cast (by omega : 1 ≤ _))
  positivity

lemma height_bound (c K d N S t₁ t₂ : ℕ) (hc : 1 ≤ c) (hN : 3 ≤ N)
    (hS : (S : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt (Real.log N))
    (h1 : (t₁ : ℝ) ≤ (N : ℝ) / Real.sqrt (Real.log N)) (h2 : (t₂ : ℝ) ≤ (N : ℝ) * Real.sqrt (Real.log N)) :
    (((d + S * c + S * c + 4 * (K * c) + 1) *
          (S * (2 * N * (2 * N * ((S * c + 2 * (2 * N) * c) ^ S * ((t₁ + t₂ + 1) * c) ^ S *
            (K * K ^ (2 * N * (t₁ + t₂)) * c ^ K) ^ 4))) *
            (1 + c) ^ (d + S * c + S * c + 4 * (K * c))) : ℕ) : ℝ)
      ≤ Real.exp (kap c K d * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N))) := by
  set L := Real.log N with hL
  set s := Real.sqrt L with hs
  have hL1 : 1 ≤ L := one_le_log_nat hN
  have hLN : L ≤ N := log_le_nat N
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.2 hL1
  have hss : s * s = L := Real.mul_self_sqrt (by linarith)
  have hsL : s ≤ L := by
    linear_combination mul_le_mul_of_nonneg_left hs1 (by linarith : (0 : ℝ) ≤ s) + hss
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hspos : 0 < s := by linarith
  have hS' : (S : ℝ) * s ≤ N ^ 2 := by rwa [le_div_iff₀ hspos] at hS
  have h1' : (t₁ : ℝ) * s ≤ N := by rwa [le_div_iff₀ hspos] at h1
  -- natural-number consequences
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have ht10 : (0 : ℝ) ≤ t₁ := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hNN : (N : ℝ) * 1 ≤ N * N := mul_le_mul_of_nonneg_left (by linarith) hN0
  have hN2 : (1 : ℝ) ≤ N ^ 2 := one_le_pow₀ (by linarith)
  have g2 : (N : ℝ) ^ 2 * 1 ≤ N ^ 2 * s := mul_le_mul_of_nonneg_left hs1 (by positivity)
  have hSn : S ≤ N ^ 2 := by
    have : (S : ℝ) ≤ N ^ 2 := by linear_combination mul_le_mul_of_nonneg_left hs1 hS0 + hS'
    exact_mod_cast this
  have h1n : t₁ ≤ N ^ 2 := by
    have : (t₁ : ℝ) ≤ N ^ 2 := by
      linear_combination mul_le_mul_of_nonneg_left hs1 ht10 + h1' + hNN
    exact_mod_cast this
  have h2n : t₂ ≤ N ^ 2 := by
    have : (t₂ : ℝ) ≤ N ^ 2 := by
      linear_combination h2 + mul_le_mul_of_nonneg_left (hsL.trans hLN) hN0
    exact_mod_cast this
  have hnat := bfin_le_nat c K d N S t₁ t₂ hc (by omega) hSn h1n h2n
  refine (Nat.cast_le.2 hnat).trans ?_
  set G := Gc c K d with hGdef
  have hG1 : (1 : ℝ) ≤ G := by rw [hGdef]; unfold Gc; exact_mod_cast (by omega : 1 ≤ _)
  have hlogG : 0 ≤ Real.log G := Real.log_nonneg hG1
  set P : ℝ := (N : ℝ) ^ 2 * s with hP
  have hP1 : 1 ≤ P := by linear_combination hN2 + g2
  have hGpos : (0 : ℝ) < G := by linarith
  have hGNpos : (0 : ℝ) < G * N := by positivity
  have eG : ∀ n : ℕ, (G : ℝ) ^ n = Real.exp (n * Real.log G) := fun n => by
    rw [Real.exp_nat_mul, Real.exp_log hGpos]
  have eGN : ∀ n : ℕ, ((G : ℝ) * N) ^ n = Real.exp (n * Real.log (G * N)) := fun n => by
    rw [Real.exp_nat_mul, Real.exp_log hGNpos]
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_mul, eG, eGN, ← Real.exp_add]
  apply Real.exp_le_exp.2
  rw [Real.log_mul (by positivity) (by positivity)]
  push_cast
  -- bounds on the exponents
  have hNm : (2 * (N : ℝ) * (t₁ + t₂)) ≤ 4 * P := by
    have f1 : (N : ℝ) * (t₁ * 1) ≤ N * (t₁ * L) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL1 ht10) hN0
    have f2 : ((N : ℝ) * s) * (t₁ * s) ≤ (N * s) * N := mul_le_mul_of_nonneg_left h1' (by positivity)
    have f3 : (N : ℝ) * t₂ ≤ N * (N * s) := mul_le_mul_of_nonneg_left h2 hN0
    linear_combination 2 * f1 + 2 * f2 - 2 * (N : ℝ) * t₁ * hss + 2 * f3
  have hSP : (S : ℝ) ≤ P := by
    linear_combination mul_le_mul_of_nonneg_left hs1 hS0 + hS' + g2
  have hSL : (S : ℝ) * L ≤ P := by
    linear_combination mul_le_mul_of_nonneg_left hS' (by linarith : (0 : ℝ) ≤ s) - (S : ℝ) * hss
  have hLP : L ≤ P := by linear_combination hLN + hNN + g2
  have hY1 : ((4 : ℝ) + 4 * (2 * N * (t₁ + t₂)) + 4 * K + (d + S * c + S * c + 4 * (K * c)))
      ≤ ((20 + 4 * K + d + 2 * c + 4 * K * c : ℕ) : ℝ) * P := by
    push_cast
    have hc0 : (0 : ℝ) ≤ c := by positivity
    have hK0 : (0 : ℝ) ≤ K := by positivity
    have hd0 : (0 : ℝ) ≤ d := by positivity
    linear_combination 4 * hP1 + 4 * hNm + 4 * mul_le_mul_of_nonneg_left hP1 hK0 +
      mul_le_mul_of_nonneg_left hP1 hd0 + 2 * mul_le_mul_of_nonneg_left hSP hc0 +
      4 * mul_le_mul_of_nonneg_left hP1 (mul_nonneg hK0 hc0)
  have hY2 : ((4 : ℝ) * S + 6) ≤ 10 * P := by linarith
  unfold kap
  have e1 := mul_le_mul_of_nonneg_right hY1 hlogG
  have e2 := mul_le_mul_of_nonneg_right hY2 hlogG
  linear_combination e1 + e2 + 4 * hSL + 6 * hLP

end Asymptotics

section OneVar

open Polynomial

/-- Size bound for a one-variable integer polynomial. -/
def Sz1 (p : ℤ[X]) (b dx : ℕ) : Prop := ∃ ph : ℕ[X], Maj1 p ph ∧ ph.eval 1 ≤ b ∧ ph.natDegree ≤ dx

lemma sz1_mono {p : ℤ[X]} {b b' dx dx' : ℕ} (h : Sz1 p b dx) (hb : b ≤ b') (hx : dx ≤ dx') :
    Sz1 p b' dx' := by
  obtain ⟨ph, h1, h2, h3⟩ := h
  exact ⟨ph, h1, h2.trans hb, h3.trans hx⟩

lemma sz1_zero : Sz1 0 0 0 := ⟨0, maj1_zero, by simp, by simp⟩

lemma sz1_one : Sz1 1 1 0 := ⟨1, maj1_one, by simp, by simp⟩

lemma sz1_add {p q : ℤ[X]} {b₁ b₂ dx : ℕ} (hp : Sz1 p b₁ dx) (hq : Sz1 q b₂ dx) :
    Sz1 (p + q) (b₁ + b₂) dx := by
  obtain ⟨ph, h1, h2, h3⟩ := hp
  obtain ⟨qh, g1, g2, g3⟩ := hq
  exact ⟨ph + qh, maj1_add h1 g1, by simpa using add_le_add h2 g2,
    (natDegree_add_le _ _).trans (max_le h3 g3)⟩

lemma sz1_neg {p : ℤ[X]} {b dx : ℕ} (hp : Sz1 p b dx) : Sz1 (-p) b dx := by
  obtain ⟨ph, h1, h2, h3⟩ := hp
  exact ⟨ph, maj1_neg h1, h2, h3⟩

lemma sz1_mul {p q : ℤ[X]} {b₁ b₂ dx₁ dx₂ : ℕ} (hp : Sz1 p b₁ dx₁) (hq : Sz1 q b₂ dx₂) :
    Sz1 (p * q) (b₁ * b₂) (dx₁ + dx₂) := by
  obtain ⟨ph, h1, h2, h3⟩ := hp
  obtain ⟨qh, g1, g2, g3⟩ := hq
  exact ⟨ph * qh, maj1_mul h1 g1, by simpa using Nat.mul_le_mul h2 g2,
    natDegree_mul_le.trans (add_le_add h3 g3)⟩

lemma sz1_prod {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) {b dx : ℕ} (h : ∀ i ∈ s, Sz1 (f i) b dx) :
    Sz1 (∏ i ∈ s, f i) (b ^ s.card) (s.card * dx) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sz1_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ, Nat.succ_mul]
    refine sz1_mono (sz1_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))) ?_ ?_
    · rw [mul_comm]
    · omega

lemma sz1_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) {b dx : ℕ} (h : ∀ i ∈ s, Sz1 (f i) b dx) :
    Sz1 (∑ i ∈ s, f i) (s.card * b) dx := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sz1_mono sz1_zero le_rfl (Nat.zero_le dx)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Nat.succ_mul, add_comm (s.card * b)]
    exact sz1_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma sz_coeff_sz1 {P : ℤ[X][X]} {b dx dy : ℕ} (h : Sz P b dx dy) (k : ℕ) : Sz1 (P.coeff k) b dx := by
  obtain ⟨⟨Ph, h1, h2, h3⟩, -⟩ := h
  exact ⟨Ph.coeff k, h1 k, (eval_coeff_le_E2 Ph k).trans h2, h3 k⟩

lemma sz1_natAbs {p : ℤ[X]} {b dx : ℕ} (h : Sz1 p b dx) (i : ℕ) : (p.coeff i).natAbs ≤ b := by
  obtain ⟨ph, h1, h2, -⟩ := h
  exact (h1 i).trans ((coeff_le_eval_one ph i).trans h2)

lemma sz1_natDegree {p : ℤ[X]} {b dx : ℕ} (h : Sz1 p b dx) : p.natDegree ≤ dx := by
  obtain ⟨ph, h1, -, h3⟩ := h
  exact (maj1_natDegree h1).trans h3

/-- Evaluating a bounded integer polynomial at a complex number. -/
lemma sz1_eval_le {p : ℤ[X]} {b dx : ℕ} (h : Sz1 p b dx) (ω : ℂ) :
    ‖aeval ω p‖ ≤ (dx + 1) * b * max 1 ‖ω‖ ^ dx := by
  have hdeg : p.natDegree < dx + 1 := Nat.lt_succ_of_le (sz1_natDegree h)
  rw [aeval_eq_sum_range' hdeg]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i ∈ Finset.range (dx + 1), ‖p.coeff i • ω ^ i‖ ≤ (b : ℝ) * max 1 ‖ω‖ ^ dx := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [zsmul_eq_mul, norm_mul, norm_pow]
    have h1 : ‖((p.coeff i : ℤ) : ℂ)‖ ≤ b := by
      have := sz1_natAbs h i
      calc ‖((p.coeff i : ℤ) : ℂ)‖ = ((p.coeff i).natAbs : ℝ) := by
            rw [Complex.norm_intCast, ← Int.cast_abs, Int.abs_eq_natAbs]; simp
        _ ≤ b := by exact_mod_cast this
    have h2 : ‖ω‖ ^ i ≤ max 1 ‖ω‖ ^ dx :=
      (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) i).trans
        (pow_le_pow_right₀ (le_max_left _ _) (by omega))
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast; ring

/-- A determinant of bounded entries. -/
lemma norm_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hA : ∀ i j, ‖A i j‖ ≤ t) : ‖A.det‖ ≤ (n.factorial : ℝ) * t ^ n := by
  rw [Matrix.det_apply]
  refine (norm_sum_le _ _).trans ?_
  have hprod : ∀ σ : Equiv.Perm (Fin n), ‖(∏ i, A (σ i) i)‖ ≤ t ^ n := by
    intro σ
    rw [norm_prod]
    calc ∏ i, ‖A (σ i) i‖ ≤ ∏ _i : Fin n, t :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hA _ _)
      _ = t ^ n := by simp
  refine (Finset.sum_le_sum (g := fun _ : Equiv.Perm (Fin n) => t ^ n) (fun σ _ => ?_)).trans ?_
  · have he : ‖Equiv.Perm.sign σ • (∏ i, A (σ i) i)‖ = ‖∏ i, A (σ i) i‖ := by
      obtain h | h := Int.units_eq_one_or (Equiv.Perm.sign σ) <;> rw [h] <;> simp
    rw [he]
    exact hprod σ
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

end OneVar

section MultMatrix

open Polynomial

/-- The matrix of multiplication by `Pi` modulo `Q`, in the basis `1, Y, …, Y^{d-1}`. -/
noncomputable def multMat (Q Pol : ℤ[X][X]) (d : ℕ) : Matrix (Fin d) (Fin d) ℤ[X] :=
  fun j k => (redP Q (Pol * X ^ (k : ℕ))).coeff (j : ℕ)

lemma phi_eq_sum {A : ℤ[X][X]} {d : ℕ} (hA : A.natDegree < d) (φ : ℤ[X][X] →+* ℂ)
    (ψ : ℤ[X] →+* ℂ) (hψ : ∀ p, φ (C p) = ψ p) (ω₁ : ℂ) (hX : φ X = ω₁) :
    φ A = ∑ j : Fin d, ψ (A.coeff (j : ℕ)) * ω₁ ^ (j : ℕ) := by
  conv_lhs => rw [A.as_sum_range' d hA]
  simp only [← C_mul_X_pow_eq_monomial, map_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun j => φ (C (A.coeff j) * X ^ j))]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul, map_pow, hψ, hX]

lemma multMat_eval (Q Pol : ℤ[X][X]) (hQm : Q.Monic) (hd : 0 < Q.natDegree) (φ : ℤ[X][X] →+* ℂ)
    (ψ : ℤ[X] →+* ℂ) (hψ : ∀ p, φ (C p) = ψ p) (ω₁ : ℂ) (hX : φ X = ω₁) (hQ : φ Q = 0) (k : Fin Q.natDegree) :
    ∑ j : Fin Q.natDegree, ψ (multMat Q Pol Q.natDegree j k) * ω₁ ^ (j : ℕ) = φ Pol * ω₁ ^ (k : ℕ) := by
  have hdeg : (redP Q (Pol * X ^ (k : ℕ))).natDegree < Q.natDegree := by
    have := (sz_redP hQm hd (sz_exists Q).choose_spec (sz_exists (Pol * X ^ (k : ℕ))).choose_spec).2
    omega
  simp only [multMat]
  rw [← phi_eq_sum hdeg φ ψ hψ ω₁ hX, redP_eval Q _ φ hQ, map_mul, map_pow, hX]

lemma det_factor {d : ℕ} (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) (γ : ℂ)
    (hv : Matrix.vecMul v A = γ • v) (hv0 : v ⟨0, hd⟩ = 1) :
    A.det = γ * (Matrix.vecMul v (Matrix.adjugate A)) ⟨0, hd⟩ := by
  have h1 : Matrix.vecMul (Matrix.vecMul v A) (Matrix.adjugate A) = Matrix.vecMul v (A * Matrix.adjugate A) :=
    Matrix.vecMul_vecMul v A (Matrix.adjugate A)
  rw [hv, Matrix.mul_adjugate] at h1
  have h2 := congrFun h1 ⟨0, hd⟩
  simp only [Matrix.smul_vecMul, Matrix.vecMul_smul, Matrix.vecMul_one, Pi.smul_apply,
    smul_eq_mul, hv0, mul_one] at h2
  exact h2.symm

lemma multMat_det_ne_zero (Q Pol : ℤ[X][X]) (hQm : Q.Monic) (hd : 0 < Q.natDegree)
    (φ : ℤ[X][X] →+* ℂ) (ψ : ℤ[X] →+* ℂ) (hψ : ∀ p, φ (C p) = ψ p) (hQ : φ Q = 0)
    (hQmin : ∀ A : ℤ[X][X], A.natDegree < Q.natDegree → φ A = 0 → A = 0) (hPol : φ Pol ≠ 0) :
    (multMat Q Pol Q.natDegree).det ≠ 0 := by
  intro h0
  obtain ⟨u, hu, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hredeg : ∀ k : Fin Q.natDegree, (redP Q (Pol * X ^ (k : ℕ))).natDegree < Q.natDegree := by
    intro k
    have := (sz_redP hQm hd (sz_exists Q).choose_spec (sz_exists (Pol * X ^ (k : ℕ))).choose_spec).2
    omega
  have hWz : (∑ k : Fin Q.natDegree, C (u k) * redP Q (Pol * X ^ (k : ℕ))) = 0 := by
    refine Polynomial.ext fun j => ?_
    rw [finsetSum_coeff, coeff_zero]
    by_cases hj : j < Q.natDegree
    · have hmj := congrFun hmv ⟨j, hj⟩
      simp only [Matrix.mulVec, dotProduct, multMat] at hmj
      have hz : (0 : Fin Q.natDegree → ℤ[X]) ⟨j, hj⟩ = 0 := rfl
      rw [hz] at hmj
      rw [← hmj]
      exact Finset.sum_congr rfl fun k _ => by rw [coeff_C_mul]; ring
    · refine Finset.sum_eq_zero fun k _ => ?_
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hredeg k) (by omega)), mul_zero]
  have hUdeg : (∑ k : Fin Q.natDegree, C (u k) * X ^ (k : ℕ)).natDegree < Q.natDegree := by
    have hle : (∑ k : Fin Q.natDegree, C (u k) * X ^ (k : ℕ)).natDegree ≤ Q.natDegree - 1 := by
      refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
      exact (natDegree_C_mul_le _ _).trans (by simpa using (by omega : (k : ℕ) ≤ Q.natDegree - 1))
    omega
  have hUphi : φ Pol * φ (∑ k : Fin Q.natDegree, C (u k) * X ^ (k : ℕ)) = 0 := by
    have hw : φ (∑ k : Fin Q.natDegree, C (u k) * redP Q (Pol * X ^ (k : ℕ))) = 0 := by
      rw [hWz, map_zero]
    rw [map_sum] at hw
    rw [map_sum, Finset.mul_sum, ← hw]
    exact Finset.sum_congr rfl fun k _ => by
      rw [map_mul, map_mul, redP_eval Q _ φ hQ, map_mul, hψ]; ring
  have hU0 : (∑ k : Fin Q.natDegree, C (u k) * X ^ (k : ℕ)) = 0 :=
    hQmin _ hUdeg ((mul_eq_zero.1 hUphi).resolve_left hPol)
  refine hu (funext fun k => ?_)
  have hcoef : (∑ k' : Fin Q.natDegree, C (u k') * X ^ (k' : ℕ)).coeff (k : ℕ) = u k := by
    rw [finsetSum_coeff, Finset.sum_eq_single k]
    · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
    · intro k' _ hk'
      have hne : (k : ℕ) ≠ (k' : ℕ) := fun h => hk' (Fin.ext h.symm)
      rw [coeff_C_mul, coeff_X_pow, if_neg hne, mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  rw [hU0, coeff_zero] at hcoef
  simpa using hcoef.symm

end MultMatrix

section Presentation5

open Polynomial

/-- The `X`-degree bound of the presented value. -/
def dxC5 (c K M S d : ℕ) : ℕ := (M + S * c + S * c + 4 * (K * c)) + (d + S * c + S * c + 4 * (K * c)) * c

/-- The height bound of the presented value. -/
def bC5 (c K M S T d Qb A B : ℕ) : ℕ :=
  ((d + S * c + S * c + 4 * (K * c)) + 1) *
    ((S * T * T * M * d) * (Qb * (S * (T * (T * ((S * c + 2 * T * c) ^ S * ((A + B + 1) * c) ^ S *
      (K * K ^ (T * (A + B)) * c ^ K) ^ 4))))) * (1 + c) ^ (d + S * c + S * c + 4 * (K * c)))

theorem pol_exists (φ : ℤ[X][X] →+* ℂ) {ω ω₁ : ℂ} (h0 : φ (C X) = ω) (h1 : φ X = ω₁)
    (x₁ x₂ y₁ y₂ : ℂ) (Q : ℤ[X][X]) (hQm : Q.Monic) (hQd : 0 < Q.natDegree) (hQ0 : φ Q = 0)
    (D : ℤ[X][X]) (E G : Fin 2 → ℤ[X][X]) (H : Fin 2 → Fin 2 → ℤ[X][X])
    (hE : ∀ i, ![x₁, x₂] i * φ D = φ (E i)) (hG : ∀ j, ![y₁, y₂] j * φ D = φ (G j))
    (hH : ∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) * φ D = φ (H i j))
    (mm : Fin 2 → Fin 2 → ℤ[X])
    (hm : ∀ i j, 0 < (mm i j).natDegree ∧
      aeval (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j)) (mm i j) = 0)
    {c K : ℕ} (hc : 1 ≤ c) (hcD : Sz D c c c) (hcE : ∀ i, Sz (E i) c c c) (hcG : ∀ j, Sz (G j) c c c)
    (hcH : ∀ i j, Sz (H i j) c c c) (hcQ : Sz Q c c c) (hℓ : ∀ i j, (mm i j).natDegree ≤ K)
    (hA : ∀ i j, (mm i j).leadingCoeff.natAbs + (absPoly1 (mm i j)).eval 1 ≤ K)
    (S T M : ℕ) (hT : 1 ≤ T) (Qb : ℕ)
    (q : Fin S → Fin T → Fin T → Fin M → Fin Q.natDegree → ℤ)
    (hq : ∀ i j k' μ ν, (q i j k' μ ν).natAbs ≤ Qb) (a b m : ℕ) (hm' : m ≤ S) :
    ∃ Pol : ℤ[X][X],
      φ Pol = (φ D ^ m * φ D ^ S * epartConst mm (φ D) (T * (a + b))) *
        iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k' : Fin T,
          (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree,
            ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' * z ^ (i : ℕ) *
            Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z))
          ((a : ℂ) * y₁ + (b : ℂ) * y₂) ∧
      Sz Pol (bC5 c K M S T Q.natDegree Qb a b) (dxC5 c K M S Q.natDegree) (Q.natDegree - 1) := by
  classical
  refine ⟨redP Q (∑ u : Fin S × Fin T × Fin T × Fin M × Fin Q.natDegree,
    C (C (q u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2)) *
      piU S T D (fun j k => C (C ((j : ℕ) : ℤ)) * E 0 + C (C ((k : ℕ) : ℤ)) * E 1)
        (zpow S a b (G 0) (G 1) D) (fun j k => epart mm H D (T * (a + b)) a b j k) m
        (pu T u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2)), ?_, ?_⟩
  · rw [redP_eval Q _ φ hQ0, map_sum]
    have hB : ∀ j k : Fin T, φ (C (C ((j : ℕ) : ℤ)) * E 0 + C (C ((k : ℕ) : ℤ)) * E 1)
        = (((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * φ D := by
      intro j k
      simp only [map_add, map_mul, phi_CC, ← hE]
      simp; ring
    have hz : ∀ i < S, φ (zpow S a b (G 0) (G 1) D i) = φ D ^ S * ((a : ℂ) * y₁ + (b : ℂ) * y₂) ^ i :=
      fun i hi => zpow_eval S a b φ (by simpa using (hG 0).symm) (by simpa using (hG 1).symm) hi.le
    have he : ∀ j k : Fin T, φ (epart mm H D (T * (a + b)) a b j k)
        = epartConst mm (φ D) (T * (a + b)) *
          Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * ((a : ℂ) * y₁ + (b : ℂ) * y₂)) := by
      intro j k
      have hj := j.2; have hk := k.2
      exact epart_eval x₁ x₂ y₁ y₂ mm hm φ H D (fun i j => (hH i j).symm) (by nlinarith) (by nlinarith)
        (by nlinarith) (by nlinarith)
    rw [← deriv_identity φ h0 h1 x₁ x₂ q m ((a : ℂ) * y₁ + (b : ℂ) * y₂), Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_mul, phi_CC, piU_eval φ D _ _ hB _ _ _ _ hz he]
    ring
  · have hB' : ∀ j k : Fin T, Sz (C (C ((j : ℕ) : ℤ)) * E 0 + C (C ((k : ℕ) : ℤ)) * E 1) (2 * T * c) c c :=
      fun j k => sz_mono (sz_Bp (hcE 0) (hcE 1) j k) (by have := j.2; have := k.2; nlinarith) le_rfl le_rfl
    have hzs : ∀ i < S, Sz (zpow S a b (G 0) (G 1) D i) (((a + b + 1) * c) ^ S) (S * c) (S * c) :=
      fun i hi => sz_zpow S a b (hcG 0) (hcG 1) hcD hi.le
    have hes : ∀ j k : Fin T, Sz (epart mm H D (T * (a + b)) a b j k)
        ((K * K ^ (T * (a + b)) * c ^ K) ^ 4) (4 * (K * c)) (4 * (K * c)) := fun j k => by
      have hj := j.2; have hk := k.2
      exact sz_epart mm hcH hcD hc hℓ hA (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
    have hsum : Sz (∑ u : Fin S × Fin T × Fin T × Fin M × Fin Q.natDegree,
        C (C (q u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2)) *
          piU S T D (fun j k => C (C ((j : ℕ) : ℤ)) * E 0 + C (C ((k : ℕ) : ℤ)) * E 1)
            (zpow S a b (G 0) (G 1) D) (fun j k => epart mm H D (T * (a + b)) a b j k) m
            (pu T u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2))
        ((S * T * T * M * Q.natDegree) * (Qb * (S * (T * (T * ((S * c + 2 * T * c) ^ S *
          ((a + b + 1) * c) ^ S * (K * K ^ (T * (a + b)) * c ^ K) ^ 4))))))
        (M + S * c + S * c + 4 * (K * c)) (Q.natDegree + S * c + S * c + 4 * (K * c)) := by
      have := sz_sum (Finset.univ : Finset (Fin S × Fin T × Fin T × Fin M × Fin Q.natDegree)) _
        (b := Qb * (S * (T * (T * ((S * c + 2 * T * c) ^ S * ((a + b + 1) * c) ^ S *
          (K * K ^ (T * (a + b)) * c ^ K) ^ 4)))))
        (dx := M + S * c + S * c + 4 * (K * c)) (dy := Q.natDegree + S * c + S * c + 4 * (K * c))
        (fun u _ => by
          have hp : ∀ i j k, Sz (pu T u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 i j k) 1 M Q.natDegree :=
            sz_pu T _ _ _ u.2.2.2.1.2.le u.2.2.2.2.2.le
          have hP := sz_piU hcD hB' hp hzs hes hm' (by nlinarith)
          have := sz_mul (sz_CC (q u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2)) hP
          refine sz_mono this ?_ (by simp) (by simp)
          gcongr
          exact hq _ _ _ _ _)
      refine sz_mono this ?_ le_rfl le_rfl
      rw [Finset.card_univ]
      simp only [Fintype.card_prod, Fintype.card_fin]
      exact le_of_eq (by ring)
    have := sz_redP hQm hQd hcQ hsum
    refine sz_mono this ?_ (by rw [dxC5]) le_rfl
    rw [bC5]

end Presentation5

section DetProps

open Polynomial

theorem det_props (Q Pol : ℤ[X][X]) (hQm : Q.Monic) (hQd : 0 < Q.natDegree) (ω ω₁ : ℂ)
    (φ : ℤ[X][X] →+* ℂ) (hφC : ∀ p, φ (C p) = eval₂ (Int.castRingHom ℂ) ω p) (hφX : φ X = ω₁)
    (hQ0 : φ Q = 0) (hQmin : ∀ A : ℤ[X][X], A.natDegree < Q.natDegree → φ A = 0 → A = 0)
    (hPol : φ Pol ≠ 0) {b dx c : ℕ} (hc : 1 ≤ c) (hcQ : Sz Q c c c)
    (hSz : Sz Pol b dx (Q.natDegree - 1)) :
    ∃ P : ℤ[X], P ≠ 0 ∧
      Sz1 P (Q.natDegree.factorial * ((2 * Q.natDegree + 1) * (b * (1 + c) ^ (2 * Q.natDegree))) ^ Q.natDegree)
        (Q.natDegree * (dx + 2 * Q.natDegree * c)) ∧
      ‖aeval ω P‖ ≤ ‖φ Pol‖ * (Q.natDegree * max 1 ‖ω₁‖ ^ Q.natDegree *
        ((Q.natDegree.factorial : ℝ) * max 1 (((dx + 2 * Q.natDegree * c : ℕ) + 1) *
          ((2 * Q.natDegree + 1) * (b * (1 + c) ^ (2 * Q.natDegree)) : ℕ) *
          max 1 ‖ω‖ ^ (dx + 2 * Q.natDegree * c)) ^ Q.natDegree)) := by
  classical
  set d := Q.natDegree with hd
  set b₂ : ℕ := (2 * d + 1) * (b * (1 + c) ^ (2 * d)) with hb₂
  set dx₂ : ℕ := dx + 2 * d * c with hdx₂
  set ψ : ℤ[X] →+* ℂ := eval₂RingHom (Int.castRingHom ℂ) ω with hψdef
  have hψ : ∀ p, φ (C p) = ψ p := hφC
  have haeval : ∀ p : ℤ[X], aeval ω p = ψ p := by
    intro p; simp [hψdef, aeval_def, algebraMap_int_eq]
  -- entries
  have hMsz : ∀ j k : Fin d, Sz1 (multMat Q Pol d j k) b₂ dx₂ := by
    intro j k
    have h1 : Sz (Pol * X ^ (k : ℕ)) b dx (2 * d) := by
      refine sz_mono (sz_mul hSz (sz_pow sz_X (k : ℕ))) ?_ ?_ ?_
      · simp
      · simp
      · have := k.2; omega
    have h2 := sz_redP hQm hQd hcQ h1
    exact sz1_mono (sz_coeff_sz1 h2 (j : ℕ)) (by rw [hb₂]) (by rw [hdx₂])
  refine ⟨(multMat Q Pol d).det, ?_, ?_, ?_⟩
  · exact fun h => multMat_det_ne_zero Q Pol hQm hQd φ ψ hψ hQ0 hQmin hPol h
  · rw [Matrix.det_apply]
    refine sz1_mono (sz1_sum Finset.univ _ (b := b₂ ^ d) (dx := d * dx₂) (fun σ _ => ?_)) ?_ le_rfl
    · have hprod : Sz1 (∏ i, multMat Q Pol d (σ i) i) (b₂ ^ d) (d * dx₂) := by
        have := sz1_prod (Finset.univ : Finset (Fin d)) (fun i => multMat Q Pol d (σ i) i)
          (fun i _ => hMsz _ _)
        simpa using this
      obtain h | h := Int.units_eq_one_or (Equiv.Perm.sign σ)
      · rw [h]; simpa using hprod
      · rw [h]; simpa using sz1_neg hprod
    · rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  · -- the value
    have hdet : aeval ω (multMat Q Pol d).det = ((multMat Q Pol d).map ψ).det := by
      rw [haeval]
      exact RingHom.map_det ψ _
    set A : Matrix (Fin d) (Fin d) ℂ := (multMat Q Pol d).map ψ with hA
    set v : Fin d → ℂ := fun j => ω₁ ^ (j : ℕ) with hv
    have hvec : Matrix.vecMul v A = φ Pol • v := by
      funext k
      simp only [Matrix.vecMul, dotProduct, hA, Matrix.map_apply, hv, Pi.smul_apply, smul_eq_mul]
      have := multMat_eval Q Pol hQm hQd φ ψ hψ ω₁ hφX hQ0 k
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hv0 : v ⟨0, hQd⟩ = 1 := by simp [hv]
    have hfac := det_factor hQd A v (φ Pol) hvec hv0
    have hent : ∀ j k, ‖A j k‖ ≤ ((dx₂ + 1) * b₂ * max 1 ‖ω‖ ^ dx₂ : ℝ) := by
      intro j k
      have h := sz1_eval_le (hMsz j k) ω
      rw [haeval] at h
      simpa [hA, Matrix.map_apply] using h
    have hent' : ∀ j k, ‖A j k‖ ≤ max 1 ((dx₂ + 1) * b₂ * max 1 ‖ω‖ ^ dx₂ : ℝ) :=
      fun j k => (hent j k).trans (le_max_right _ _)
    have hadj : ∀ j, ‖Matrix.adjugate A j ⟨0, hQd⟩‖ ≤
        (d.factorial : ℝ) * max 1 ((dx₂ + 1) * b₂ * max 1 ‖ω‖ ^ dx₂ : ℝ) ^ d := by
      intro j
      rw [Matrix.adjugate_apply]
      refine norm_det_le _ _ (le_trans zero_le_one (le_max_left _ _)) fun i k => ?_
      rcases eq_or_ne i ⟨0, hQd⟩ with rfl | hne
      · simp only [Matrix.updateRow_self, Pi.single_apply]
        split_ifs
        · simpa using le_max_left (1 : ℝ) _
        · simpa using le_trans zero_le_one (le_max_left (1 : ℝ) _)
      · rw [Matrix.updateRow_ne hne]; exact hent' i k
    have hvecadj : ‖(Matrix.vecMul v (Matrix.adjugate A)) ⟨0, hQd⟩‖ ≤
        d * max 1 ‖ω₁‖ ^ d * ((d.factorial : ℝ) * max 1 ((dx₂ + 1) * b₂ * max 1 ‖ω‖ ^ dx₂ : ℝ) ^ d) := by
      simp only [Matrix.vecMul, dotProduct]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum (g := fun _ : Fin d => max 1 ‖ω₁‖ ^ d *
        ((d.factorial : ℝ) * max 1 ((dx₂ + 1) * b₂ * max 1 ‖ω‖ ^ dx₂ : ℝ) ^ d)) (fun j _ => ?_)).trans
        (le_of_eq ?_)
      · rw [norm_mul]
        refine mul_le_mul ?_ (hadj j) (norm_nonneg _) (by positivity)
        rw [hv, norm_pow]
        exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
          (pow_le_pow_right₀ (le_max_left _ _) (by have := j.2; omega))
      · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    rw [hdet, hfac, norm_mul]
    exact mul_le_mul_of_nonneg_left hvecadj (norm_nonneg _)

end DetProps

section Asymptotics5

def Gc5 (c K d : ℕ) : ℕ := d + 32 * c + 4 * K * c + 1 + 5 * c + K + c + 34

lemma bfin5_le_nat (c K d N S t₁ t₂ : ℕ) (hc : 1 ≤ c) (hN : 1 ≤ N) (hS : S ≤ N ^ 2) (h1 : t₁ ≤ 14 * N ^ 2)
    (h2 : t₂ ≤ 14 * N ^ 2) :
    (d + S * c + S * c + 4 * (K * c) + 1) *
          (S * (2 * N * (2 * N * ((S * c + 2 * (2 * N) * c) ^ S * ((t₁ + t₂ + 1) * c) ^ S *
            (K * K ^ (2 * N * (t₁ + t₂)) * c ^ K) ^ 4))) *
            (1 + c) ^ (d + S * c + S * c + 4 * (K * c)))
      ≤ Gc5 c K d ^ (4 + 4 * (2 * N * (t₁ + t₂)) + 4 * K + (d + S * c + S * c + 4 * (K * c))) *
          (Gc5 c K d * N) ^ (4 * S + 6) := by
  have hN2 : N ≤ N ^ 2 := by nlinarith
  have hG1 : 1 ≤ Gc5 c K d := by unfold Gc5; omega
  have hGsq : Gc5 c K d ≤ Gc5 c K d ^ 2 := by nlinarith
  have hA : d + S * c + S * c + 4 * (K * c) + 1 ≤ (Gc5 c K d * N) ^ 2 := by
    have : d + S * c + S * c + 4 * (K * c) + 1 ≤ Gc5 c K d * N ^ 2 := by
      unfold Gc5
      have hN1 : 1 ≤ N ^ 2 := by nlinarith
      nlinarith [Nat.mul_le_mul_right c hS, Nat.le_mul_of_pos_right d hN1, Nat.le_mul_of_pos_right (K * c) hN1,
        Nat.zero_le (c * N ^ 2), Nat.zero_le (K * N ^ 2)]
    calc _ ≤ Gc5 c K d * N ^ 2 := this
      _ ≤ Gc5 c K d ^ 2 * N ^ 2 := by gcongr
      _ = (Gc5 c K d * N) ^ 2 := by ring
  have hB : S * (2 * N) * (2 * N) ≤ (Gc5 c K d * N) ^ 4 := by
    have h4 : 4 ≤ Gc5 c K d := by unfold Gc5; omega
    calc S * (2 * N) * (2 * N) ≤ N ^ 2 * (2 * N) * (2 * N) := by gcongr
      _ = 4 * N ^ 4 := by ring
      _ ≤ Gc5 c K d ^ 4 * N ^ 4 := by gcongr; nlinarith
      _ = (Gc5 c K d * N) ^ 4 := by ring
  have hC : S * c + 2 * (2 * N) * c ≤ (Gc5 c K d * N) ^ 2 := by
    calc S * c + 2 * (2 * N) * c ≤ N ^ 2 * c + 4 * N ^ 2 * c := by nlinarith [Nat.mul_le_mul_right c hS, Nat.mul_le_mul_right c hN2]
      _ ≤ Gc5 c K d * N ^ 2 := by
        unfold Gc5; nlinarith [Nat.zero_le (d * N ^ 2), Nat.zero_le (K * c * N ^ 2), Nat.zero_le (K * N ^ 2), Nat.zero_le (c * N ^ 2), Nat.zero_le (N ^ 2)]
      _ ≤ Gc5 c K d ^ 2 * N ^ 2 := by gcongr
      _ = (Gc5 c K d * N) ^ 2 := by ring
  have hD : (t₁ + t₂ + 1) * c ≤ (Gc5 c K d * N) ^ 2 := by
    have hN1 : 1 ≤ N ^ 2 := by nlinarith
    calc (t₁ + t₂ + 1) * c ≤ (29 * N ^ 2) * c := by gcongr; omega
      _ ≤ Gc5 c K d * N ^ 2 := by
        unfold Gc5; nlinarith [Nat.zero_le (d * N ^ 2), Nat.zero_le (K * c * N ^ 2), Nat.zero_le (K * N ^ 2), Nat.zero_le (c * N ^ 2), Nat.zero_le (N ^ 2)]
      _ ≤ Gc5 c K d ^ 2 * N ^ 2 := by gcongr
      _ = (Gc5 c K d * N) ^ 2 := by ring
  have hE : K * K ^ (2 * N * (t₁ + t₂)) * c ^ K ≤
      Gc5 c K d * Gc5 c K d ^ (2 * N * (t₁ + t₂)) * Gc5 c K d ^ K := by
    have hK : K ≤ Gc5 c K d := by unfold Gc5; omega
    have hc' : c ≤ Gc5 c K d := by unfold Gc5; omega
    gcongr
  have hF : 1 + c ≤ Gc5 c K d := by unfold Gc5; omega
  calc _ = (d + S * c + S * c + 4 * (K * c) + 1) * (S * (2 * N) * (2 * N)) *
          (S * c + 2 * (2 * N) * c) ^ S * ((t₁ + t₂ + 1) * c) ^ S *
          (K * K ^ (2 * N * (t₁ + t₂)) * c ^ K) ^ 4 * (1 + c) ^ (d + S * c + S * c + 4 * (K * c)) := by ring
    _ ≤ (Gc5 c K d * N) ^ 2 * (Gc5 c K d * N) ^ 4 * ((Gc5 c K d * N) ^ 2) ^ S * ((Gc5 c K d * N) ^ 2) ^ S *
          (Gc5 c K d * Gc5 c K d ^ (2 * N * (t₁ + t₂)) * Gc5 c K d ^ K) ^ 4 *
          Gc5 c K d ^ (d + S * c + S * c + 4 * (K * c)) := by gcongr
    _ = _ := by ring

/-- The height exponent for the larger grid. -/
noncomputable def kap5 (c K d : ℕ) : ℝ :=
  ((240 + 4 * K + d + 2 * c + 4 * K * c : ℕ) : ℝ) * Real.log (Gc5 c K d) + 10 * Real.log (Gc5 c K d) + 10

lemma kap5_nonneg (c K d : ℕ) : 0 ≤ kap5 c K d := by
  unfold kap5
  have : 0 ≤ Real.log (Gc5 c K d) := Real.log_nonneg (by unfold Gc5; exact_mod_cast (by omega : 1 ≤ _))
  positivity

lemma height_bound5 (c K d N S t₁ t₂ : ℕ) (hc : 1 ≤ c) (hN : 3 ≤ N)
    (hS : (S : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt (Real.log N))
    (h1 : (t₁ : ℝ) ≤ 14 * ((N : ℝ) / Real.sqrt (Real.log N))) (h2 : (t₂ : ℝ) ≤ 14 * ((N : ℝ) * Real.sqrt (Real.log N))) :
    (((d + S * c + S * c + 4 * (K * c) + 1) *
          (S * (2 * N * (2 * N * ((S * c + 2 * (2 * N) * c) ^ S * ((t₁ + t₂ + 1) * c) ^ S *
            (K * K ^ (2 * N * (t₁ + t₂)) * c ^ K) ^ 4))) *
            (1 + c) ^ (d + S * c + S * c + 4 * (K * c))) : ℕ) : ℝ)
      ≤ Real.exp (kap5 c K d * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N))) := by
  set L := Real.log N with hL
  set s := Real.sqrt L with hs
  have hL1 : 1 ≤ L := one_le_log_nat hN
  have hLN : L ≤ N := log_le_nat N
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.2 hL1
  have hss : s * s = L := Real.mul_self_sqrt (by linarith)
  have hsL : s ≤ L := by
    linear_combination mul_le_mul_of_nonneg_left hs1 (by linarith : (0 : ℝ) ≤ s) + hss
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hspos : 0 < s := by linarith
  have hS' : (S : ℝ) * s ≤ N ^ 2 := by rwa [le_div_iff₀ hspos] at hS
  have h1' : (t₁ : ℝ) * s ≤ 14 * N := by
    rw [mul_comm (14 : ℝ) ((N : ℝ) / s), div_mul_eq_mul_div, le_div_iff₀ hspos] at h1
    linarith
  -- natural-number consequences
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have ht10 : (0 : ℝ) ≤ t₁ := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hNN : (N : ℝ) * 1 ≤ N * N := mul_le_mul_of_nonneg_left (by linarith) hN0
  have hN2 : (1 : ℝ) ≤ N ^ 2 := one_le_pow₀ (by linarith)
  have g2 : (N : ℝ) ^ 2 * 1 ≤ N ^ 2 * s := mul_le_mul_of_nonneg_left hs1 (by positivity)
  have hSn : S ≤ N ^ 2 := by
    have : (S : ℝ) ≤ N ^ 2 := by linear_combination mul_le_mul_of_nonneg_left hs1 hS0 + hS'
    exact_mod_cast this
  have h1n : t₁ ≤ 14 * N ^ 2 := by
    have : (t₁ : ℝ) ≤ 14 * (N : ℝ) ^ 2 := by
      linear_combination mul_le_mul_of_nonneg_left hs1 ht10 + h1' + 14 * hNN
    exact_mod_cast this
  have h2n : t₂ ≤ 14 * N ^ 2 := by
    have : (t₂ : ℝ) ≤ 14 * (N : ℝ) ^ 2 := by
      linear_combination h2 + 14 * mul_le_mul_of_nonneg_left (hsL.trans hLN) hN0
    exact_mod_cast this
  have hnat := bfin5_le_nat c K d N S t₁ t₂ hc (by omega) hSn h1n h2n
  refine (Nat.cast_le.2 hnat).trans ?_
  set G := Gc5 c K d with hGdef
  have hG1 : (1 : ℝ) ≤ G := by rw [hGdef]; unfold Gc5; exact_mod_cast (by omega : 1 ≤ _)
  have hlogG : 0 ≤ Real.log G := Real.log_nonneg hG1
  set P : ℝ := (N : ℝ) ^ 2 * s with hP
  have hP1 : 1 ≤ P := by linear_combination hN2 + g2
  have hGpos : (0 : ℝ) < G := by linarith
  have hGNpos : (0 : ℝ) < G * N := by positivity
  have eG : ∀ n : ℕ, (G : ℝ) ^ n = Real.exp (n * Real.log G) := fun n => by
    rw [Real.exp_nat_mul, Real.exp_log hGpos]
  have eGN : ∀ n : ℕ, ((G : ℝ) * N) ^ n = Real.exp (n * Real.log (G * N)) := fun n => by
    rw [Real.exp_nat_mul, Real.exp_log hGNpos]
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_mul, eG, eGN, ← Real.exp_add]
  apply Real.exp_le_exp.2
  rw [Real.log_mul (by positivity) (by positivity)]
  push_cast
  -- bounds on the exponents
  have hNm : (2 * (N : ℝ) * (t₁ + t₂)) ≤ 56 * P := by
    have f1 : (N : ℝ) * (t₁ * 1) ≤ N * (t₁ * L) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL1 ht10) hN0
    have f2 : ((N : ℝ) * s) * (t₁ * s) ≤ (N * s) * (14 * N) :=
      mul_le_mul_of_nonneg_left h1' (by positivity)
    have f3 : (N : ℝ) * t₂ ≤ N * (14 * ((N : ℝ) * s)) := mul_le_mul_of_nonneg_left h2 hN0
    linear_combination 2 * f1 + 2 * f2 - 2 * (N : ℝ) * t₁ * hss + 2 * f3
  have hSP : (S : ℝ) ≤ P := by
    linear_combination mul_le_mul_of_nonneg_left hs1 hS0 + hS' + g2
  have hSL : (S : ℝ) * L ≤ P := by
    linear_combination mul_le_mul_of_nonneg_left hS' (by linarith : (0 : ℝ) ≤ s) - (S : ℝ) * hss
  have hLP : L ≤ P := by linear_combination hLN + hNN + g2
  have hY1 : ((4 : ℝ) + 4 * (2 * N * (t₁ + t₂)) + 4 * K + (d + S * c + S * c + 4 * (K * c)))
      ≤ ((240 + 4 * K + d + 2 * c + 4 * K * c : ℕ) : ℝ) * P := by
    push_cast
    have hc0 : (0 : ℝ) ≤ c := by positivity
    have hK0 : (0 : ℝ) ≤ K := by positivity
    have hd0 : (0 : ℝ) ≤ d := by positivity
    linear_combination 4 * hP1 + 4 * hNm + 12 * hP1 + 4 * mul_le_mul_of_nonneg_left hP1 hK0 +
      mul_le_mul_of_nonneg_left hP1 hd0 + 2 * mul_le_mul_of_nonneg_left hSP hc0 +
      4 * mul_le_mul_of_nonneg_left hP1 (mul_nonneg hK0 hc0)
  have hY2 : ((4 : ℝ) * S + 6) ≤ 10 * P := by linarith
  unfold kap5
  have e1 := mul_le_mul_of_nonneg_right hY1 hlogG
  have e2 := mul_le_mul_of_nonneg_right hY2 hlogG
  linear_combination e1 + e2 + 4 * hSL + 6 * hLP


lemma log_nat_facts {N : ℕ} (hN : 3 ≤ N) :
    1 ≤ Real.log N ∧ Real.log N ≤ N ∧ Real.log N / 2 ≤ Real.log ((N : ℝ) - 1) := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  · have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < N); linarith
  · have h : (N : ℝ) ≤ ((N : ℝ) - 1) ^ 2 := by nlinarith
    have := Real.log_le_log (by positivity) h
    rw [Real.log_pow] at this
    push_cast at this
    linarith

/-- Shared facts about `L = log N` and `q = √L`. -/
lemma q_facts {N : ℕ} (hN : 3 ≤ N) :
    1 ≤ Real.sqrt (Real.log N) ∧ Real.sqrt (Real.log N) * Real.sqrt (Real.log N) = Real.log N ∧
      Real.sqrt (Real.log N) ≤ N := by
  obtain ⟨hL1, hLN, -⟩ := log_nat_facts hN
  have hq1 : 1 ≤ Real.sqrt (Real.log N) := Real.one_le_sqrt.2 hL1
  have hqq := Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ Real.log N)
  refine ⟨hq1, hqq, ?_⟩
  have : Real.sqrt (Real.log N) ≤ Real.log N := by
    linear_combination mul_le_mul_of_nonneg_left hq1 (by linarith : (0 : ℝ) ≤ Real.sqrt (Real.log N)) + hqq
  linarith


end Asymptotics5

section ExpHelpers

lemma mul_exp_le {x y e f : ℝ} (hy : 0 ≤ y) (hx' : x ≤ Real.exp e) (hy' : y ≤ Real.exp f) :
    x * y ≤ Real.exp (e + f) := by
  rw [Real.exp_add]
  exact mul_le_mul hx' hy' hy (Real.exp_pos _).le

lemma pow_exp_le {x e : ℝ} (hx : 0 ≤ x) (h : x ≤ Real.exp e) (n : ℕ) : x ^ n ≤ Real.exp (n * e) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ hx h n

lemma nat_le_exp_log (m : ℕ) : (m : ℝ) ≤ Real.exp (Real.log (m + 1)) := by
  rw [Real.exp_log (by positivity)]
  linarith

lemma npow_eq_exp {N : ℕ} (hN : 1 ≤ N) (m : ℕ) : ((N : ℝ) ^ m) = Real.exp (m * Real.log N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.exp_nat_mul, Real.exp_log hN0]

end ExpHelpers


section NumHelpers

open Polynomial

lemma card_bound (κ : ℝ) (hκ : 0 < κ) (N S M d : ℕ) (hN : 1 ≤ N) (hS : (S : ℝ) ≤ (N : ℝ) ^ 2)
    (hM : (M : ℝ) ≤ κ * (N : ℝ) ^ 2) :
    ((S * (2 * N) * (2 * N) * M * d : ℕ) : ℝ)
      ≤ Real.exp (Real.log (4 * κ * (d + 1) + 4) + 6 * Real.log N) := by
  have hpos : (0 : ℝ) < 4 * κ * (d + 1) + 4 := by positivity
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have hS0 : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have h6 : ((N : ℝ) ^ 6) = Real.exp (6 * Real.log N) := npow_eq_exp hN 6
  rw [Real.exp_add, Real.exp_log hpos, ← h6]
  push_cast
  calc (S : ℝ) * (2 * N) * (2 * N) * M * d
      ≤ (N : ℝ) ^ 2 * (2 * N) * (2 * N) * (κ * (N : ℝ) ^ 2) * d := by gcongr <;> positivity
    _ = (4 * κ * d) * (N : ℝ) ^ 6 := by ring
    _ ≤ (4 * κ * (d + 1) + 4) * (N : ℝ) ^ 6 := by nlinarith [pow_nonneg hN0 6]

lemma ceil_exp_le (x : ℝ) (hx : 0 ≤ x) : ((⌈Real.exp x⌉₊ : ℕ) : ℝ) ≤ Real.exp (x + 1) := by
  have h1 : ((⌈Real.exp x⌉₊ : ℕ) : ℝ) ≤ Real.exp x + 1 :=
    (Nat.ceil_lt_add_one (Real.exp_pos x).le).le
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have h3 : (1 : ℝ) ≤ Real.exp x := Real.one_le_exp hx
  rw [Real.exp_add]
  nlinarith [Real.exp_pos x]

/-- The height of the presented value, in exponential form. -/
lemma bC5_exp_le (c K M S T d Qb a b : ℕ) (E₁ E₂ E₃ : ℝ)
    (hcard : ((S * T * T * M * d : ℕ) : ℝ) ≤ Real.exp E₁) (hQb : (Qb : ℝ) ≤ Real.exp E₂)
    (hbfin : (((d + S * c + S * c + 4 * (K * c) + 1) *
      (S * (T * (T * ((S * c + 2 * T * c) ^ S * ((a + b + 1) * c) ^ S *
        (K * K ^ (T * (a + b)) * c ^ K) ^ 4))) * (1 + c) ^ (d + S * c + S * c + 4 * (K * c))) : ℕ) : ℝ)
        ≤ Real.exp E₃) :
    ((bC5 c K M S T d Qb a b : ℕ) : ℝ) ≤ Real.exp (E₁ + E₂ + E₃) := by
  have heq : bC5 c K M S T d Qb a b = (S * T * T * M * d) * Qb *
      ((d + S * c + S * c + 4 * (K * c) + 1) *
        (S * (T * (T * ((S * c + 2 * T * c) ^ S * ((a + b + 1) * c) ^ S *
          (K * K ^ (T * (a + b)) * c ^ K) ^ 4))) * (1 + c) ^ (d + S * c + S * c + 4 * (K * c)))) := by
    rw [bC5]; ring
  rw [heq, Nat.cast_mul, Nat.cast_mul]
  exact mul_exp_le (by positivity) (mul_exp_le (by positivity) hcard hQb) hbfin

/-- From a bound on `x`, a bound on the height of the determinant. -/
lemma det_height_exp_le (x c d : ℕ) (E : ℝ) (hx : ((x : ℕ) : ℝ) ≤ Real.exp E) :
    ((d.factorial * ((2 * d + 1) * (x * (1 + c) ^ (2 * d))) ^ d : ℕ) : ℝ)
      ≤ Real.exp (Real.log (d.factorial + 1) +
          d * (Real.log (2 * d + 2) + (E + 2 * d * Real.log (c + 2)))) := by
  have t1 : (1 : ℝ) + (c : ℝ) ≤ Real.exp (Real.log ((c : ℝ) + 2)) := by
    rw [Real.exp_log (by positivity)]
    linarith
  have t2 : ((1 : ℝ) + (c : ℝ)) ^ (2 * d) ≤ Real.exp (2 * (d : ℝ) * Real.log ((c : ℝ) + 2)) := by
    have := pow_exp_le (by positivity) t1 (2 * d)
    rw [show ((2 * d : ℕ) : ℝ) = 2 * (d : ℝ) by push_cast; ring] at this
    exact this
  have t3 : 2 * (d : ℝ) + 1 ≤ Real.exp (Real.log (2 * (d : ℝ) + 2)) := by
    rw [Real.exp_log (by positivity)]
    linarith
  have t4 : (x : ℝ) * ((1 : ℝ) + (c : ℝ)) ^ (2 * d)
      ≤ Real.exp (E + 2 * (d : ℝ) * Real.log ((c : ℝ) + 2)) := mul_exp_le (by positivity) hx t2
  have t5 : (2 * (d : ℝ) + 1) * ((x : ℝ) * ((1 : ℝ) + (c : ℝ)) ^ (2 * d))
      ≤ Real.exp (Real.log (2 * (d : ℝ) + 2) + (E + 2 * (d : ℝ) * Real.log ((c : ℝ) + 2))) :=
    mul_exp_le (by positivity) t3 t4
  have t6 : ((2 * (d : ℝ) + 1) * ((x : ℝ) * ((1 : ℝ) + (c : ℝ)) ^ (2 * d))) ^ d
      ≤ Real.exp ((d : ℝ) * (Real.log (2 * (d : ℝ) + 2) + (E + 2 * (d : ℝ) * Real.log ((c : ℝ) + 2)))) := by
    have := pow_exp_le (by positivity) t5 d
    exact this
  have t7 : ((d.factorial : ℕ) : ℝ) ≤ Real.exp (Real.log (d.factorial + 1)) := nat_le_exp_log _
  push_cast
  exact mul_exp_le (by positivity) t7 t6

lemma dx_bound (c K M S d : ℕ) (B κ : ℝ) (hκ : 0 < κ) (hB1 : 1 ≤ B) (hS : (S : ℝ) ≤ B)
    (hM : (M : ℝ) ≤ κ * B) :
    ((dxC5 c K M S d + 2 * d * c : ℕ) : ℝ)
      ≤ (κ + 2 * c + 4 * K * c + 3 * d * c + 2 * c ^ 2 + 4 * K * c ^ 2) * B := by
  have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  rw [dxC5]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hS hc0, mul_le_mul_of_nonneg_right hS (by positivity : (0:ℝ) ≤ (c:ℝ)^2),
    mul_le_mul_of_nonneg_left hB1 (by positivity : (0:ℝ) ≤ 4 * (K:ℝ) * c),
    mul_le_mul_of_nonneg_left hB1 (by positivity : (0:ℝ) ≤ 3 * (d:ℝ) * c),
    mul_le_mul_of_nonneg_left hB1 (by positivity : (0:ℝ) ≤ 4 * (K:ℝ) * (c:ℝ)^2)]

lemma max_one_le_exp {X e : ℝ} (he : 0 ≤ e) (hX : X ≤ Real.exp e) : max 1 X ≤ Real.exp e :=
  max_le (Real.one_le_exp he) hX

lemma log_succ_le (t : ℝ) (ht : 0 ≤ t) : Real.log (t + 1) ≤ t := by
  have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < t + 1)
  linarith

lemma norm_epartConst_le (mm : Fin 2 → Fin 2 → Polynomial ℤ) (δ : ℂ) (Nm K : ℕ)
    (hℓ : ∀ i j, (mm i j).natDegree ≤ K) (hA : ∀ i j, (mm i j).leadingCoeff.natAbs ≤ K) :
    ‖epartConst mm δ Nm‖ ≤ (max 1 ‖δ‖ ^ K * ((K : ℝ) + 1) ^ Nm) ^ 4 := by
  have hfac : ∀ i j : Fin 2, ‖δ ^ ((mm i j).natDegree - 1) * ((mm i j).leadingCoeff : ℂ) ^ Nm‖
      ≤ max 1 ‖δ‖ ^ K * ((K : ℝ) + 1) ^ Nm := by
    intro i j
    rw [norm_mul, norm_pow, norm_pow]
    have h1 : ‖δ‖ ^ ((mm i j).natDegree - 1) ≤ max 1 ‖δ‖ ^ K :=
      (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) (by have := hℓ i j; omega))
    have h2 : ‖((mm i j).leadingCoeff : ℂ)‖ ≤ (K : ℝ) + 1 := by
      have h3 : ‖((mm i j).leadingCoeff : ℂ)‖ = (((mm i j).leadingCoeff.natAbs : ℕ) : ℝ) := by
        rw [Complex.norm_intCast, ← Int.cast_abs, Int.abs_eq_natAbs]; simp
      rw [h3]
      have := hA i j
      have : (((mm i j).leadingCoeff.natAbs : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast this
      linarith
    exact mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) h2 Nm) (by positivity) (by positivity)
  have hrhs : (max 1 ‖δ‖ ^ K * ((K : ℝ) + 1) ^ Nm) ^ 4 =
      (max 1 ‖δ‖ ^ K * ((K : ℝ) + 1) ^ Nm) * (max 1 ‖δ‖ ^ K * ((K : ℝ) + 1) ^ Nm) *
      ((max 1 ‖δ‖ ^ K * ((K : ℝ) + 1) ^ Nm) * (max 1 ‖δ‖ ^ K * ((K : ℝ) + 1) ^ Nm)) := by ring
  simp only [epartConst, Fin.prod_univ_two, norm_mul]
  rw [hrhs]
  gcongr ?_ * ?_ * (?_ * ?_)
  · rw [← norm_mul]; exact hfac 0 0
  · rw [← norm_mul]; exact hfac 0 1
  · rw [← norm_mul]; exact hfac 1 0
  · rw [← norm_mul]; exact hfac 1 1


/-- Elementary size facts about `N²√log N` and `N²/√log N`. -/
lemma basic5_facts {N : ℕ} (hN : 3 ≤ N) :
    1 ≤ (N : ℝ) ^ 2 * Real.sqrt (Real.log N) ∧ 1 ≤ (N : ℝ) ^ 2 / Real.sqrt (Real.log N) ∧
      (N : ℝ) ^ 2 / Real.sqrt (Real.log N) ≤ (N : ℝ) ^ 2 * Real.sqrt (Real.log N) ∧
      Real.log N ≤ (N : ℝ) ^ 2 * Real.sqrt (Real.log N) := by
  obtain ⟨hL1, hLN, -⟩ := log_nat_facts hN
  obtain ⟨hq1, hqq, hqN⟩ := q_facts hN
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hqpos : 0 < Real.sqrt (Real.log N) := by linarith
  refine ⟨by nlinarith, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hqpos]; nlinarith
  · rw [div_le_iff₀ hqpos]; nlinarith
  · nlinarith

lemma floor_sq_le {N : ℕ} (hN : 3 ≤ N) :
    (⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) ≤ (N : ℝ) ^ 2 := by
  obtain ⟨hq1, -, -⟩ := q_facts hN
  have h := Nat.floor_le (a := (N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))) (by positivity)
  have : (N : ℝ) ^ 2 / Real.sqrt (Real.log N) ≤ (N : ℝ) ^ 2 := div_le_self (by positivity) hq1
  linarith


/-- Constants for the final bounds. -/
noncomputable def betaC5 (d : ℕ) (κ kap5v : ℝ) : ℝ := Real.log (4 * κ * (d + 1) + 4) + 7 + κ + kap5v

noncomputable def kb2C5 (c d : ℕ) (β : ℝ) : ℝ := Real.log (2 * d + 2) + β + 2 * d * Real.log (c + 2)

noncomputable def khC5 (d : ℕ) (kb2 : ℝ) : ℝ := Real.log (d.factorial + 1) + d * kb2

noncomputable def kdegC5 (c K d : ℕ) (κ : ℝ) : ℝ :=
  κ + 2 * c + 4 * K * c + 3 * d * c + 2 * c ^ 2 + 4 * K * c ^ 2

noncomputable def kdeltaC5 (K : ℕ) (lδ : ℝ) : ℝ := 2 * lδ + 4 * K * lδ + 224 * Real.log (K + 1)

noncomputable def kvC5 (d : ℕ) (lw lw1 kdeg kb2 : ℝ) : ℝ :=
  Real.log (d + 1) + d * lw1 + Real.log (d.factorial + 1) + d * (kdeg + kb2 + kdeg * lw)

noncomputable def kC5 (c K d : ℕ) (κ lw lw1 lδ kap5v : ℝ) : ℝ :=
  khC5 d (kb2C5 c d (betaC5 d κ kap5v)) + d * kdegC5 c K d κ + kdeltaC5 K lδ +
    kvC5 d lw lw1 (kdegC5 c K d κ) (kb2C5 c d (betaC5 d κ kap5v)) + 1

lemma beta_nonneg (d : ℕ) (κ kap5v : ℝ) (hκ : 0 < κ) (hkap : 0 ≤ kap5v) : 0 ≤ betaC5 d κ kap5v := by
  unfold betaC5
  have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
  have : 0 ≤ Real.log (4 * κ * (d + 1) + 4) := Real.log_nonneg (by nlinarith)
  linarith

lemma kb2_nonneg (c d : ℕ) (β : ℝ) (hβ : 0 ≤ β) : 0 ≤ kb2C5 c d β := by
  unfold kb2C5
  have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
  have hc0 : (0:ℝ) ≤ (c:ℝ) := Nat.cast_nonneg _
  have h1 : 0 ≤ Real.log (2 * (d:ℝ) + 2) := Real.log_nonneg (by linarith)
  have h2 : 0 ≤ Real.log ((c:ℝ) + 2) := Real.log_nonneg (by linarith)
  have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hd0) h2
  linarith

lemma kh_nonneg (d : ℕ) (kb2 : ℝ) (h : 0 ≤ kb2) : 0 ≤ khC5 d kb2 := by
  unfold khC5
  have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
  have h1 : 0 ≤ Real.log ((d.factorial : ℝ) + 1) := Real.log_nonneg (by
    have : (0:ℝ) ≤ (d.factorial : ℝ) := Nat.cast_nonneg _; linarith)
  have := mul_nonneg hd0 h
  linarith

lemma kdeg_nonneg (c K d : ℕ) (κ : ℝ) (hκ : 0 < κ) : 0 ≤ kdegC5 c K d κ := by
  unfold kdegC5
  have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
  have hc0 : (0:ℝ) ≤ (c:ℝ) := Nat.cast_nonneg _
  have hK0 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg _
  have h1 : (0:ℝ) ≤ 4 * (K:ℝ) * c := by positivity
  have h2 : (0:ℝ) ≤ 3 * (d:ℝ) * c := by positivity
  have h3 : (0:ℝ) ≤ 2 * (c:ℝ)^2 := by positivity
  have h4 : (0:ℝ) ≤ 4 * (K:ℝ) * (c:ℝ)^2 := by positivity
  linarith

lemma kdelta_nonneg (K : ℕ) (lδ : ℝ) (hl : 0 ≤ lδ) : 0 ≤ kdeltaC5 K lδ := by
  unfold kdeltaC5
  have hK0 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg _
  have h1 : 0 ≤ Real.log ((K:ℝ) + 1) := Real.log_nonneg (by linarith)
  have h2 : (0:ℝ) ≤ 4 * (K:ℝ) * lδ := by positivity
  linarith

lemma kv_nonneg (d : ℕ) (lw lw1 kdeg kb2 : ℝ) (hlw : 0 ≤ lw) (hlw1 : 0 ≤ lw1) (hkdeg : 0 ≤ kdeg)
    (hkb2 : 0 ≤ kb2) : 0 ≤ kvC5 d lw lw1 kdeg kb2 := by
  unfold kvC5
  have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
  have h1 : 0 ≤ Real.log ((d:ℝ) + 1) := Real.log_nonneg (by linarith)
  have h2 : 0 ≤ Real.log ((d.factorial : ℝ) + 1) := Real.log_nonneg (by
    have : (0:ℝ) ≤ (d.factorial : ℝ) := Nat.cast_nonneg _; linarith)
  have h3 : (0:ℝ) ≤ (d:ℝ) * lw1 := by positivity
  have h4 : (0:ℝ) ≤ (d:ℝ) * (kdeg + kb2 + kdeg * lw) := by positivity
  linarith

lemma kC5_pos (c K d : ℕ) (κ lw lw1 lδ kap5v : ℝ) (hκ : 0 < κ) (hkap : 0 ≤ kap5v)
    (hlw : 0 ≤ lw) (hlw1 : 0 ≤ lw1) (hlδ : 0 ≤ lδ) : 0 < kC5 c K d κ lw lw1 lδ kap5v := by
  unfold kC5
  have hβ := beta_nonneg d κ kap5v hκ hkap
  have hb2 := kb2_nonneg c d _ hβ
  have h1 := kh_nonneg d _ hb2
  have h2 := kdeg_nonneg c K d κ hκ
  have h3 := kdelta_nonneg K lδ hlδ
  have h4 := kv_nonneg d lw lw1 _ _ hlw hlw1 h2 hb2
  have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
  have h5 : (0:ℝ) ≤ (d:ℝ) * kdegC5 c K d κ := by positivity
  linarith

/-- The height of the presented value against the constant `β`. -/
lemma bC5_beta {d : ℕ} {κ kap5v A LN x : ℝ} (hκ : 0 < κ) (hkap : 0 ≤ kap5v) (hA1 : 1 ≤ A)
    (hLN : LN ≤ A) (hLN0 : 0 ≤ LN)
    (hx : x ≤ Real.exp ((Real.log (4 * κ * ((d : ℝ) + 1) + 4) + 6 * LN) + (κ * A + 1) + kap5v * A)) :
    x ≤ Real.exp (betaC5 d κ kap5v * A) := by
  refine hx.trans (Real.exp_le_exp.2 ?_)
  unfold betaC5
  have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log (4 * κ * ((d:ℝ) + 1) + 4) := Real.log_nonneg (by nlinarith)
  nlinarith [mul_le_mul_of_nonneg_left hA1 hlog]

/-- The height of the determinant. -/
lemma height_final (c d x : ℕ) {β A : ℝ} (hA1 : 1 ≤ A) (hβ0 : 0 ≤ β)
    (hx : ((x : ℕ) : ℝ) ≤ Real.exp (β * A)) :
    ((d.factorial * ((2 * d + 1) * (x * (1 + c) ^ (2 * d))) ^ d : ℕ) : ℝ)
      ≤ Real.exp (khC5 d (kb2C5 c d β) * A) := by
  refine (det_height_exp_le x c d (β * A) hx).trans (Real.exp_le_exp.2 ?_)
  unfold khC5 kb2C5
  have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
  have hc0 : (0:ℝ) ≤ (c:ℝ) := Nat.cast_nonneg _
  have h1 : 0 ≤ Real.log ((d.factorial : ℝ) + 1) := Real.log_nonneg (by
    have : (0:ℝ) ≤ (d.factorial : ℝ) := Nat.cast_nonneg _; linarith)
  have h2 : 0 ≤ Real.log (2 * (d:ℝ) + 2) := Real.log_nonneg (by linarith)
  have h3 : 0 ≤ Real.log ((c:ℝ) + 2) := Real.log_nonneg (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hA1 h1, mul_le_mul_of_nonneg_left hA1 (mul_nonneg hd0 h2),
    mul_le_mul_of_nonneg_left hA1 (mul_nonneg (mul_nonneg (mul_nonneg hd0 (by norm_num : (0:ℝ) ≤ 2)) hd0) h3)]

/-- The degree of the determinant. -/
lemma degree_final (c K d M S : ℕ) {B κ : ℝ} (hκ : 0 < κ) (hB1 : 1 ≤ B) (hS : (S : ℝ) ≤ B)
    (hM : (M : ℝ) ≤ κ * B) :
    ((d * (dxC5 c K M S d + 2 * d * c) : ℕ) : ℝ) ≤ ((d : ℝ) * kdegC5 c K d κ) * B := by
  have h := dx_bound c K M S d B κ hκ hB1 hS hM
  have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
  rw [Nat.cast_mul]
  have := mul_le_mul_of_nonneg_left h hd0
  unfold kdegC5
  calc (d : ℝ) * ((dxC5 c K M S d + 2 * d * c : ℕ) : ℝ)
      ≤ (d : ℝ) * ((κ + 2 * c + 4 * K * c + 3 * d * c + 2 * c ^ 2 + 4 * K * c ^ 2) * B) := this
    _ = (d : ℝ) * (κ + 2 * c + 4 * K * c + 3 * d * c + 2 * c ^ 2 + 4 * K * c ^ 2) * B := by ring

/-- The scaling factor of the presented value. -/
lemma delta_final (K sd S Nm : ℕ) (δ : ℂ) (mm : Fin 2 → Fin 2 → Polynomial ℤ)
    (hℓ : ∀ i j, (mm i j).natDegree ≤ K) (hAk : ∀ i j, (mm i j).leadingCoeff.natAbs ≤ K)
    {A : ℝ} (hA1 : 1 ≤ A) (hsd : (sd : ℝ) ≤ A) (hS : (S : ℝ) ≤ A) (hNm : (Nm : ℝ) ≤ 56 * A) :
    ‖δ ^ sd * δ ^ S * epartConst mm δ Nm‖ ≤ Real.exp (kdeltaC5 K (Real.log (max 1 ‖δ‖)) * A) := by
  have hW : (1:ℝ) ≤ max 1 ‖δ‖ := le_max_left _ _
  have hlδ : 0 ≤ Real.log (max 1 ‖δ‖) := Real.log_nonneg hW
  have hpow : ∀ n : ℕ, (max 1 ‖δ‖) ^ n = Real.exp ((n : ℝ) * Real.log (max 1 ‖δ‖)) := by
    intro n; rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
  have h1 : ‖δ ^ sd‖ ≤ Real.exp (A * Real.log (max 1 ‖δ‖)) := by
    rw [norm_pow]
    refine le_trans (pow_le_pow_left₀ (norm_nonneg _) (le_max_right 1 ‖δ‖) sd) ?_
    rw [hpow sd]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hsd hlδ)
  have h2 : ‖δ ^ S‖ ≤ Real.exp (A * Real.log (max 1 ‖δ‖)) := by
    rw [norm_pow]
    refine le_trans (pow_le_pow_left₀ (norm_nonneg _) (le_max_right 1 ‖δ‖) S) ?_
    rw [hpow S]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hS hlδ)
  have hKlog : 0 ≤ Real.log ((K:ℝ) + 1) := Real.log_nonneg (by
    have : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg _; linarith)
  have hK1 : (0:ℝ) < (K:ℝ) + 1 := by have : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg _; linarith
  have h3 : ‖epartConst mm δ Nm‖
      ≤ Real.exp (4 * (K : ℝ) * Real.log (max 1 ‖δ‖) + 224 * A * Real.log ((K:ℝ) + 1)) := by
    refine (norm_epartConst_le mm δ Nm K hℓ hAk).trans ?_
    have a1 : (max 1 ‖δ‖) ^ K = Real.exp ((K : ℝ) * Real.log (max 1 ‖δ‖)) := hpow K
    have a2 : ((K:ℝ) + 1) ^ Nm = Real.exp ((Nm : ℝ) * Real.log ((K:ℝ) + 1)) := by
      rw [Real.exp_nat_mul, Real.exp_log hK1]
    rw [a1, a2, ← Real.exp_add, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    push_cast
    have := mul_le_mul_of_nonneg_right hNm hKlog
    nlinarith
  have hprod := mul_exp_le (y := ‖epartConst mm δ Nm‖) (norm_nonneg _)
    (mul_exp_le (y := ‖δ ^ S‖) (norm_nonneg _) h1 h2) h3
  rw [norm_mul, norm_mul]
  refine hprod.trans (Real.exp_le_exp.2 ?_)
  unfold kdeltaC5
  have hK0 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hA1 (by positivity : (0:ℝ) ≤ 4 * (K:ℝ) * Real.log (max 1 ‖δ‖))]

/-- The cofactor factor of the value bound. -/
lemma vfac_final (d DX b2 : ℕ) {Wω Wω₁ A kdeg kb2 : ℝ} (hW : 1 ≤ Wω) (hW1 : 1 ≤ Wω₁)
    (hA1 : 1 ≤ A) (hDX : ((DX : ℕ) : ℝ) ≤ kdeg * A) (hkdeg : 0 ≤ kdeg) (hkb2 : 0 ≤ kb2)
    (hb2 : ((b2 : ℕ) : ℝ) ≤ Real.exp (kb2 * A)) :
    (d : ℝ) * Wω₁ ^ d * ((d.factorial : ℝ) * max 1 ((((DX : ℕ) : ℝ) + 1) * ((b2 : ℕ) : ℝ) * Wω ^ DX) ^ d)
      ≤ Real.exp (kvC5 d (Real.log Wω) (Real.log Wω₁) kdeg kb2 * A) := by
  have hlw : 0 ≤ Real.log Wω := Real.log_nonneg hW
  have hlw1 : 0 ≤ Real.log Wω₁ := Real.log_nonneg hW1
  have hDX1 : ((DX : ℕ) : ℝ) + 1 ≤ Real.exp (kdeg * A) := by
    refine le_trans ?_ (Real.add_one_le_exp (kdeg * A))
    linarith
  have hWpow : Wω ^ DX ≤ Real.exp (kdeg * A * Real.log Wω) := by
    have e : Wω ^ DX = Real.exp ((DX : ℝ) * Real.log Wω) := by
      rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
    rw [e]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hDX hlw)
  have hX : (((DX : ℕ) : ℝ) + 1) * ((b2 : ℕ) : ℝ) * Wω ^ DX
      ≤ Real.exp (kdeg * A + kb2 * A + kdeg * A * Real.log Wω) :=
    mul_exp_le (by positivity) (mul_exp_le (by positivity) hDX1 hb2) hWpow
  have hmax : max 1 ((((DX : ℕ) : ℝ) + 1) * ((b2 : ℕ) : ℝ) * Wω ^ DX)
      ≤ Real.exp (kdeg * A + kb2 * A + kdeg * A * Real.log Wω) :=
    max_one_le_exp (by positivity) hX
  have hpowmax : (max 1 ((((DX : ℕ) : ℝ) + 1) * ((b2 : ℕ) : ℝ) * Wω ^ DX)) ^ d
      ≤ Real.exp ((d : ℝ) * (kdeg * A + kb2 * A + kdeg * A * Real.log Wω)) := by
    have := pow_exp_le (le_trans zero_le_one (le_max_left _ _)) hmax d
    exact this
  have hd : (d : ℝ) ≤ Real.exp (Real.log ((d : ℝ) + 1)) := by
    have := nat_le_exp_log d; push_cast at this; exact this
  have hW1pow : Wω₁ ^ d ≤ Real.exp ((d : ℝ) * Real.log Wω₁) := by
    have e : Wω₁ ^ d = Real.exp ((d : ℝ) * Real.log Wω₁) := by
      rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
    exact le_of_eq e
  have hfact : (d.factorial : ℝ) ≤ Real.exp (Real.log ((d.factorial : ℝ) + 1)) := by
    have := nat_le_exp_log d.factorial; push_cast at this; exact this
  have hall := mul_exp_le (by positivity)
    (mul_exp_le (by positivity) hd hW1pow)
    (mul_exp_le (by positivity) hfact hpowmax)
  refine hall.trans (Real.exp_le_exp.2 ?_)
  unfold kvC5
  have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
  have h1 : 0 ≤ Real.log ((d:ℝ) + 1) := Real.log_nonneg (by linarith)
  have h2 : 0 ≤ Real.log ((d.factorial : ℝ) + 1) := Real.log_nonneg (by
    have : (0:ℝ) ≤ (d.factorial : ℝ) := Nat.cast_nonneg _; linarith)
  nlinarith [mul_le_mul_of_nonneg_left hA1 h1, mul_le_mul_of_nonneg_left hA1 h2,
    mul_le_mul_of_nonneg_left hA1 (mul_nonneg hd0 hlw1)]

/-- The final comparison. -/
lemma final_compare (N : ℕ) {κ' C k kv : ℝ} (hκ' : 0 < κ') (hk : 0 ≤ k) (hkv : 0 ≤ kv)
    (hN : 3 ≤ N) (hbig : 2 * κ' * ((|C| + 1) * k ^ 2 + kv + 1) ≤ Real.sqrt (Real.log N)) :
    Real.exp (kv * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N))) *
        Real.exp (-(((N : ℝ) ^ 4 * Real.sqrt (Real.log N)) / κ'))
      < Real.exp (-(C * (k * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N))) *
          (k * ((N : ℝ) ^ 2 / Real.sqrt (Real.log N))))) := by
  obtain ⟨hL1, hLN, -⟩ := log_nat_facts hN
  obtain ⟨hq1, hqq, hqN⟩ := q_facts hN
  have hNr : (3:ℝ) ≤ N := by exact_mod_cast hN
  have hqpos : 0 < Real.sqrt (Real.log N) := by linarith
  rw [← Real.exp_add]
  refine Real.exp_lt_exp.2 ?_
  have hAB : C * (k * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N))) * (k * ((N : ℝ) ^ 2 / Real.sqrt (Real.log N)))
      = C * (k ^ 2 * (N : ℝ) ^ 4) := by
    field_simp
    try ring
  rw [hAB]
  have hN4 : (1:ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ (by linarith)
  have hNN2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hqN2 : Real.sqrt (Real.log N) ≤ (N : ℝ) ^ 2 := by linarith
  have hkvA : kv * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N)) ≤ kv * (N : ℝ) ^ 4 := by
    refine mul_le_mul_of_nonneg_left ?_ hkv
    nlinarith
  have hCk : C * (k ^ 2 * (N : ℝ) ^ 4) ≤ |C| * k ^ 2 * (N : ℝ) ^ 4 := by
    have h := le_abs_self C
    have hp : (0:ℝ) ≤ k ^ 2 * (N : ℝ) ^ 4 := by positivity
    calc C * (k ^ 2 * (N : ℝ) ^ 4) ≤ |C| * (k ^ 2 * (N : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_right h hp
      _ = |C| * k ^ 2 * (N : ℝ) ^ 4 := by ring
  have hdiv : 2 * ((|C| + 1) * k ^ 2 + kv + 1) * (N : ℝ) ^ 4
      ≤ (N : ℝ) ^ 4 * Real.sqrt (Real.log N) / κ' := by
    rw [le_div_iff₀ hκ']
    have h := mul_le_mul_of_nonneg_left hbig (by positivity : (0:ℝ) ≤ (N : ℝ) ^ 4)
    nlinarith
  have habs : 0 ≤ |C| := abs_nonneg C
  have hN40 : (0:ℝ) ≤ (N : ℝ) ^ 4 := by positivity
  have p1 : (0:ℝ) ≤ |C| * k ^ 2 * (N : ℝ) ^ 4 := by positivity
  have p2 : (0:ℝ) ≤ k ^ 2 * (N : ℝ) ^ 4 := by positivity
  have p3 : (0:ℝ) ≤ kv * (N : ℝ) ^ 4 := by positivity
  linarith

lemma b2_exp_le (x c d : ℕ) {β A : ℝ} (hA1 : 1 ≤ A) (hβ0 : 0 ≤ β)
    (hx : ((x : ℕ) : ℝ) ≤ Real.exp (β * A)) :
    (((2 * d + 1) * (x * (1 + c) ^ (2 * d)) : ℕ) : ℝ) ≤ Real.exp (kb2C5 c d β * A) := by
  have t1 : (1 : ℝ) + (c : ℝ) ≤ Real.exp (Real.log ((c : ℝ) + 2)) := by
    rw [Real.exp_log (by positivity)]; linarith
  have t2 : ((1 : ℝ) + (c : ℝ)) ^ (2 * d) ≤ Real.exp (2 * (d : ℝ) * Real.log ((c : ℝ) + 2)) := by
    have := pow_exp_le (by positivity) t1 (2 * d)
    rw [show ((2 * d : ℕ) : ℝ) = 2 * (d : ℝ) by push_cast; ring] at this
    exact this
  have t3 : 2 * (d : ℝ) + 1 ≤ Real.exp (Real.log (2 * (d : ℝ) + 2)) := by
    rw [Real.exp_log (by positivity)]; linarith
  have t4 : (x : ℝ) * ((1 : ℝ) + (c : ℝ)) ^ (2 * d)
      ≤ Real.exp (β * A + 2 * (d : ℝ) * Real.log ((c : ℝ) + 2)) := mul_exp_le (by positivity) hx t2
  have t5 := mul_exp_le (y := (x : ℝ) * ((1 : ℝ) + (c : ℝ)) ^ (2 * d)) (by positivity) t3 t4
  push_cast
  refine t5.trans (Real.exp_le_exp.2 ?_)
  unfold kb2C5
  have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
  have hc0 : (0:ℝ) ≤ (c:ℝ) := Nat.cast_nonneg _
  have h2 : 0 ≤ Real.log (2 * (d:ℝ) + 2) := Real.log_nonneg (by linarith)
  have h3 : 0 ≤ Real.log ((c:ℝ) + 2) := Real.log_nonneg (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hA1 h2,
    mul_le_mul_of_nonneg_left hA1 (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hd0) h3)]

lemma nm_bound (N a b : ℕ) (hN : 3 ≤ N) (har : (a : ℝ) ≤ 14 * ((N : ℝ) / Real.sqrt (Real.log N)))
    (hbr : (b : ℝ) ≤ 14 * ((N : ℝ) * Real.sqrt (Real.log N))) :
    ((2 * N * (a + b) : ℕ) : ℝ) ≤ 56 * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N)) := by
  obtain ⟨-, hB1, hBA, -⟩ := basic5_facts hN
  obtain ⟨hq1, -, -⟩ := q_facts hN
  have hN0 : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have e1 : 2 * (N : ℝ) * (a : ℝ) ≤ 2 * (N : ℝ) * (14 * ((N : ℝ) / Real.sqrt (Real.log N))) :=
    mul_le_mul_of_nonneg_left har (by positivity)
  have e2 : 2 * (N : ℝ) * (b : ℝ) ≤ 2 * (N : ℝ) * (14 * ((N : ℝ) * Real.sqrt (Real.log N))) :=
    mul_le_mul_of_nonneg_left hbr (by positivity)
  have e3 : 2 * (N : ℝ) * (14 * ((N : ℝ) / Real.sqrt (Real.log N)))
      = 28 * ((N : ℝ) ^ 2 / Real.sqrt (Real.log N)) := by ring
  have e4 : 2 * (N : ℝ) * (14 * ((N : ℝ) * Real.sqrt (Real.log N)))
      = 28 * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N)) := by ring
  push_cast
  rw [e3] at e1
  rw [e4] at e2
  have : 28 * ((N : ℝ) ^ 2 / Real.sqrt (Real.log N)) ≤ 28 * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N)) := by
    linarith
  nlinarith


end NumHelpers


end FourExpAux

set_option maxHeartbeats 2000000 in
theorem solution
    (x₁ x₂ y₁ y₂ : ℂ)
    (hexp : ∀ i j : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j))) (ω ω₁ : ℂ) (hω : Transcendental ℚ ω) (Q : Polynomial (Polynomial ℤ)) (hQm : Q.Monic) (hQd : 0 < Q.natDegree)
    (hQroot : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0)
    (hQmin : ∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree → Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0)
    (D : Polynomial (Polynomial ℤ)) (E G : Fin 2 → Polynomial (Polynomial ℤ)) (H : Fin 2 → Fin 2 → Polynomial (Polynomial ℤ))
    (hD : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ≠ 0) (hE : ∀ i, ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i))
    (hG : ∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j))
    (hH : ∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (H i j))
    (κ κ' : ℝ) (hκ : 0 < κ) (hκ' : 0 < κ') :
    ∃ k : ℝ, 0 < k ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∀ M : ℕ, (M : ℝ) ≤ κ * ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ →
      ∀ q : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → Fin M → Fin Q.natDegree → ℤ,
      (∀ i j k' μ ν, |((q i j k' μ ν : ℤ) : ℝ)| ≤ Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) →
      ∀ a b s : ℕ, a < 14 * ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ → b < 14 * ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ → s < ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ / 2 →
      iteratedDeriv s (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z)) ((a : ℂ) * y₁ + (b : ℂ) * y₂) ≠ 0 →
      ‖iteratedDeriv s (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z)) ((a : ℂ) * y₁ + (b : ℂ) * y₂)‖
          ≤ Real.exp (-(((N : ℝ) ^ 4 * Real.sqrt (Real.log (N : ℝ))) / κ')) →
      ∃ P : Polynomial ℤ, P ≠ 0 ∧
        (∀ i : ℕ, |(P.coeff i : ℝ)| ≤ Real.exp (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 * Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) ∧
        (P.natDegree : ℝ) ≤ k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 / Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))) ∧
        ‖Polynomial.aeval ω P‖ < Real.exp (-(C * (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 * Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)))) * (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 / Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ)))))) := by
  classical
  have h0 : (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁)
      (Polynomial.C Polynomial.X) = ω := by simp
  have h1 : (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁)
      Polynomial.X = ω₁ := by simp
  have hφC : ∀ p : Polynomial ℤ,
      (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁) (Polynomial.C p)
        = Polynomial.eval₂ (Int.castRingHom ℂ) ω p := by
    intro p; simp
  choose mm hmm using fun i j => FourExpAux.exists_int_annihilator (hexp i j)
  obtain ⟨cD, hcD⟩ := FourExpAux.sz_exists D
  obtain ⟨cE0, hcE0⟩ := FourExpAux.sz_exists (E 0)
  obtain ⟨cE1, hcE1⟩ := FourExpAux.sz_exists (E 1)
  obtain ⟨cG0, hcG0⟩ := FourExpAux.sz_exists (G 0)
  obtain ⟨cG1, hcG1⟩ := FourExpAux.sz_exists (G 1)
  obtain ⟨cH00, hcH00⟩ := FourExpAux.sz_exists (H 0 0)
  obtain ⟨cH01, hcH01⟩ := FourExpAux.sz_exists (H 0 1)
  obtain ⟨cH10, hcH10⟩ := FourExpAux.sz_exists (H 1 0)
  obtain ⟨cH11, hcH11⟩ := FourExpAux.sz_exists (H 1 1)
  obtain ⟨cQ, hcQ⟩ := FourExpAux.sz_exists Q
  obtain ⟨c, hcdef⟩ : ∃ c, c = cD + cE0 + cE1 + cG0 + cG1 + cH00 + cH01 + cH10 + cH11 + cQ + 1 := ⟨_, rfl⟩
  have hc : 1 ≤ c := by omega
  have mono : ∀ {P : Polynomial (Polynomial ℤ)} {c' : ℕ}, FourExpAux.Sz P c' c' c' → c' ≤ c →
      FourExpAux.Sz P c c c := fun h hle => FourExpAux.sz_mono h hle hle hle
  have hcD' := mono hcD (by omega)
  have hcE : ∀ i, FourExpAux.Sz (E i) c c c := by
    intro i; fin_cases i
    · exact mono hcE0 (by omega)
    · exact mono hcE1 (by omega)
  have hcG : ∀ j, FourExpAux.Sz (G j) c c c := by
    intro j; fin_cases j
    · exact mono hcG0 (by omega)
    · exact mono hcG1 (by omega)
  have hcH : ∀ i j, FourExpAux.Sz (H i j) c c c := by
    intro i j; fin_cases i <;> fin_cases j
    · exact mono hcH00 (by omega)
    · exact mono hcH01 (by omega)
    · exact mono hcH10 (by omega)
    · exact mono hcH11 (by omega)
  have hcQ' := mono hcQ (by omega)
  obtain ⟨K, hK⟩ : ∃ K, K = ∑ i : Fin 2, ∑ j : Fin 2, ((mm i j).natDegree +
      ((mm i j).leadingCoeff.natAbs + (FourExpAux.absPoly1 (mm i j)).eval 1)) := ⟨_, rfl⟩
  have hKle : ∀ i j, (mm i j).natDegree +
      ((mm i j).leadingCoeff.natAbs + (FourExpAux.absPoly1 (mm i j)).eval 1) ≤ K := by
    intro i j
    rw [hK]
    refine le_trans ?_ (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => (mm i j).natDegree +
      ((mm i j).leadingCoeff.natAbs + (FourExpAux.absPoly1 (mm i j)).eval 1))
      (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
  have hℓ : ∀ i j, (mm i j).natDegree ≤ K := fun i j => le_trans (Nat.le_add_right _ _) (hKle i j)
  have hA : ∀ i j, (mm i j).leadingCoeff.natAbs + (FourExpAux.absPoly1 (mm i j)).eval 1 ≤ K :=
    fun i j => le_trans (Nat.le_add_left _ _) (hKle i j)
  -- the constants
  obtain ⟨lw, hlwdef⟩ : ∃ lw : ℝ, lw = Real.log (max 1 ‖ω‖) := ⟨_, rfl⟩
  obtain ⟨lw1, hlw1def⟩ : ∃ lw1 : ℝ, lw1 = Real.log (max 1 ‖ω₁‖) := ⟨_, rfl⟩
  obtain ⟨lδ, hlδdef⟩ : ∃ lδ : ℝ, lδ = Real.log (max 1
    ‖(Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁) D‖) := ⟨_, rfl⟩
  have hlw0 : 0 ≤ lw := by rw [hlwdef]; exact Real.log_nonneg (le_max_left _ _)
  have hlw10 : 0 ≤ lw1 := by rw [hlw1def]; exact Real.log_nonneg (le_max_left _ _)
  have hlδ0 : 0 ≤ lδ := by rw [hlδdef]; exact Real.log_nonneg (le_max_left _ _)
  have hkap0 := FourExpAux.kap5_nonneg c K Q.natDegree
  obtain ⟨kk, hkkdef⟩ : ∃ kk : ℝ, kk = FourExpAux.kC5 c K Q.natDegree κ lw lw1 lδ
    (FourExpAux.kap5 c K Q.natDegree) := ⟨_, rfl⟩
  obtain ⟨kv, hkvdef⟩ : ∃ kv : ℝ, kv = FourExpAux.kdeltaC5 K lδ +
    FourExpAux.kvC5 Q.natDegree lw lw1 (FourExpAux.kdegC5 c K Q.natDegree κ)
      (FourExpAux.kb2C5 c Q.natDegree (FourExpAux.betaC5 Q.natDegree κ (FourExpAux.kap5 c K Q.natDegree)))
    := ⟨_, rfl⟩
  have hβ0 := FourExpAux.beta_nonneg Q.natDegree κ _ hκ hkap0
  have hkb20 := FourExpAux.kb2_nonneg c Q.natDegree _ hβ0
  have hkh0 := FourExpAux.kh_nonneg Q.natDegree _ hkb20
  have hkdeg0 := FourExpAux.kdeg_nonneg c K Q.natDegree κ hκ
  have hkdelta0 := FourExpAux.kdelta_nonneg K lδ hlδ0
  have hkv2 := FourExpAux.kv_nonneg Q.natDegree lw lw1 _ _ hlw0 hlw10 hkdeg0 hkb20
  have hkv0 : 0 ≤ kv := by rw [hkvdef]; linarith
  have hkkpos : 0 < kk := by
    rw [hkkdef]; exact FourExpAux.kC5_pos c K Q.natDegree κ lw lw1 lδ _ hκ hkap0 hlw0 hlw10 hlδ0
  have hkhle : FourExpAux.khC5 Q.natDegree (FourExpAux.kb2C5 c Q.natDegree
      (FourExpAux.betaC5 Q.natDegree κ (FourExpAux.kap5 c K Q.natDegree))) ≤ kk := by
    rw [hkkdef]; unfold FourExpAux.kC5
    have hd0 : (0:ℝ) ≤ (Q.natDegree : ℝ) := Nat.cast_nonneg _
    have : (0:ℝ) ≤ (Q.natDegree : ℝ) * FourExpAux.kdegC5 c K Q.natDegree κ := by positivity
    linarith
  have hkdegle : (Q.natDegree : ℝ) * FourExpAux.kdegC5 c K Q.natDegree κ ≤ kk := by
    rw [hkkdef]; unfold FourExpAux.kC5
    linarith
  refine ⟨kk, hkkpos, fun C => ?_⟩
  refine ⟨max 3 ⌈Real.exp ((2 * κ' * ((|C| + 1) * kk ^ 2 + kv + 1)) ^ 2)⌉₊,
    fun N hN M hM qq hqq a b sd ha hb hsd hne hsmall => ?_⟩
  have hN3 : 3 ≤ N := by omega
  obtain ⟨hL1, hLN, -⟩ := FourExpAux.log_nat_facts hN3
  obtain ⟨hq1, hqq2, hqN⟩ := FourExpAux.q_facts hN3
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hqpos : 0 < Real.sqrt (Real.log N) := by linarith
  -- floors
  have hSu : (⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt (Real.log N) :=
    Nat.floor_le (by positivity)
  have h1u : (⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) ≤ (N : ℝ) / Real.sqrt (Real.log N) :=
    Nat.floor_le (by positivity)
  have h2u : (⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) ≤ (N : ℝ) * Real.sqrt (Real.log N) :=
    Nat.floor_le (by positivity)
  have har : (a : ℝ) ≤ 14 * ((N : ℝ) / Real.sqrt (Real.log N)) := by
    have : (a : ℝ) ≤ 14 * (⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) := by
      have : a ≤ 14 * ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ := by omega
      exact_mod_cast this
    calc (a : ℝ) ≤ 14 * (⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) := this
      _ ≤ 14 * ((N : ℝ) / Real.sqrt (Real.log N)) := by gcongr
  have hbr : (b : ℝ) ≤ 14 * ((N : ℝ) * Real.sqrt (Real.log N)) := by
    have h : (b : ℝ) ≤ 14 * (⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) := by
      have : b ≤ 14 * ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ := by omega
      exact_mod_cast this
    calc (b : ℝ) ≤ 14 * (⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) := h
      _ ≤ 14 * ((N : ℝ) * Real.sqrt (Real.log N)) := by gcongr
  -- the integer bound on the unknowns
  obtain ⟨Qb, hQbdef⟩ : ∃ Qb : ℕ, Qb = ⌈Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))⌉₊ := ⟨_, rfl⟩
  have hqb : ∀ i j k' μ ν, (qq i j k' μ ν).natAbs ≤ Qb := by
    intro i j k' μ ν
    rw [hQbdef]
    have h1 : (((qq i j k' μ ν).natAbs : ℕ) : ℝ)
        ≤ Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)))) := by
      rw [show (((qq i j k' μ ν).natAbs : ℕ) : ℝ) = |((qq i j k' μ ν : ℤ) : ℝ)| by
        rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp]
      exact hqq i j k' μ ν
    exact_mod_cast h1.trans (Nat.le_ceil _)
  -- the presentation
  obtain ⟨Pol, hPolval, hPolsz⟩ := FourExpAux.pol_exists
    (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁) h0 h1 x₁ x₂ y₁ y₂
    Q hQm hQd hQroot D E G H hE hG hH mm hmm hc hcD' hcE hcG hcH hcQ' hℓ hA
    ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ (2 * N) M (by omega) Qb qq hqb a b sd (by omega)
  -- the value is non-zero
  have hΛ : FourExpAux.epartConst mm
      ((Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁) D)
      (2 * N * (a + b)) ≠ 0 := by
    unfold FourExpAux.epartConst
    refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
    have hne0 : (mm i j) ≠ 0 := fun h => by have := (hmm i j).1; rw [h] at this; simp at this
    exact mul_ne_zero (pow_ne_zero _ hD)
      (pow_ne_zero _ (by exact_mod_cast Polynomial.leadingCoeff_ne_zero.2 hne0))
  have hPolne : (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁) Pol ≠ 0 := by
    rw [hPolval]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hD) (pow_ne_zero _ hD)) hΛ) hne
  obtain ⟨P, hPne, hPsz, hPval⟩ := FourExpAux.det_props Q Pol hQm hQd ω ω₁
    (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁) hφC h1 hQroot hQmin
    hPolne hc hcQ' hPolsz
  have hNgt3 : ¬ ((N : ℝ) ≤ 3) := by
    have : (4 : ℝ) ≤ N := by
      have : 4 ≤ N := by omega
      exact_mod_cast this
    linarith
  obtain ⟨hA1, hB1, hBA, hLA⟩ := FourExpAux.basic5_facts hN3
  have hSN2 : (⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) ≤ (N : ℝ) ^ 2 :=
    FourExpAux.floor_sq_le hN3
  have hMN2 : (M : ℝ) ≤ κ * (N : ℝ) ^ 2 := hM.trans (mul_le_mul_of_nonneg_left hSN2 hκ.le)
  have hEb : ((FourExpAux.bC5 c K M ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ (2 * N) Q.natDegree Qb a b : ℕ) : ℝ)
      ≤ Real.exp ((Real.log (4 * κ * (Q.natDegree + 1) + 4) + 6 * Real.log (N : ℝ)) +
          (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))) + 1) +
          FourExpAux.kap5 c K Q.natDegree * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)))) := by
    refine FourExpAux.bC5_exp_le c K M _ (2 * N) Q.natDegree Qb a b _ _ _
      (FourExpAux.card_bound κ hκ N _ M Q.natDegree (by omega) hSN2 hMN2) ?_
      (FourExpAux.height_bound5 c K Q.natDegree N _ a b hc hN3 hSu har hbr)
    rw [hQbdef]
    exact FourExpAux.ceil_exp_le _ (by positivity)
  -- the pieces of the value bound
  have hMB : (M : ℝ) ≤ κ * ((N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))) :=
    hM.trans (mul_le_mul_of_nonneg_left hSu hκ.le)
  have hsdS : sd ≤ ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ := by omega
  have hsdA : (sd : ℝ) ≤ (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)) := by
    have h1 : (sd : ℝ) ≤ (⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) := by exact_mod_cast hsdS
    linarith [hSu, hBA]
  have hSA : (⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ)
      ≤ (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)) := by linarith [hSu, hBA]
  have hbeta : ((FourExpAux.bC5 c K M ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ (2 * N) Q.natDegree Qb a b : ℕ) : ℝ)
      ≤ Real.exp (FourExpAux.betaC5 Q.natDegree κ (FourExpAux.kap5 c K Q.natDegree) *
          ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)))) :=
    FourExpAux.bC5_beta hκ hkap0 hA1 hLA (by linarith) hEb
  have hdxA : ((FourExpAux.dxC5 c K M ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ Q.natDegree
      + 2 * Q.natDegree * c : ℕ) : ℝ)
      ≤ FourExpAux.kdegC5 c K Q.natDegree κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))) := by
    refine (FourExpAux.dx_bound c K M _ Q.natDegree _ κ hκ hB1 hSu hMB).trans ?_
    exact mul_le_mul_of_nonneg_left hBA hkdeg0
  refine ⟨P, hPne, ?_, ?_, ?_⟩
  · rw [if_neg hNgt3]
    intro i
    have hcoef := FourExpAux.sz1_natAbs hPsz i
    have hc1 : |((P.coeff i : ℤ) : ℝ)| = (((P.coeff i).natAbs : ℕ) : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
    rw [hc1]
    have h2 : (((P.coeff i).natAbs : ℕ) : ℝ)
        ≤ ((Q.natDegree.factorial * ((2 * Q.natDegree + 1) *
          (FourExpAux.bC5 c K M ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ (2 * N) Q.natDegree Qb a b *
            (1 + c) ^ (2 * Q.natDegree))) ^ Q.natDegree : ℕ) : ℝ) := by exact_mod_cast hcoef
    refine h2.trans ((FourExpAux.height_final c Q.natDegree _ hA1 hβ0 hbeta).trans ?_)
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hkhle (by linarith))
  · rw [if_neg hNgt3]
    have hdeg := FourExpAux.sz1_natDegree hPsz
    have h1 : ((P.natDegree : ℕ) : ℝ) ≤ ((Q.natDegree *
        (FourExpAux.dxC5 c K M ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ Q.natDegree
          + 2 * Q.natDegree * c) : ℕ) : ℝ) := by exact_mod_cast hdeg
    refine h1.trans ((FourExpAux.degree_final c K Q.natDegree M _ hκ hB1 hSu hMB).trans ?_)
    exact mul_le_mul_of_nonneg_right hkdegle (by linarith)
  · rw [if_neg hNgt3, if_neg hNgt3]
    have hbigN : 2 * κ' * ((|C| + 1) * kk ^ 2 + kv + 1) ≤ Real.sqrt (Real.log (N : ℝ)) := by
      have h1 : Real.exp ((2 * κ' * ((|C| + 1) * kk ^ 2 + kv + 1)) ^ 2) ≤ (N : ℝ) := by
        have h2 := Nat.le_ceil (Real.exp ((2 * κ' * ((|C| + 1) * kk ^ 2 + kv + 1)) ^ 2))
        have h3 : (⌈Real.exp ((2 * κ' * ((|C| + 1) * kk ^ 2 + kv + 1)) ^ 2)⌉₊ : ℝ) ≤ (N : ℝ) := by
          have : ⌈Real.exp ((2 * κ' * ((|C| + 1) * kk ^ 2 + kv + 1)) ^ 2)⌉₊ ≤ N := by omega
          exact_mod_cast this
        linarith
      have h4 : (2 * κ' * ((|C| + 1) * kk ^ 2 + kv + 1)) ^ 2 ≤ Real.log (N : ℝ) := by
        rw [← Real.log_exp ((2 * κ' * ((|C| + 1) * kk ^ 2 + kv + 1)) ^ 2)]
        exact Real.log_le_log (Real.exp_pos _) h1
      have h5 : 0 ≤ 2 * κ' * ((|C| + 1) * kk ^ 2 + kv + 1) := by
        have : (0:ℝ) ≤ |C| := abs_nonneg C
        have : (0:ℝ) ≤ (|C| + 1) * kk ^ 2 := by positivity
        nlinarith
      calc 2 * κ' * ((|C| + 1) * kk ^ 2 + kv + 1)
          = Real.sqrt ((2 * κ' * ((|C| + 1) * kk ^ 2 + kv + 1)) ^ 2) := by
            rw [Real.sqrt_sq h5]
        _ ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_le_sqrt h4
    refine lt_of_le_of_lt (hPval.trans ?_)
      (FourExpAux.final_compare N hκ' hkkpos.le hkv0 hN3 hbigN)
    rw [hPolval, norm_mul]
    have hΔb : ‖(Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁) D ^ sd *
        (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁) D
          ^ ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ *
        FourExpAux.epartConst mm ((Polynomial.eval₂RingHom
          (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁) D) (2 * N * (a + b))‖
        ≤ Real.exp (FourExpAux.kdeltaC5 K lδ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)))) := by
      rw [hlδdef]
      exact FourExpAux.delta_final K sd _ _ _ mm hℓ (fun i j => le_trans (Nat.le_add_right _ _) (hA i j))
        hA1 hsdA hSA (FourExpAux.nm_bound N a b hN3 har hbr)
    have hVb : (Q.natDegree : ℝ) * max 1 ‖ω₁‖ ^ Q.natDegree *
        ((Q.natDegree.factorial : ℝ) *
          max 1 (((FourExpAux.dxC5 c K M ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ Q.natDegree
              + 2 * Q.natDegree * c : ℕ) + 1) *
            ((2 * Q.natDegree + 1) * (FourExpAux.bC5 c K M
              ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ (2 * N) Q.natDegree Qb a b *
                (1 + c) ^ (2 * Q.natDegree)) : ℕ) *
            max 1 ‖ω‖ ^ (FourExpAux.dxC5 c K M ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ Q.natDegree
              + 2 * Q.natDegree * c)) ^ Q.natDegree)
        ≤ Real.exp (FourExpAux.kvC5 Q.natDegree lw lw1 (FourExpAux.kdegC5 c K Q.natDegree κ)
            (FourExpAux.kb2C5 c Q.natDegree (FourExpAux.betaC5 Q.natDegree κ (FourExpAux.kap5 c K Q.natDegree)))
            * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)))) := by
      rw [hlwdef, hlw1def]
      exact FourExpAux.vfac_final Q.natDegree _ _ (le_max_left _ _) (le_max_left _ _) hA1 hdxA hkdeg0
        hkb20 (FourExpAux.b2_exp_le _ c Q.natDegree hA1 hβ0 hbeta)
    have hγb := hsmall
    calc ‖(Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁) D ^ sd *
          (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁) D
            ^ ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ *
          FourExpAux.epartConst mm ((Polynomial.eval₂RingHom
            (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁) D) (2 * N * (a + b))‖ *
          ‖iteratedDeriv sd (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊,
            ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
            (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree,
              ((qq i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' * z ^ (i : ℕ) *
              Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z))
            ((a : ℂ) * y₁ + (b : ℂ) * y₂)‖ *
          ((Q.natDegree : ℝ) * max 1 ‖ω₁‖ ^ Q.natDegree *
            ((Q.natDegree.factorial : ℝ) *
              max 1 (((FourExpAux.dxC5 c K M ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ Q.natDegree
                  + 2 * Q.natDegree * c : ℕ) + 1) *
                ((2 * Q.natDegree + 1) * (FourExpAux.bC5 c K M
                  ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ (2 * N) Q.natDegree Qb a b *
                    (1 + c) ^ (2 * Q.natDegree)) : ℕ) *
                max 1 ‖ω‖ ^ (FourExpAux.dxC5 c K M ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ Q.natDegree
                  + 2 * Q.natDegree * c)) ^ Q.natDegree))
        = (‖(Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁) D ^ sd *
            (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁) D
              ^ ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ *
            FourExpAux.epartConst mm ((Polynomial.eval₂RingHom
              (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁) D) (2 * N * (a + b))‖ *
            ((Q.natDegree : ℝ) * max 1 ‖ω₁‖ ^ Q.natDegree *
              ((Q.natDegree.factorial : ℝ) *
                max 1 (((FourExpAux.dxC5 c K M ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ Q.natDegree
                    + 2 * Q.natDegree * c : ℕ) + 1) *
                  ((2 * Q.natDegree + 1) * (FourExpAux.bC5 c K M
                    ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ (2 * N) Q.natDegree Qb a b *
                      (1 + c) ^ (2 * Q.natDegree)) : ℕ) *
                  max 1 ‖ω‖ ^ (FourExpAux.dxC5 c K M ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ Q.natDegree
                    + 2 * Q.natDegree * c)) ^ Q.natDegree))) *
          ‖iteratedDeriv sd (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊,
            ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
            (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree,
              ((qq i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' * z ^ (i : ℕ) *
              Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z))
            ((a : ℂ) * y₁ + (b : ℂ) * y₂)‖ := by ring
      _ ≤ Real.exp (kv * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)))) *
          Real.exp (-(((N : ℝ) ^ 4 * Real.sqrt (Real.log (N : ℝ))) / κ')) := by
        refine mul_le_mul ?_ hγb (norm_nonneg _) (Real.exp_pos _).le
        have hcomb := mul_le_mul hΔb hVb (by positivity) (Real.exp_pos _).le
        rw [← Real.exp_add] at hcomb
        refine hcomb.trans (le_of_eq ?_)
        rw [hkvdef]
        congr 1
        ring
