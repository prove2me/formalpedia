-- Prove2me | solution 1 for DerivationHitting.Commutative.wronskian_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:53:26.522255+00:00
-- url     : https://prove2.me/submissions/9f8ce400-8329-47d4-a465-c96d9388f6bf

import Definitions.Def_DerivationHitting_Commutative_DifferentialData
import Theorems.Thm_DerivationHitting_Commutative_wronskian_x_free

section
open scoped RatFunc
open DerivationHitting.Commutative

namespace DerivationHitting.Dev.XFree
noncomputable section

variable {F : Type*} [Field F]

/-- quotient rule for any representation -/
theorem rd_div (p q : Polynomial F) (hq : q ≠ 0) :
    rationalDerivative (algebraMap (Polynomial F) (RatFunc F) p /
      algebraMap (Polynomial F) (RatFunc F) q) =
    algebraMap (Polynomial F) (RatFunc F) (p.derivative * q - p * q.derivative) /
      (algebraMap (Polynomial F) (RatFunc F) q) ^ 2 := by
  set a := algebraMap (Polynomial F) (RatFunc F) p /
      algebraMap (Polynomial F) (RatFunc F) q with ha
  have hqne : algebraMap (Polynomial F) (RatFunc F) q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  have hd : algebraMap (Polynomial F) (RatFunc F) a.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero a)
  have h1 : a.num * q = p * a.denom := by
    apply RatFunc.algebraMap_injective F
    have := RatFunc.num_div_denom a
    rw [map_mul, map_mul]
    rw [div_eq_div_iff hd hqne] at this
    exact this
  have h2 := congrArg Polynomial.derivative h1
  simp only [Polynomial.derivative_mul] at h2
  unfold rationalDerivative
  rw [div_eq_div_iff (pow_ne_zero _ hd) (pow_ne_zero _ hqne), ← map_pow, ← map_pow, ← map_mul,
    ← map_mul]
  congr 1
  linear_combination (a.denom * q) * h2 + (-(a.denom.derivative * q) - q.derivative * a.denom) * h1

theorem rd_zero : rationalDerivative (0 : RatFunc F) = 0 := by
  have := rd_div (F := F) 0 1 one_ne_zero
  simpa using this

theorem rd_repr (a : RatFunc F) :
    ∃ p q : Polynomial F, q ≠ 0 ∧ a = algebraMap (Polynomial F) (RatFunc F) p /
      algebraMap (Polynomial F) (RatFunc F) q :=
  ⟨a.num, a.denom, RatFunc.denom_ne_zero a, (RatFunc.num_div_denom a).symm⟩

variable {n : ℕ}

theorem coeff_T (h : MvPolynomial (Fin n) (RatFunc F)) (m : Fin n →₀ ℕ) :
    MvPolynomial.coeff m (timeDerivative h) = rationalDerivative (MvPolynomial.coeff m h) := by
  classical
  unfold timeDerivative
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  by_cases hm : m ∈ h.support
  · rw [Finset.sum_eq_single m]
    · simp
    · intro m' _ hne; simp [hne]
    · intro hn; exact absurd hm hn
  · rw [Finset.sum_eq_zero]
    · have : MvPolynomial.coeff m h = 0 := by simpa using hm
      rw [this, rd_zero]
    · intro m' hm'
      have : m' ≠ m := fun e => hm (e ▸ hm')
      simp [this]

section Det

variable {A : Type*} [CommRing A] {K : Type*} [CommRing K] [Algebra K A]

end Det

end
end DerivationHitting.Dev.XFree

namespace DerivationHitting.Commutative
open DerivationHitting.Dev.XFree

end DerivationHitting.Commutative
end

section
open scoped RatFunc
open DerivationHitting.Commutative DerivationHitting.Dev.XFree

namespace DerivationHitting.Dev.DegBound
noncomputable section

variable {F : Type*} [Field F] {n : ℕ}

/-- polynomial-coefficient embedding -/
def phi (F : Type*) [Field F] (n : ℕ) :
    MvPolynomial (Fin n) (Polynomial F) →+* MvPolynomial (Fin n) (RatFunc F) :=
  MvPolynomial.map (algebraMap (Polynomial F) (RatFunc F))

theorem rd_alg (p : Polynomial F) :
    rationalDerivative (algebraMap (Polynomial F) (RatFunc F) p) =
      algebraMap (Polynomial F) (RatFunc F) p.derivative := by
  have := rd_div (F := F) p 1 one_ne_zero
  simpa using this

theorem rd_mul (a b : RatFunc F) :
    rationalDerivative (a * b) = rationalDerivative a * b + a * rationalDerivative b := by
  obtain ⟨p1, q1, h1, rfl⟩ := rd_repr a
  obtain ⟨p2, q2, h2, rfl⟩ := rd_repr b
  have e1 : algebraMap (Polynomial F) (RatFunc F) q1 ≠ 0 := RatFunc.algebraMap_ne_zero h1
  have e2 : algebraMap (Polynomial F) (RatFunc F) q2 ≠ 0 := RatFunc.algebraMap_ne_zero h2
  have : algebraMap (Polynomial F) (RatFunc F) p1 / algebraMap (Polynomial F) (RatFunc F) q1 *
      (algebraMap (Polynomial F) (RatFunc F) p2 / algebraMap (Polynomial F) (RatFunc F) q2) =
      algebraMap (Polynomial F) (RatFunc F) (p1 * p2) /
        algebraMap (Polynomial F) (RatFunc F) (q1 * q2) := by
    simp only [map_mul]
    field_simp
  rw [this, rd_div _ _ (mul_ne_zero h1 h2), rd_div _ _ h1, rd_div _ _ h2]
  simp only [map_add, map_mul, map_sub, Polynomial.derivative_mul, Polynomial.derivative_add, map_pow]
  field_simp
  ring

/-- the numerator operator for T -/
def T' (N : MvPolynomial (Fin n) (Polynomial F)) : MvPolynomial (Fin n) (Polynomial F) :=
  ∑ m ∈ N.support, MvPolynomial.monomial m (Polynomial.derivative (N.coeff m))

theorem coeff_T' (N : MvPolynomial (Fin n) (Polynomial F)) (m : Fin n →₀ ℕ) :
    (T' N).coeff m = Polynomial.derivative (N.coeff m) := by
  classical
  unfold T'
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  by_cases hm : m ∈ N.support
  · rw [Finset.sum_eq_single m]
    · simp
    · intro m' _ hne; simp [hne]
    · intro hn; exact absurd hm hn
  · rw [Finset.sum_eq_zero]
    · have : N.coeff m = 0 := by simpa using hm
      rw [this]; simp
    · intro m' hm'
      have : m' ≠ m := fun e => hm (e ▸ hm')
      simp [this]

theorem phi_T' (N : MvPolynomial (Fin n) (Polynomial F)) :
    phi F n (T' N) = timeDerivative (phi F n N) := by
  ext m
  simp only [phi, MvPolynomial.coeff_map, coeff_T', coeff_T, rd_alg]

theorem T_C_mul (c : RatFunc F) (h : MvPolynomial (Fin n) (RatFunc F)) :
    timeDerivative (MvPolynomial.C c * h) =
      MvPolynomial.C (rationalDerivative c) * h + MvPolynomial.C c * timeDerivative h := by
  ext m
  rw [coeff_T, MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_C_mul, coeff_T, rd_mul]

theorem D_C_mul (b : Fin n → RatFunc F) (c : RatFunc F) (h : MvPolynomial (Fin n) (RatFunc F)) :
    linearDerivation b (MvPolynomial.C c * h) =
      MvPolynomial.C (rationalDerivative c) * h + MvPolynomial.C c * linearDerivation b h := by
  unfold linearDerivation
  rw [T_C_mul]
  simp only [MvPolynomial.pderiv_C_mul, mul_add]
  have : ∑ i, MvPolynomial.C (b i) * (MvPolynomial.C c * MvPolynomial.pderiv i h) =
      MvPolynomial.C c * ∑ i, MvPolynomial.C (b i) * MvPolynomial.pderiv i h := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this]; ring

theorem D_phi (b : Fin n → RatFunc F) (N : MvPolynomial (Fin n) (Polynomial F)) :
    linearDerivation b (phi F n N) =
      phi F n (T' N) + ∑ i, MvPolynomial.C (b i) * phi F n (MvPolynomial.pderiv i N) := by
  unfold linearDerivation
  rw [phi_T']
  have : ∑ i, MvPolynomial.C (b i) * MvPolynomial.pderiv i (phi F n N) =
      ∑ i, MvPolynomial.C (b i) * phi F n (MvPolynomial.pderiv i N) :=
    Finset.sum_congr rfl fun k _ => by simp only [phi, MvPolynomial.pderiv_map]
  rw [this]

/-- the product L -/
def Lp (F : Type*) [Field F] (n : ℕ) : Polynomial F :=
  ∏ i : Fin n, (1 + Polynomial.C ((i.val + 1 : ℕ) : F) * Polynomial.X)

/-- numerators of L * b_i -/
def Bp (F : Type*) [Field F] (n : ℕ) (i : Fin n) : Polynomial F :=
  Polynomial.C ((i.val + 1 : ℕ) : F) *
    ∏ j ∈ Finset.univ.erase i, (1 + Polynomial.C ((j.val + 1 : ℕ) : F) * Polynomial.X)

theorem lin_ne (c : F) : (1 + Polynomial.C c * Polynomial.X : Polynomial F) ≠ 0 := by
  intro h
  have := congrArg (fun p => Polynomial.coeff p 0) h
  simp at this

theorem Lp_ne : Lp F n ≠ 0 := by
  unfold Lp
  exact Finset.prod_ne_zero_iff.2 fun i _ => lin_ne _

theorem lin_deg (c : F) : (1 + Polynomial.C c * Polynomial.X : Polynomial F).natDegree ≤ 1 := by
  compute_degree

theorem Lp_deg : (Lp F n).natDegree ≤ n := by
  unfold Lp
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc _ ≤ ∑ i : Fin n, 1 := Finset.sum_le_sum fun i _ => lin_deg _
    _ = n := by simp

theorem Lpd_deg : (Polynomial.derivative (Lp F n)).natDegree ≤ n :=
  (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le_of_le_add (by have := @Lp_deg F _ n; omega))

theorem Bp_deg (i : Fin n) : (Bp F n i).natDegree ≤ n := by
  unfold Bp
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc _ ≤ ∑ j ∈ Finset.univ.erase i, 1 := Finset.sum_le_sum fun i _ => lin_deg _
    _ ≤ n := by simp

theorem alg_Lp_ne : algebraMap (Polynomial F) (RatFunc F) (Lp F n) ≠ 0 :=
  RatFunc.algebraMap_ne_zero Lp_ne

theorem Lb (i : Fin n) :
    algebraMap (Polynomial F) (RatFunc F) (Lp F n) * logarithmKernel i =
      algebraMap (Polynomial F) (RatFunc F) (Bp F n i) := by
  have hne : algebraMap (Polynomial F) (RatFunc F)
      (1 + Polynomial.C ((i.val + 1 : ℕ) : F) * Polynomial.X) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (lin_ne _)
  have hL : Lp F n = (1 + Polynomial.C ((i.val + 1 : ℕ) : F) * Polynomial.X) *
      ∏ j ∈ Finset.univ.erase i, (1 + Polynomial.C ((j.val + 1 : ℕ) : F) * Polynomial.X) := by
    unfold Lp
    rw [Finset.mul_prod_erase _ (fun j : Fin n => (1 + Polynomial.C ((j.val + 1 : ℕ) : F) * Polynomial.X))
      (Finset.mem_univ i)]
  have hk : logarithmKernel i = algebraMap (Polynomial F) (RatFunc F) (Polynomial.C ((i.val + 1 : ℕ) : F)) /
      algebraMap (Polynomial F) (RatFunc F) (1 + Polynomial.C ((i.val + 1 : ℕ) : F) * Polynomial.X) := by
    unfold logarithmKernel
    simp only [map_add, map_mul, map_one, RatFunc.algebraMap_X]
    rfl
  rw [hk, hL, Bp]
  simp only [map_mul]
  field_simp

/-- derivative of (L^e)⁻¹ times L^(e+1) -/
theorem rd_inv_pow (e : ℕ) :
    rationalDerivative ((algebraMap (Polynomial F) (RatFunc F) (Lp F n) ^ e)⁻¹) *
        algebraMap (Polynomial F) (RatFunc F) (Lp F n) ^ (e + 1) =
      -((e : RatFunc F) * algebraMap (Polynomial F) (RatFunc F) (Polynomial.derivative (Lp F n))) := by
  have hL := @alg_Lp_ne F _ n
  have h1 : ((algebraMap (Polynomial F) (RatFunc F) (Lp F n)) ^ e)⁻¹ =
      algebraMap (Polynomial F) (RatFunc F) 1 /
        algebraMap (Polynomial F) (RatFunc F) (Lp F n ^ e) := by
    simp
  rw [h1, rd_div _ _ (pow_ne_zero _ Lp_ne)]
  cases e with
  | zero => simp
  | succ e =>
    rw [Polynomial.derivative_pow]
    simp only [map_mul, map_sub, map_one, map_pow, Polynomial.derivative_one, map_zero, zero_mul,
      one_mul, zero_sub, map_neg, Polynomial.derivative_C, map_natCast, Polynomial.C_eq_natCast]
    push_cast
    field_simp
    ring

def DegLe (d : ℕ) (N : MvPolynomial (Fin n) (Polynomial F)) : Prop :=
  ∀ m, (N.coeff m).natDegree ≤ d

theorem DegLe.mono {d d' : ℕ} {N : MvPolynomial (Fin n) (Polynomial F)} (h : DegLe d N)
    (hd : d ≤ d') : DegLe d' N := fun m => (h m).trans hd

theorem DegLe.zero (d : ℕ) : DegLe d (0 : MvPolynomial (Fin n) (Polynomial F)) := by
  intro m; simp

theorem DegLe.add {d : ℕ} {N M : MvPolynomial (Fin n) (Polynomial F)} (h : DegLe d N)
    (h' : DegLe d M) : DegLe d (N + M) := fun m => by
  rw [MvPolynomial.coeff_add]; exact (Polynomial.natDegree_add_le _ _).trans (max_le (h m) (h' m))

theorem DegLe.neg {d : ℕ} {N : MvPolynomial (Fin n) (Polynomial F)} (h : DegLe d N) :
    DegLe d (-N) := fun m => by
  rw [MvPolynomial.coeff_neg, Polynomial.natDegree_neg]; exact h m

theorem DegLe.sub {d : ℕ} {N M : MvPolynomial (Fin n) (Polynomial F)} (h : DegLe d N)
    (h' : DegLe d M) : DegLe d (N - M) := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem DegLe.sum {ι : Type*} (s : Finset ι) {d : ℕ} (f : ι → MvPolynomial (Fin n) (Polynomial F))
    (h : ∀ i ∈ s, DegLe d (f i)) : DegLe d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using DegLe.zero d
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem DegLe.C_mul (P : Polynomial F) {d : ℕ} {N : MvPolynomial (Fin n) (Polynomial F)}
    (h : DegLe d N) : DegLe (P.natDegree + d) (MvPolynomial.C P * N) := fun m => by
  rw [MvPolynomial.coeff_C_mul]
  exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add_left (h m) _)

theorem DegLe.pderiv (i : Fin n) {d : ℕ} {N : MvPolynomial (Fin n) (Polynomial F)}
    (h : DegLe d N) : DegLe d (MvPolynomial.pderiv i N) := fun m => by
  rw [MvPolynomial.coeff_pderiv]
  have : ((m i : Polynomial F) + 1) = Polynomial.C (((m i : ℕ) : F) + 1) := by simp
  rw [this]
  calc _ ≤ _ := Polynomial.natDegree_mul_le
    _ ≤ d + 0 := Nat.add_le_add (h _) (by rw [Polynomial.natDegree_C])
    _ = d := rfl

theorem DegLe.T' {d : ℕ} {N : MvPolynomial (Fin n) (Polynomial F)}
    (h : DegLe d N) : DegLe d (T' N) := fun m => by
  rw [coeff_T']
  exact (Polynomial.natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans (h m))

theorem DegLe.mul {d₁ d₂ : ℕ} {N M : MvPolynomial (Fin n) (Polynomial F)}
    (h : DegLe d₁ N) (h' : DegLe d₂ M) : DegLe (d₁ + d₂) (N * M) := fun m => by
  rw [MvPolynomial.coeff_mul]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
  exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add (h _) (h' _))

theorem DegLe.prod {ι : Type*} (s : Finset ι) {d : ℕ} (f : ι → MvPolynomial (Fin n) (Polynomial F))
    (h : ∀ i ∈ s, DegLe d (f i)) : DegLe (s.card * d) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, zero_mul]
    intro m
    rw [MvPolynomial.coeff_one]
    split_ifs <;> simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, add_mul, one_mul, add_comm]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem DegLe.det {q d : ℕ} (M : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) (Polynomial F)))
    (h : ∀ i j, DegLe d (M i j)) : DegLe (q * d) M.det := by
  rw [Matrix.det_apply]
  apply DegLe.sum
  intro σ _
  rw [Units.smul_def]
  have hp := DegLe.prod Finset.univ (fun i => M (σ i) i) (fun i _ => h _ _)
  simp only [Finset.card_univ, Fintype.card_fin] at hp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> rw [e]
  · simpa using hp
  · simpa using hp.neg

/-- the invariant -/
def Good (e d : ℕ) (h : MvPolynomial (Fin n) (RatFunc F)) : Prop :=
  ∃ N : MvPolynomial (Fin n) (Polynomial F), DegLe d N ∧
    h * MvPolynomial.C (algebraMap (Polynomial F) (RatFunc F) (Lp F n) ^ e) = phi F n N

theorem good_D (e d : ℕ) (h : MvPolynomial (Fin n) (RatFunc F))
    (hh : Good e d h) :
    Good (e + 1) (d + n) (linearDerivation logarithmKernel h) := by
  obtain ⟨N, hN, hhN⟩ := hh
  set ℓ := algebraMap (Polynomial F) (RatFunc F) (Lp F n) with hℓ
  have hℓne : ℓ ≠ 0 := alg_Lp_ne
  set c := (ℓ ^ e)⁻¹ with hc
  have hcl : c * ℓ ^ (e + 1) = ℓ := by
    rw [hc, pow_succ]; field_simp
  have hhc : h = MvPolynomial.C c * phi F n N := by
    rw [← hhN, ← mul_assoc, mul_comm (MvPolynomial.C c) h, mul_assoc, ← map_mul,
      hc, inv_mul_cancel₀ (pow_ne_zero _ hℓne), map_one, mul_one]
  let N' : MvPolynomial (Fin n) (Polynomial F) :=
    MvPolynomial.C (Lp F n) * T' N -
      MvPolynomial.C ((e : Polynomial F) * Polynomial.derivative (Lp F n)) * N +
      ∑ i, MvPolynomial.C (Bp F n i) * MvPolynomial.pderiv i N
  refine ⟨N', ?_, ?_⟩
  · refine DegLe.add (DegLe.sub ?_ ?_) (DegLe.sum _ _ fun i _ => ?_)
    · exact (hN.T'.C_mul (Lp F n)).mono (by have := @Lp_deg F _ n; omega)
    · refine (hN.C_mul _).mono ?_
      have h1 := @Lpd_deg F _ n
      have h2 : ((e : Polynomial F) * Polynomial.derivative (Lp F n)).natDegree ≤ n :=
        (Polynomial.natDegree_mul_le).trans (by rw [Polynomial.natDegree_natCast]; omega)
      omega
    · exact ((hN.pderiv i).C_mul _).mono (by have := @Bp_deg F _ n i; omega)
  · have hD : linearDerivation logarithmKernel h =
        MvPolynomial.C (rationalDerivative c) * phi F n N +
          MvPolynomial.C c * (phi F n (T' N) +
            ∑ i, MvPolynomial.C (logarithmKernel i) * phi F n (MvPolynomial.pderiv i N)) := by
      rw [hhc, D_C_mul, D_phi]
    rw [hD]
    have hr : rationalDerivative c * ℓ ^ (e + 1) =
        -((e : RatFunc F) * algebraMap (Polynomial F) (RatFunc F) (Polynomial.derivative (Lp F n))) :=
      rd_inv_pow e
    have hC : ∀ x y : RatFunc F, (MvPolynomial.C x : MvPolynomial (Fin n) (RatFunc F)) * MvPolynomial.C y =
        MvPolynomial.C (x * y) := fun x y => (map_mul _ _ _).symm
    have hN' : phi F n N' = MvPolynomial.C ℓ * phi F n (T' N) -
        MvPolynomial.C ((e : RatFunc F) * algebraMap (Polynomial F) (RatFunc F)
          (Polynomial.derivative (Lp F n))) * phi F n N +
        ∑ i, MvPolynomial.C (algebraMap (Polynomial F) (RatFunc F) (Bp F n i)) *
          phi F n (MvPolynomial.pderiv i N) := by
      simp only [N', map_add, map_sub, map_mul, map_sum, phi, MvPolynomial.map_C, map_natCast, hℓ]
    have key1 : MvPolynomial.C (rationalDerivative c) *
        (MvPolynomial.C (ℓ ^ (e + 1)) : MvPolynomial (Fin n) (RatFunc F)) =
        -MvPolynomial.C ((e : RatFunc F) * algebraMap (Polynomial F) (RatFunc F)
          (Polynomial.derivative (Lp F n))) := by
      rw [hC, hr, map_neg]
    have key2 : MvPolynomial.C c * (MvPolynomial.C (ℓ ^ (e + 1)) : MvPolynomial (Fin n) (RatFunc F)) =
        MvPolynomial.C ℓ := by rw [hC, hcl]
    have hS : (MvPolynomial.C ℓ : MvPolynomial (Fin n) (RatFunc F)) *
        ∑ i, MvPolynomial.C (logarithmKernel i) * phi F n (MvPolynomial.pderiv i N) =
        ∑ i, MvPolynomial.C (algebraMap (Polynomial F) (RatFunc F) (Bp F n i)) *
          phi F n (MvPolynomial.pderiv i N) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Lb i, map_mul, hℓ]
      ring
    rw [hN']
    linear_combination (phi F n N) * key1 + (phi F n (T' N)) * key2 +
      (∑ i, MvPolynomial.C (logarithmKernel i) * phi F n (MvPolynomial.pderiv i N)) * key2 + hS


theorem good_iter (m : ℕ) (h : MvPolynomial (Fin n) (RatFunc F)) (hh : Good 0 0 h) :
    Good m (m * n) ((linearDerivation (logarithmKernel : Fin n → RatFunc F))^[m] h) := by
  induction m with
  | zero => simpa using hh
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have := good_D m (m * n) _ ih
    rwa [show (m + 1) * n = m * n + n by ring]

theorem good_lift (e q d : ℕ) (hq : e ≤ q) (h : MvPolynomial (Fin n) (RatFunc F))
    (hh : Good e d h) : Good q (d + (q - e) * n) h := by
  obtain ⟨N, hN, hhN⟩ := hh
  refine ⟨N * MvPolynomial.C (Lp F n ^ (q - e)), ?_, ?_⟩
  · refine (hN.mul (d₂ := (q - e) * n) ?_).mono le_rfl
    intro m
    rw [MvPolynomial.coeff_C]
    split_ifs
    · exact (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left _ Lp_deg)
    · simp
  · rw [map_mul, ← hhN]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hq
    simp only [phi, MvPolynomial.map_C, map_pow, Nat.add_sub_cancel_left]
    rw [pow_add, mul_assoc]

theorem base_good (g : MvPolynomial (Fin n) F) : Good 0 0 (rationalPolynomial g) := by
  refine ⟨MvPolynomial.map (algebraMap F (Polynomial F)) g, ?_, ?_⟩
  · intro m
    rw [MvPolynomial.coeff_map]
    exact (Polynomial.natDegree_C _).le
  · simp only [pow_zero, map_one, mul_one, rationalPolynomial, phi, MvPolynomial.map_map]
    rfl

end
end DerivationHitting.Dev.DegBound

namespace DerivationHitting.Commutative
open DerivationHitting.Dev.DegBound

theorem chk_wronskian_degree_bound {F : Type*} [Field F] [CharZero F] {n q : ℕ}
    (g : Fin q → MvPolynomial (Fin n) F) (hclosed : derivativeClosed g) :
    ∃ A C : Polynomial F, C ≠ 0 ∧ A.natDegree ≤ n * q ^ 2 ∧
      C.natDegree ≤ n * q ^ 2 ∧
      derivationWronskian logarithmKernel g =
        MvPolynomial.C (algebraMap (Polynomial F) (RatFunc F) A /
          algebraMap (Polynomial F) (RatFunc F) C) := by
  classical
  obtain ⟨a, ha⟩ := wronskian_x_free (logarithmKernel : Fin n → RatFunc F) g hclosed
  have hrow : ∀ m j : Fin q, Good q (n * q)
      ((linearDerivation (logarithmKernel : Fin n → RatFunc F))^[m.val] (rationalPolynomial (g j))) := by
    intro m j
    have h1 := good_iter m.val _ (base_good (g j))
    have h2 := good_lift m.val q _ m.is_lt.le _ h1
    refine h2.imp fun N hN => ⟨hN.1.mono ?_, hN.2⟩
    have : m.val * n + (q - m.val) * n = n * q := by
      rw [← add_mul, Nat.add_sub_cancel' m.is_lt.le, mul_comm]
    omega
  choose M hM hMe using hrow
  set ℓ := algebraMap (Polynomial F) (RatFunc F) (Lp F n) with hℓ
  have hdet : phi F n (Matrix.of M).det =
      MvPolynomial.C (a * ℓ ^ (q * q)) := by
    rw [RingHom.map_det]
    have : (phi F n).mapMatrix (Matrix.of M) =
        (MvPolynomial.C (ℓ ^ q) : MvPolynomial (Fin n) (RatFunc F)) • (Matrix.of fun m j : Fin q =>
          (linearDerivation (logarithmKernel : Fin n → RatFunc F))^[m.val]
            (rationalPolynomial (g j))) := by
      ext m j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
        smul_eq_mul]
      rw [← hMe, mul_comm]
    rw [this, Matrix.det_smul]
    have hW : (Matrix.of fun m j : Fin q =>
          (linearDerivation (logarithmKernel : Fin n → RatFunc F))^[m.val]
            (rationalPolynomial (g j))).det = MvPolynomial.C a := ha
    rw [hW, Fintype.card_fin, ← map_pow, ← pow_mul, ← map_mul, mul_comm]
  have hdeg : DegLe (q * (n * q)) (Matrix.of M).det := DegLe.det _ hM
  refine ⟨(Matrix.of M).det.coeff 0, Lp F n ^ (q * q), pow_ne_zero _ Lp_ne, ?_, ?_, ?_⟩
  · exact (hdeg 0).trans (by nlinarith)
  · exact (Polynomial.natDegree_pow_le).trans (by
      have := @Lp_deg F _ n
      calc q * q * (Lp F n).natDegree ≤ q * q * n := Nat.mul_le_mul_left _ this
        _ = n * q ^ 2 := by ring)
  · have h0 := congrArg (MvPolynomial.coeff 0) hdet
    rw [MvPolynomial.coeff_C, if_pos rfl] at h0
    simp only [phi, MvPolynomial.coeff_map] at h0
    rw [ha, h0, map_pow, ← hℓ, mul_div_cancel_right₀ _ (pow_ne_zero _ alg_Lp_ne)]

end DerivationHitting.Commutative
end

theorem solution : type_of% @DerivationHitting.Commutative.chk_wronskian_degree_bound := @DerivationHitting.Commutative.chk_wronskian_degree_bound
