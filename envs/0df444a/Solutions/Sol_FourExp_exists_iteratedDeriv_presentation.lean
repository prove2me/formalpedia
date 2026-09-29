-- Prove2me | solution 1 for FourExp.exists_iteratedDeriv_presentation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T16:47:04.476768+00:00
-- url     : https://prove2.me/submissions/d4a43f2a-3f8f-4149-aebb-83e392ded2e1

import Mathlib
import Theorems.Thm_Transcendence_exists_int_pow_repr
import Theorems.Thm_Transcendence_length_mul_le
import Theorems.Thm_Transcendence_length_sum_le

/-!
# Integer presentations of the derivatives of the auxiliary exponential polynomial

Write `φ(P) = P(ω, ω₁)` for `P ∈ ℤ[X][Y]`, `δ = φ(D)`, `β = j x₁ + k x₂` and `ζ = a y₁ + b y₂`.

* **Leibniz.** `(z^i e^(βz))⁽ᵐ⁾(ζ) = ∑_{l ≤ m} C(m,l) i(i-1)⋯(i-l+1) ζ^(i-l) β^(m-l) e^(βζ)`,
  and the `m`-th derivative is linear in the coefficients `f_{ijk}`.
* **Polynomial factors.** Since `δβ = φ(j E₀ + k E₁)` and `δζ = φ(a G₀ + b G₁)`, for `l ≤ i < S`
  the number `δ^(m+S) ζ^(i-l) β^(m-l)` is `φ` of
  `D^l (j E₀ + k E₁)^(m-l) (a G₀ + b G₁)^(i-l) D^(S-i+l)`. For `l > i` the Leibniz term vanishes.
* **Exponential factor.** `e^(βζ) = α₀₀^(ja) α₀₁^(jb) α₁₀^(ka) α₁₁^(kb)` with `α_{pq} = e^(x_p y_q)`
  algebraic. For each `α_{pq}` there are `ℓ`, `A` and an integer `L ≠ 0` with
  `Lⁿ αⁿ = ∑_{t<ℓ} r_t α^t` and `|r_t| ≤ Aⁿ`. As `δα = φ(H)`, the number
  `δ^(ℓ-1) L^N αⁿ = L^(N-n) ∑_t r_t (δα)^t δ^(ℓ-1-t)` (for `n ≤ N`) is `φ` of an integer polynomial
  of length at most `|L|^(N-n) ℓ Aⁿ c^(ℓ-1)` and degrees at most `(ℓ-1) c`, where `c` bounds the
  data. With `N = T(a+b)` the four factors present `Λ' e^(βζ)`, `Λ' = ∏ δ^(ℓ_{pq}-1) L_{pq}^N`,
  and `Λ = δ^(m+S) Λ'`.
* **Sizes.** Lengths are controlled by `len(PQ) ≤ len(P) len(Q)` and `len(∑ Pᵢ) ≤ ∑ len(Pᵢ)`; the
  degrees in `X` and `Y` add up under products. The lengths of the `P_{ijk}` are at most
  `K^(4m+S) W^(4(N+1))` with `K = 2(1+m+S+T+a+b)c` and `W` depending only on the data, and their
  degrees at most `(2m+S)c + 4W`.
-/

namespace S7W3_exists_iteratedDeriv_presentation

open Polynomial

/-! ### Length and size of integer polynomials in two variables -/

/-- The length of `P ∈ ℤ[X][Y]`: the sum of the absolute values of all its integer coefficients. -/
noncomputable def len (P : ℤ[X][X]) : ℕ :=
  ∑ r ∈ P.support, ∑ h ∈ (P.coeff r).support, ((P.coeff r).coeff h).natAbs

lemma len_mul (P Q : ℤ[X][X]) : len (P * Q) ≤ len P * len Q :=
  Transcendence.length_mul_le P Q

lemma len_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ[X][X]) :
    len (∑ i ∈ s, f i) ≤ ∑ i ∈ s, len (f i) :=
  Transcendence.length_sum_le s f

lemma len_add (P Q : ℤ[X][X]) : len (P + Q) ≤ len P + len Q := by
  have h := len_sum (Finset.univ : Finset (Fin 2)) ![P, Q]
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
  exact h

lemma len_CC (z : ℤ) : len (C (C z)) = z.natAbs := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [Polynomial.C_0, Polynomial.C_0, len, Polynomial.support_zero, Finset.sum_empty,
      Int.natAbs_zero]
  · rw [len, Polynomial.support_C (Polynomial.C_ne_zero.2 hz), Finset.sum_singleton,
      Polynomial.coeff_C_zero, Polynomial.support_C hz, Finset.sum_singleton,
      Polynomial.coeff_C_zero]

/-- `P` has length at most `b`, and degrees at most `d` in `X` and in `Y`. -/
def Sz (P : ℤ[X][X]) (b d : ℕ) : Prop :=
  len P ≤ b ∧ (∀ r, (P.coeff r).natDegree ≤ d) ∧ P.natDegree ≤ d

lemma sz_mono {P : ℤ[X][X]} {b b' d d' : ℕ} (h : Sz P b d) (hb : b ≤ b') (hd : d ≤ d') :
    Sz P b' d' :=
  ⟨h.1.trans hb, fun r => (h.2.1 r).trans hd, h.2.2.trans hd⟩

lemma sz_mul {P Q : ℤ[X][X]} {b₁ b₂ d₁ d₂ : ℕ} (hP : Sz P b₁ d₁) (hQ : Sz Q b₂ d₂) :
    Sz (P * Q) (b₁ * b₂) (d₁ + d₂) := by
  refine ⟨(len_mul P Q).trans (Nat.mul_le_mul hP.1 hQ.1), fun r => ?_,
    Polynomial.natDegree_mul_le.trans (Nat.add_le_add hP.2.2 hQ.2.2)⟩
  rw [Polynomial.coeff_mul]
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun x _ =>
    Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hP.2.1 x.1) (hQ.2.1 x.2))

lemma sz_add {P Q : ℤ[X][X]} {b₁ b₂ d : ℕ} (hP : Sz P b₁ d) (hQ : Sz Q b₂ d) :
    Sz (P + Q) (b₁ + b₂) d := by
  refine ⟨(len_add P Q).trans (Nat.add_le_add hP.1 hQ.1), fun r => ?_,
    (Polynomial.natDegree_add_le P Q).trans (max_le hP.2.2 hQ.2.2)⟩
  rw [Polynomial.coeff_add]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le (hP.2.1 r) (hQ.2.1 r))

lemma sz_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ[X][X]) {b d : ℕ}
    (h : ∀ i ∈ s, Sz (f i) b d) : Sz (∑ i ∈ s, f i) (s.card * b) d := by
  refine ⟨(len_sum s f).trans ?_, fun r => ?_,
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => (h i hi).2.2⟩
  · rw [← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i hi => (h i hi).1
  · rw [Polynomial.finsetSum_coeff]
    exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => (h i hi).2.1 r

lemma sz_CC (z : ℤ) : Sz (C (C z)) z.natAbs 0 := by
  refine ⟨(len_CC z).le, fun r => ?_, (Polynomial.natDegree_C _).le⟩
  rw [Polynomial.coeff_C]
  split_ifs
  · exact (Polynomial.natDegree_C z).le
  · exact Polynomial.natDegree_zero.le

lemma sz_CN (n : ℕ) : Sz (C (C (n : ℤ))) n 0 :=
  sz_CC (n : ℤ)

lemma sz_one : Sz 1 1 0 := by
  have h := sz_CC 1
  rw [Polynomial.C_1, Polynomial.C_1] at h
  exact h

lemma sz_pow {P : ℤ[X][X]} {b d : ℕ} (h : Sz P b d) : ∀ n : ℕ, Sz (P ^ n) (b ^ n) (n * d)
  | 0 => by
    rw [pow_zero, pow_zero, Nat.zero_mul]
    exact sz_one
  | n + 1 => by
    rw [pow_succ, pow_succ, Nat.succ_mul]
    exact sz_mul (sz_pow h n) h

lemma sz_exists (P : ℤ[X][X]) : ∃ c, Sz P c c := by
  refine ⟨len P + (∑ k ∈ Finset.range (P.natDegree + 1), (P.coeff k).natDegree) + P.natDegree,
    by omega, fun r => ?_, by omega⟩
  by_cases hr : r ≤ P.natDegree
  · have : (P.coeff r).natDegree ≤ ∑ k ∈ Finset.range (P.natDegree + 1), (P.coeff k).natDegree :=
      Finset.single_le_sum (f := fun k => (P.coeff k).natDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hr))
    omega
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.1 hr), Polynomial.natDegree_zero]
    exact Nat.zero_le _

lemma sz_exists_fam {ι : Type*} [Fintype ι] (F : ι → ℤ[X][X]) : ∃ c, ∀ i, Sz (F i) c c := by
  choose c hc using fun i => sz_exists (F i)
  have hle : ∀ i, c i ≤ ∑ i', c i' := fun i =>
    Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact ⟨∑ i, c i, fun i => sz_mono (hc i) (hle i) (hle i)⟩

lemma exists_bound_fin2 (w : Fin 2 → Fin 2 → ℕ) : ∃ W, ∀ p q, w p q ≤ W :=
  ⟨∑ p, ∑ q, w p q, fun p q =>
    (Finset.single_le_sum (f := fun q' => w p q') (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ q)).trans
      (Finset.single_le_sum (f := fun p' => ∑ q', w p' q') (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ p))⟩

lemma succ_le_two_pow : ∀ m : ℕ, m + 1 ≤ 2 ^ m
  | 0 => le_rfl
  | m + 1 => by
    have := succ_le_two_pow m
    rw [pow_succ]
    omega

/-! ### Values of integer polynomials -/

lemma phi_CC (φ : ℤ[X][X] →+* ℂ) (z : ℤ) : φ (C (C z)) = (z : ℂ) :=
  eq_intCast (φ.comp ((C : ℤ[X] →+* ℤ[X][X]).comp (C : ℤ →+* ℤ[X]))) z

/-- If `u φ(D) = φ(U)` and `v φ(D) = φ(V)`, then `(p u + q v) φ(D) = φ(p U + q V)`. -/
lemma lin_eval (φ : ℤ[X][X] →+* ℂ) {u v : ℂ} {Dp U V : ℤ[X][X]} (hU : u * φ Dp = φ U)
    (hV : v * φ Dp = φ V) (p q : ℕ) :
    ((p : ℂ) * u + (q : ℂ) * v) * φ Dp = φ (C (C (p : ℤ)) * U + C (C (q : ℤ)) * V) := by
  rw [map_add φ, map_mul φ, map_mul φ, phi_CC φ, phi_CC φ, ← hU, ← hV, Int.cast_natCast,
    Int.cast_natCast]
  ring

lemma sz_lin {U V : ℤ[X][X]} {c : ℕ} (hU : Sz U c c) (hV : Sz V c c) (p q : ℕ) :
    Sz (C (C (p : ℤ)) * U + C (C (q : ℤ)) * V) ((p + q) * c) c :=
  sz_mono (sz_add (sz_mul (sz_CN p) hU) (sz_mul (sz_CN q) hV)) (Nat.add_mul p q c).symm.le
    (Nat.zero_add c).le

/-! ### The four exponential factors -/

/-- With `r` the coordinates of `Lⁿ αⁿ` in the basis `1, α, …, α^(ℓ-1)` and `φ(H) = α φ(D)`, this
integer polynomial takes the value `φ(D)^(ℓ-1) Lⁿ αⁿ`. -/
noncomputable def expPres (ℓ : ℕ) (r : ℕ → ℤ) (Hp Dp : ℤ[X][X]) : ℤ[X][X] :=
  ∑ t ∈ Finset.range ℓ, C (C (r t)) * Hp ^ t * Dp ^ (ℓ - 1 - t)

lemma expPres_eval (φ : ℤ[X][X] →+* ℂ) (ℓ : ℕ) (r : ℕ → ℤ) (Hp Dp : ℤ[X][X]) {α : ℂ}
    (hH : α * φ Dp = φ Hp) :
    φ (expPres ℓ r Hp Dp) = φ Dp ^ (ℓ - 1) * ∑ t ∈ Finset.range ℓ, (r t : ℂ) * α ^ t := by
  rw [expPres, map_sum φ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  have hsplit : φ Dp ^ (ℓ - 1) = φ Dp ^ t * φ Dp ^ (ℓ - 1 - t) := by
    rw [← pow_add]
    congr 1
    omega
  rw [map_mul φ, map_mul φ, map_pow φ, map_pow φ, ← hH, phi_CC φ, hsplit, mul_pow]
  ring

lemma sz_expPres (ℓ : ℕ) (r : ℕ → ℤ) {Hp Dp : ℤ[X][X]} {c R : ℕ} (hH : Sz Hp c c)
    (hD : Sz Dp c c) (hr : ∀ t, (r t).natAbs ≤ R) :
    Sz (expPres ℓ r Hp Dp) (ℓ * (R * c ^ (ℓ - 1))) ((ℓ - 1) * c) := by
  have h : Sz (expPres ℓ r Hp Dp) ((Finset.range ℓ).card * (R * c ^ (ℓ - 1))) ((ℓ - 1) * c) :=
    sz_sum (Finset.range ℓ) _ fun t ht => by
      have ht' := Finset.mem_range.1 ht
      have he : t + (ℓ - 1 - t) = ℓ - 1 := by omega
      refine sz_mono (sz_mul (sz_mul (sz_CC (r t)) (sz_pow hH t)) (sz_pow hD (ℓ - 1 - t))) ?_ ?_
      · rw [Nat.mul_assoc, ← pow_add, he]
        exact Nat.mul_le_mul_right _ (hr t)
      · rw [Nat.zero_add, ← Nat.add_mul, he]
  rw [Finset.card_range] at h
  exact h

/-- `φ(D)^(ℓ-1) L^N αⁿ` as an integer polynomial, for `n ≤ N`. -/
noncomputable def fac (ℓ : ℕ) (r : ℕ → ℕ → ℤ) (Lc : ℤ) (Hp Dp : ℤ[X][X]) (N n : ℕ) : ℤ[X][X] :=
  C (C (Lc ^ (N - n))) * expPres ℓ (r n) Hp Dp

lemma fac_eval (φ : ℤ[X][X] →+* ℂ) (ℓ : ℕ) (r : ℕ → ℕ → ℤ) (Lc : ℤ) (Hp Dp : ℤ[X][X]) {α : ℂ}
    (hH : α * φ Dp = φ Hp)
    (hr : ∀ n, (Lc : ℂ) ^ n * α ^ n = ∑ t ∈ Finset.range ℓ, (r n t : ℂ) * α ^ t)
    {N n : ℕ} (hn : n ≤ N) :
    φ (fac ℓ r Lc Hp Dp N n) = φ Dp ^ (ℓ - 1) * (Lc : ℂ) ^ N * α ^ n := by
  rw [fac, map_mul φ, phi_CC φ, expPres_eval φ ℓ (r n) Hp Dp hH, ← hr n, Int.cast_pow]
  have hsplit : (Lc : ℂ) ^ N = (Lc : ℂ) ^ (N - n) * (Lc : ℂ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hn]
  rw [hsplit]
  ring

lemma sz_fac (ℓ : ℕ) (r : ℕ → ℕ → ℤ) (Lc : ℤ) {Hp Dp : ℤ[X][X]} {c A W : ℕ}
    (hH : Sz Hp c c) (hD : Sz Dp c c) (hr : ∀ n t, (r n t).natAbs ≤ A ^ n)
    (hW : ℓ * c ^ (ℓ - 1) ≤ W ∧ (ℓ - 1) * c ≤ W ∧ Lc.natAbs ≤ W ∧ A ≤ W) {N n : ℕ}
    (hn : n ≤ N) : Sz (fac ℓ r Lc Hp Dp N n) (W ^ (N + 1)) W := by
  refine sz_mono (sz_mul (sz_CC _) (sz_expPres ℓ (r n) hH hD (hr n))) ?_
    ((Nat.zero_add _).trans_le hW.2.1)
  rw [Int.natAbs_pow]
  calc Lc.natAbs ^ (N - n) * (ℓ * (A ^ n * c ^ (ℓ - 1)))
      = Lc.natAbs ^ (N - n) * A ^ n * (ℓ * c ^ (ℓ - 1)) := by ring
    _ ≤ W ^ (N - n) * W ^ n * W :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hW.2.2.1 _)
        (Nat.pow_le_pow_left hW.2.2.2 _)) hW.1
    _ = W ^ (N + 1) := by rw [← pow_add, Nat.sub_add_cancel hn, pow_succ]

/-- The product of the four factors, presenting `Λ' e^((j x₁ + k x₂)(a y₁ + b y₂))`. -/
noncomputable def epart (ℓ : Fin 2 → Fin 2 → ℕ) (r : Fin 2 → Fin 2 → ℕ → ℕ → ℤ)
    (L : Fin 2 → Fin 2 → ℤ) (H : Fin 2 → Fin 2 → ℤ[X][X]) (Dp : ℤ[X][X]) (N a b j k : ℕ) :
    ℤ[X][X] :=
  fac (ℓ 0 0) (r 0 0) (L 0 0) (H 0 0) Dp N (j * a) *
    fac (ℓ 0 1) (r 0 1) (L 0 1) (H 0 1) Dp N (j * b) *
    fac (ℓ 1 0) (r 1 0) (L 1 0) (H 1 0) Dp N (k * a) *
    fac (ℓ 1 1) (r 1 1) (L 1 1) (H 1 1) Dp N (k * b)

/-- The constant `Λ' = ∏_{p,q} δ^(ℓ_{pq}-1) L_{pq}^N`. -/
noncomputable def lam (δ : ℂ) (ℓ : Fin 2 → Fin 2 → ℕ) (L : Fin 2 → Fin 2 → ℤ) (N : ℕ) : ℂ :=
  δ ^ (ℓ 0 0 - 1) * (L 0 0 : ℂ) ^ N * (δ ^ (ℓ 0 1 - 1) * (L 0 1 : ℂ) ^ N) *
    (δ ^ (ℓ 1 0 - 1) * (L 1 0 : ℂ) ^ N) * (δ ^ (ℓ 1 1 - 1) * (L 1 1 : ℂ) ^ N)

lemma exp_split (x₁ x₂ y₁ y₂ : ℂ) (a b j k : ℕ) :
    Complex.exp (((j : ℂ) * x₁ + (k : ℂ) * x₂) * ((a : ℂ) * y₁ + (b : ℂ) * y₂)) =
      Complex.exp (![x₁, x₂] 0 * ![y₁, y₂] 0) ^ (j * a) *
        Complex.exp (![x₁, x₂] 0 * ![y₁, y₂] 1) ^ (j * b) *
        Complex.exp (![x₁, x₂] 1 * ![y₁, y₂] 0) ^ (k * a) *
        Complex.exp (![x₁, x₂] 1 * ![y₁, y₂] 1) ^ (k * b) := by
  show _ = Complex.exp (x₁ * y₁) ^ (j * a) * Complex.exp (x₁ * y₂) ^ (j * b) *
    Complex.exp (x₂ * y₁) ^ (k * a) * Complex.exp (x₂ * y₂) ^ (k * b)
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma epart_eval (φ : ℤ[X][X] →+* ℂ) (x₁ x₂ y₁ y₂ : ℂ) (ℓ : Fin 2 → Fin 2 → ℕ)
    (r : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (L : Fin 2 → Fin 2 → ℤ) (H : Fin 2 → Fin 2 → ℤ[X][X])
    (Dp : ℤ[X][X]) (hH : ∀ p q, Complex.exp (![x₁, x₂] p * ![y₁, y₂] q) * φ Dp = φ (H p q))
    (hr : ∀ p q n, (L p q : ℂ) ^ n * Complex.exp (![x₁, x₂] p * ![y₁, y₂] q) ^ n =
      ∑ t ∈ Finset.range (ℓ p q), (r p q n t : ℂ) * Complex.exp (![x₁, x₂] p * ![y₁, y₂] q) ^ t)
    {N a b j k : ℕ} (h1 : j * a ≤ N) (h2 : j * b ≤ N) (h3 : k * a ≤ N) (h4 : k * b ≤ N) :
    φ (epart ℓ r L H Dp N a b j k) = lam (φ Dp) ℓ L N *
      Complex.exp (((j : ℂ) * x₁ + (k : ℂ) * x₂) * ((a : ℂ) * y₁ + (b : ℂ) * y₂)) := by
  rw [epart, map_mul φ, map_mul φ, map_mul φ,
    fac_eval φ _ _ _ _ _ (hH 0 0) (hr 0 0) h1, fac_eval φ _ _ _ _ _ (hH 0 1) (hr 0 1) h2,
    fac_eval φ _ _ _ _ _ (hH 1 0) (hr 1 0) h3, fac_eval φ _ _ _ _ _ (hH 1 1) (hr 1 1) h4,
    exp_split x₁ x₂ y₁ y₂ a b j k, lam]
  ring

lemma sz_epart (ℓ : Fin 2 → Fin 2 → ℕ) (r : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (L : Fin 2 → Fin 2 → ℤ)
    (A : Fin 2 → Fin 2 → ℕ) {H : Fin 2 → Fin 2 → ℤ[X][X]} {Dp : ℤ[X][X]} {c W : ℕ}
    (hH : ∀ p q, Sz (H p q) c c) (hD : Sz Dp c c)
    (hr : ∀ p q n t, (r p q n t).natAbs ≤ A p q ^ n)
    (hW : ∀ p q, ℓ p q * c ^ (ℓ p q - 1) ≤ W ∧ (ℓ p q - 1) * c ≤ W ∧ (L p q).natAbs ≤ W ∧
      A p q ≤ W)
    {N a b j k : ℕ} (h1 : j * a ≤ N) (h2 : j * b ≤ N) (h3 : k * a ≤ N) (h4 : k * b ≤ N) :
    Sz (epart ℓ r L H Dp N a b j k) (W ^ (4 * (N + 1))) (4 * W) := by
  have hf : ∀ p q n, n ≤ N → Sz (fac (ℓ p q) (r p q) (L p q) (H p q) Dp N n) (W ^ (N + 1)) W :=
    fun p q n hn => sz_fac (ℓ p q) (r p q) (L p q) (hH p q) hD (hr p q) (hW p q) hn
  exact sz_mono (sz_mul (sz_mul (sz_mul (hf 0 0 _ h1) (hf 0 1 _ h2)) (hf 1 0 _ h3)) (hf 1 1 _ h4))
    (le_of_eq (by ring)) (by omega)

lemma lam_ne_zero {δ : ℂ} (hδ : δ ≠ 0) (ℓ : Fin 2 → Fin 2 → ℕ) {L : Fin 2 → Fin 2 → ℤ}
    (hL : ∀ p q, L p q ≠ 0) (N : ℕ) : lam δ ℓ L N ≠ 0 := by
  have hf : ∀ p q, δ ^ (ℓ p q - 1) * (L p q : ℂ) ^ N ≠ 0 := fun p q =>
    mul_ne_zero (pow_ne_zero _ hδ) (pow_ne_zero _ (Int.cast_ne_zero.2 (hL p q)))
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hf 0 0) (hf 0 1)) (hf 1 0)) (hf 1 1)

lemma norm_mul_le_pow {x y : ℂ} {C : ℝ} {p q : ℕ} (hx : ‖x‖ ≤ C ^ p) (hy : ‖y‖ ≤ C ^ q) :
    ‖x * y‖ ≤ C ^ (p + q) := by
  rw [norm_mul, pow_add]
  exact mul_le_mul hx hy (norm_nonneg y) ((norm_nonneg x).trans hx)

lemma norm_pow_le_pow {x : ℂ} {C : ℝ} (hx : ‖x‖ ≤ C) (n : ℕ) : ‖x ^ n‖ ≤ C ^ n := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg x) hx n

lemma norm_lam_le {δ : ℂ} {C : ℝ} (hδ : ‖δ‖ ≤ C) (ℓ : Fin 2 → Fin 2 → ℕ)
    {L : Fin 2 → Fin 2 → ℤ} (hL : ∀ p q, ‖(L p q : ℂ)‖ ≤ C) (N : ℕ) :
    ‖lam δ ℓ L N‖ ≤
      C ^ (ℓ 0 0 - 1 + N + (ℓ 0 1 - 1 + N) + (ℓ 1 0 - 1 + N) + (ℓ 1 1 - 1 + N)) := by
  have hf : ∀ p q, ‖δ ^ (ℓ p q - 1) * (L p q : ℂ) ^ N‖ ≤ C ^ (ℓ p q - 1 + N) := fun p q =>
    norm_mul_le_pow (norm_pow_le_pow hδ _) (norm_pow_le_pow (hL p q) N)
  exact norm_mul_le_pow (norm_mul_le_pow (norm_mul_le_pow (hf 0 0) (hf 0 1)) (hf 1 0)) (hf 1 1)

/-! ### The presentation of the derivative -/

/-- Leibniz's rule for the exponential polynomial, linearly in its coefficients. -/
lemma iteratedDeriv_expPoly (S T m : ℕ) (x₁ x₂ : ℂ) (f : Fin S → Fin T → Fin T → ℂ) (w : ℂ) :
    iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
        f i j k * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z)) w =
      ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T, f i j k *
        ∑ l ∈ Finset.range (m + 1), (m.choose l : ℂ) *
          (((i : ℕ).descFactorial l : ℂ) * w ^ ((i : ℕ) - l)) *
          ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) ^ (m - l) *
            Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * w)) := by
  have key : ∀ (i : Fin S) (j k : Fin T), iteratedDeriv m (fun z : ℂ =>
      f i j k * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z)) w =
      f i j k * ∑ l ∈ Finset.range (m + 1), (m.choose l : ℂ) *
        (((i : ℕ).descFactorial l : ℂ) * w ^ ((i : ℕ) - l)) *
          ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) ^ (m - l) *
            Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * w)) := by
    intro i j k
    have h1 : ContDiffAt ℂ m (fun z : ℂ => z ^ (i : ℕ)) w := (contDiff_id.pow _).contDiffAt
    have h2 : ContDiffAt ℂ m (fun z : ℂ =>
        Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z)) w := by fun_prop
    simp_rw [mul_assoc (f i j k)]
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_mul h1 h2]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [iteratedDeriv_pow, iteratedDeriv_cexp_const_mul]
  rw [iteratedDeriv_fun_sum (fun i _ => by fun_prop)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDeriv_fun_sum (fun j _ => by fun_prop)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedDeriv_fun_sum (fun k _ => by fun_prop)]
  exact Finset.sum_congr rfl fun k _ => key i j k

/-- The integer polynomial `∑_{l ≤ m} C(m,l) i(i-1)⋯(i-l+1) D^l B^(m-l) Z^(i-l) D^(S-i+l) e`. -/
noncomputable def pres (Dp Bp Zp ep : ℤ[X][X]) (S m i : ℕ) : ℤ[X][X] :=
  ∑ l ∈ Finset.range (m + 1), C (C ((m.choose l * i.descFactorial l : ℕ) : ℤ)) *
    (Dp ^ l * Bp ^ (m - l) * Zp ^ (i - l) * Dp ^ (S - i + l)) * ep

lemma pres_eval (φ : ℤ[X][X] →+* ℂ) {Dp Bp Zp ep : ℤ[X][X]} {β ζ Λ' e : ℂ}
    (hB : β * φ Dp = φ Bp) (hZ : ζ * φ Dp = φ Zp) (he : φ ep = Λ' * e) {S m i : ℕ} (hi : i < S) :
    φ (pres Dp Bp Zp ep S m i) = φ Dp ^ (m + S) * Λ' *
      ∑ l ∈ Finset.range (m + 1), (m.choose l : ℂ) * ((i.descFactorial l : ℂ) * ζ ^ (i - l)) *
        (β ^ (m - l) * e) := by
  rw [pres, map_sum φ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  simp only [map_mul φ, map_pow φ]
  rw [← hB, ← hZ, he, phi_CC φ, Int.cast_natCast, Nat.cast_mul]
  rcases Nat.lt_or_ge i l with h | h
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 h, Nat.cast_zero]
    ring
  · have hδ : φ Dp ^ (m + S) =
        φ Dp ^ l * φ Dp ^ (m - l) * φ Dp ^ (i - l) * φ Dp ^ (S - i + l) := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega
    rw [hδ, mul_pow, mul_pow]
    ring

lemma sz_pres {Dp Bp Zp ep : ℤ[X][X]} {K c E dE S m i : ℕ} (hD : Sz Dp K c) (hB : Sz Bp K c)
    (hZ : Sz Zp K c) (he : Sz ep E dE) (hi : i < S) (hK : 2 * (i + 1) ≤ K) :
    Sz (pres Dp Bp Zp ep S m i) (K ^ (4 * m + S) * E) ((2 * m + S) * c + dE) := by
  have hK0 : 0 < K := by omega
  have hcoef : ∀ l, l ≤ m → m.choose l * i.descFactorial l ≤ K ^ m := fun l hl =>
    calc m.choose l * i.descFactorial l ≤ 2 ^ m * (i + 1) ^ m :=
          Nat.mul_le_mul (Nat.choose_le_two_pow m l)
            ((Nat.descFactorial_le_pow i l).trans ((Nat.pow_le_pow_left (Nat.le_succ i) l).trans
              (Nat.pow_le_pow_right (Nat.succ_pos i) hl)))
      _ = (2 * (i + 1)) ^ m := (Nat.mul_pow 2 (i + 1) m).symm
      _ ≤ K ^ m := Nat.pow_le_pow_left hK m
  have h : Sz (pres Dp Bp Zp ep S m i) ((Finset.range (m + 1)).card * (K ^ (3 * m + S) * E))
      ((2 * m + S) * c + dE) :=
    sz_sum (Finset.range (m + 1)) _ fun l hl => by
      have hl' := Finset.mem_range.1 hl
      refine sz_mono (sz_mul (sz_mul (sz_CN _) (sz_mul (sz_mul (sz_mul (sz_pow hD l)
        (sz_pow hB (m - l))) (sz_pow hZ (i - l))) (sz_pow hD (S - i + l)))) he) ?_ ?_
      · refine Nat.mul_le_mul_right E ?_
        rw [← pow_add, ← pow_add, ← pow_add]
        calc m.choose l * i.descFactorial l * K ^ (l + (m - l) + (i - l) + (S - i + l))
            ≤ K ^ m * K ^ (2 * m + S) :=
              Nat.mul_le_mul (hcoef l (by omega)) (Nat.pow_le_pow_right hK0 (by omega))
          _ = K ^ (3 * m + S) := by rw [← pow_add, show m + (2 * m + S) = 3 * m + S by omega]
      · rw [Nat.zero_add, ← Nat.add_mul, ← Nat.add_mul, ← Nat.add_mul]
        exact Nat.add_le_add_right (Nat.mul_le_mul_right c (by omega)) dE
  refine sz_mono h ?_ le_rfl
  rw [Finset.card_range]
  calc (m + 1) * (K ^ (3 * m + S) * E) ≤ K ^ m * (K ^ (3 * m + S) * E) :=
        Nat.mul_le_mul_right _ ((succ_le_two_pow m).trans (Nat.pow_le_pow_left (by omega) m))
    _ = K ^ (4 * m + S) * E := by
        rw [← Nat.mul_assoc, ← pow_add, show m + (3 * m + S) = 4 * m + S by omega]

/-- The polynomial `P_{ijk}`. -/
noncomputable def Ppol (ℓ : Fin 2 → Fin 2 → ℕ) (r : Fin 2 → Fin 2 → ℕ → ℕ → ℤ)
    (L : Fin 2 → Fin 2 → ℤ) (D : ℤ[X][X]) (E G : Fin 2 → ℤ[X][X]) (H : Fin 2 → Fin 2 → ℤ[X][X])
    (S a b m N i j k : ℕ) : ℤ[X][X] :=
  pres D (C (C (j : ℤ)) * E 0 + C (C (k : ℤ)) * E 1) (C (C (a : ℤ)) * G 0 + C (C (b : ℤ)) * G 1)
    (epart ℓ r L H D N a b j k) S m i

/-- The statement, for an arbitrary ring homomorphism `φ : ℤ[X][Y] → ℂ`. -/
theorem main (x₁ x₂ y₁ y₂ : ℂ)
    (hexp : ∀ i j : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j)))
    (φ : ℤ[X][X] →+* ℂ) (D : ℤ[X][X]) (E G : Fin 2 → ℤ[X][X]) (H : Fin 2 → Fin 2 → ℤ[X][X])
    (hD : φ D ≠ 0) (hE : ∀ i, ![x₁, x₂] i * φ D = φ (E i))
    (hG : ∀ j, ![y₁, y₂] j * φ D = φ (G j))
    (hH : ∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) * φ D = φ (H i j)) :
    ∃ c : ℕ, ∀ S T a b m : ℕ, ∃ Λ : ℂ, Λ ≠ 0 ∧ ‖Λ‖ ≤ (c : ℝ) ^ (c * (1 + m + S + T * (a + b))) ∧
      ∃ P : Fin S → Fin T → Fin T → ℤ[X][X],
        (∀ i j k, len (P i j k) ≤
          c ^ (c * (1 + m + S + T * (a + b))) * (1 + m + S + T + a + b) ^ (c * (1 + m + S))) ∧
        (∀ i j k r, ((P i j k).coeff r).natDegree ≤ c * (1 + m + S)) ∧
        (∀ i j k, (P i j k).natDegree ≤ c * (1 + m + S)) ∧
        ∀ f : Fin S → Fin T → Fin T → ℂ,
          Λ * iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
              f i j k * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
            ((a : ℂ) * y₁ + (b : ℂ) * y₂) =
          ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T, f i j k * φ (P i j k) := by
  -- integer relations for the powers of the four algebraic exponentials
  choose ℓ A L hL hr using fun p q => Transcendence.exists_int_pow_repr (hexp p q)
  choose r hr1 hr2 using hr
  -- a common size `c₀` for the data
  obtain ⟨cD, hcD⟩ := sz_exists D
  obtain ⟨cE, hcE⟩ := sz_exists_fam E
  obtain ⟨cG, hcG⟩ := sz_exists_fam G
  obtain ⟨cH, hcH⟩ := sz_exists_fam (fun pq : Fin 2 × Fin 2 => H pq.1 pq.2)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = cD + cE + cG + cH + 1 := ⟨_, rfl⟩
  have hD0 : Sz D c₀ c₀ := sz_mono hcD (by omega) (by omega)
  have hE0 : ∀ p, Sz (E p) c₀ c₀ := fun p => sz_mono (hcE p) (by omega) (by omega)
  have hG0 : ∀ q, Sz (G q) c₀ c₀ := fun q => sz_mono (hcG q) (by omega) (by omega)
  have hH0 : ∀ p q, Sz (H p q) c₀ c₀ := fun p q => sz_mono (hcH (p, q)) (by omega) (by omega)
  -- the constants of the four exponential factors
  obtain ⟨W, hW⟩ := exists_bound_fin2 fun p q =>
    ℓ p q * c₀ ^ (ℓ p q - 1) + (ℓ p q - 1) * c₀ + (L p q).natAbs + A p q + ℓ p q
  have hW' : ∀ p q, ℓ p q * c₀ ^ (ℓ p q - 1) ≤ W ∧ (ℓ p q - 1) * c₀ ≤ W ∧
      (L p q).natAbs ≤ W ∧ A p q ≤ W := fun p q => by
    have h : ℓ p q * c₀ ^ (ℓ p q - 1) + (ℓ p q - 1) * c₀ + (L p q).natAbs + A p q + ℓ p q ≤ W :=
      hW p q
    exact ⟨by omega, by omega, by omega, by omega⟩
  have hℓW : ∀ p q, ℓ p q ≤ W := fun p q => by
    have h : ℓ p q * c₀ ^ (ℓ p q - 1) + (ℓ p q - 1) * c₀ + (L p q).natAbs + A p q + ℓ p q ≤ W :=
      hW p q
    omega
  obtain ⟨CL, hCL⟩ := exists_bound_fin2 fun p q => ⌈‖(L p q : ℂ)‖⌉₊
  obtain ⟨c, hc⟩ : ∃ c, c = 4 * (W + c₀ + CL + ⌈‖φ D‖⌉₊ + 1) := ⟨_, rfl⟩
  refine ⟨c, fun S T a b m => ?_⟩
  obtain ⟨N, hN⟩ : ∃ N, N = T * (a + b) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 1 + m + S + T + a + b := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = 2 * Q * c₀ := ⟨_, rfl⟩
  rw [← hN, ← hQ]
  -- elementary inequalities
  have hQK : 2 * Q ≤ K := by
    rw [hK]
    calc 2 * Q = 2 * Q * 1 := (Nat.mul_one _).symm
      _ ≤ 2 * Q * c₀ := Nat.mul_le_mul_left _ (by omega)
  have hc₀K : c₀ ≤ K := by
    rw [hK]
    calc c₀ = 1 * c₀ := (Nat.one_mul _).symm
      _ ≤ 2 * Q * c₀ := Nat.mul_le_mul_right _ (by omega)
  have hja : ∀ j : Fin T, (j : ℕ) * a ≤ N := fun j => by
    rw [hN]; exact Nat.mul_le_mul j.2.le (Nat.le_add_right a b)
  have hjb : ∀ j : Fin T, (j : ℕ) * b ≤ N := fun j => by
    rw [hN]; exact Nat.mul_le_mul j.2.le (Nat.le_add_left b a)
  -- sizes of the `P_{ijk}`
  have hsz : ∀ (i : Fin S) (j k : Fin T), Sz (Ppol ℓ r L D E G H S a b m N i j k)
      (K ^ (4 * m + S) * W ^ (4 * (N + 1))) ((2 * m + S) * c₀ + 4 * W) := fun i j k =>
    sz_pres (sz_mono hD0 hc₀K le_rfl)
      (sz_mono (sz_lin (hE0 0) (hE0 1) (j : ℕ) (k : ℕ))
        (by rw [hK]; exact Nat.mul_le_mul_right c₀ (by omega)) le_rfl)
      (sz_mono (sz_lin (hG0 0) (hG0 1) a b)
        (by rw [hK]; exact Nat.mul_le_mul_right c₀ (by omega)) le_rfl)
      (sz_epart ℓ r L A hH0 hD0 hr2 hW' (hja j) (hjb j) (hja k) (hjb k)) i.2
      (by have := i.2; omega)
  have hdeg : (2 * m + S) * c₀ + 4 * W ≤ c * (1 + m + S) := by
    have e1 : (2 * m + S) * c₀ ≤ (2 * m + 2 * S) * c₀ := Nat.mul_le_mul_right c₀ (by omega)
    have e2 : (2 * m + 2 * S) * c₀ = 2 * c₀ * (m + S) := by ring
    have e3 : 2 * c₀ * (m + S) ≤ c * (m + S) := Nat.mul_le_mul_right (m + S) (by omega)
    have e4 : c * (1 + m + S) = c + c * (m + S) := by ring
    omega
  refine ⟨φ D ^ (m + S) * lam (φ D) ℓ L N, mul_ne_zero (pow_ne_zero _ hD) (lam_ne_zero hD ℓ hL N),
    ?_, fun i j k => Ppol ℓ r L D E G H S a b m N i j k, fun i j k => ?_,
    fun i j k r' => ((hsz i j k).2.1 r').trans hdeg, fun i j k => (hsz i j k).2.2.trans hdeg,
    fun f => ?_⟩
  · -- the size of `Λ`
    have h1 : (1 : ℝ) ≤ c := Nat.one_le_cast.2 (by omega)
    have hδc : ‖φ D‖ ≤ (c : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.2 (by omega))
    have hLc : ∀ p q, ‖(L p q : ℂ)‖ ≤ (c : ℝ) := fun p q =>
      (Nat.le_ceil _).trans (Nat.cast_le.2 ((hCL p q).trans (by omega)))
    refine (norm_mul_le_pow (norm_pow_le_pow hδc (m + S)) (norm_lam_le hδc ℓ hLc N)).trans
      (pow_le_pow_right₀ h1 ?_)
    have e1 : c * (1 + m + S + N) = c + c * (m + S + N) := by ring
    have e2 : 4 * (m + S + N) ≤ c * (m + S + N) := Nat.mul_le_mul_right _ (by omega)
    have := hℓW 0 0
    have := hℓW 0 1
    have := hℓW 1 0
    have := hℓW 1 1
    omega
  · -- the length of `P_{ijk}`
    have e1 : 4 * m + S ≤ c * (1 + m + S) := by
      have : 4 * (1 + m + S) ≤ c * (1 + m + S) := Nat.mul_le_mul_right _ (by omega)
      omega
    have e2 : 4 * m + S + 4 * (N + 1) ≤ c * (1 + m + S + N) := by
      have : 4 * (1 + m + S + N) ≤ c * (1 + m + S + N) := Nat.mul_le_mul_right _ (by omega)
      omega
    calc len (Ppol ℓ r L D E G H S a b m N i j k)
        ≤ K ^ (4 * m + S) * W ^ (4 * (N + 1)) := (hsz i j k).1
      _ = (2 * c₀) ^ (4 * m + S) * W ^ (4 * (N + 1)) * Q ^ (4 * m + S) := by rw [hK]; ring
      _ ≤ c ^ (4 * m + S) * c ^ (4 * (N + 1)) * Q ^ (c * (1 + m + S)) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _)
            (Nat.pow_le_pow_left (by omega) _)) (Nat.pow_le_pow_right (by omega) e1)
      _ ≤ c ^ (c * (1 + m + S + N)) * Q ^ (c * (1 + m + S)) := by
          rw [← pow_add]
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) e2)
  · -- the identity, by Leibniz's rule
    rw [iteratedDeriv_expPoly S T m x₁ x₂ f, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only [Ppol]
    rw [pres_eval φ (lin_eval φ (u := x₁) (v := x₂) (hE 0) (hE 1) (j : ℕ) (k : ℕ))
      (lin_eval φ (u := y₁) (v := y₂) (hG 0) (hG 1) a b)
      (epart_eval φ x₁ x₂ y₁ y₂ ℓ r L H D hH hr1 (hja j) (hjb j) (hja k) (hjb k)) i.2]
    exact mul_left_comm _ _ _

end S7W3_exists_iteratedDeriv_presentation

open S7W3_exists_iteratedDeriv_presentation

theorem solution
    (x₁ x₂ y₁ y₂ : ℂ)
    (hexp : ∀ i j : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j)))
    (ω ω₁ : ℂ) (D : Polynomial (Polynomial ℤ)) (E G : Fin 2 → Polynomial (Polynomial ℤ))
    (H : Fin 2 → Fin 2 → Polynomial (Polynomial ℤ))
    (hD : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ≠ 0)
    (hE : ∀ i, ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i))
    (hG : ∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j))
    (hH : ∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) *
        Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (H i j)) :
    ∃ c : ℕ, ∀ S T a b m : ℕ, ∃ Λ : ℂ, Λ ≠ 0 ∧ ‖Λ‖ ≤ (c : ℝ) ^ (c * (1 + m + S + T * (a + b))) ∧
      ∃ P : Fin S → Fin T → Fin T → Polynomial (Polynomial ℤ),
        (∀ i j k, ∑ r ∈ (P i j k).support, ∑ h ∈ ((P i j k).coeff r).support,
            (((P i j k).coeff r).coeff h).natAbs ≤
          c ^ (c * (1 + m + S + T * (a + b))) * (1 + m + S + T + a + b) ^ (c * (1 + m + S))) ∧
        (∀ i j k r, ((P i j k).coeff r).natDegree ≤ c * (1 + m + S)) ∧
        (∀ i j k, (P i j k).natDegree ≤ c * (1 + m + S)) ∧
        ∀ f : Fin S → Fin T → Fin T → ℂ,
          Λ * iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
              f i j k * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
            ((a : ℂ) * y₁ + (b : ℂ) * y₂) =
          ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
            f i j k * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (P i j k) := by
  exact main x₁ x₂ y₁ y₂ hexp
    (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁) D E G H hD hE hG hH

#print axioms solution
