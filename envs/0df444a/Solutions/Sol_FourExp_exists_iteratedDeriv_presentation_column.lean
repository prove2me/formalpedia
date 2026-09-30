-- Prove2me | solution 1 for FourExp.exists_iteratedDeriv_presentation_column
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T08:29:14.351521+00:00
-- url     : https://prove2.me/submissions/98e0e768-09fd-4e70-85d6-6f58ba124185

import Mathlib
import Theorems.Thm_FourExp_exists_iteratedDeriv_presentation_of_exp_factor
import Theorems.Thm_Transcendence_exists_int_pow_repr
import Theorems.Thm_Transcendence_length_mul_le
import Theorems.Thm_Transcendence_length_sum_le

/-!
# Integer presentations of the derivatives, in the column case

Write `φ(P) = P(ω, ω₁)` for `P ∈ ℤ[X][Y]`, `δ = φ(D)`, `β = j x₁ + k x₂`, `ζ = a y₁ + b y₂` and
`α_{pq} = e^(x_p y_q)`. The shared node `FourExp.exists_iteratedDeriv_presentation_of_exp_factor`
builds the presentation from integer polynomials `U_{jk}` with `φ(U_{jk}) = Λ₁ e^(βζ)`, so only the
exponential factor `e^(βζ) = α₀₀^(ja) α₀₁^(jb) α₁₀^(ka) α₁₁^(kb)` is presented here.

* **The column `y₂`.** `α_{p1}` is algebraic. As in `FourExp.exists_iteratedDeriv_presentation`,
  there are `ℓ`, `A` and an integer `L ≠ 0` with `Lⁿ αⁿ = ∑_{t<ℓ} r_t α^t` and `|r_t| ≤ Aⁿ`, and
  for `n ≤ N = T b` the number `δ^(ℓ-1) L^N αⁿ` is `φ` of an integer polynomial of length at most
  `W^(N+1)` and degrees at most `W`.
* **The column `y₁`.** `α_{p0}` need not be algebraic, but `δ α_{p0} = φ(H_{p0})`, so for
  `n ≤ T a` the number `δ^(T a) αⁿ` is `φ(H_{p0}ⁿ D^(T a - n))`, of length at most `c₀^(T a)` and
  degrees at most `T a c₀`, where `c₀` bounds the data.
* **Assembly.** The four factors present `Λ₁ e^(βζ)` with
  `Λ₁ = δ^(2 T a) δ^(ℓ₀-1) L₀^N δ^(ℓ₁-1) L₁^N ≠ 0`, with length `c₀^(2 T a) W^(2(N+1))` and
  degrees `2 T a c₀ + 2 W`. The shared node gives `δ^(m+S) Λ₁ F⁽ᵐ⁾(ζ) = ∑ f_{ijk} φ(P_{ijk})`, so
  `Λ = δ^(m+S) Λ₁`, and all the constants are absorbed into one `c`.
-/

namespace T2_exists_iteratedDeriv_presentation_column

open Polynomial

/-! ### Length and size of integer polynomials in two variables -/

/-- The length of `P ∈ ℤ[X][Y]`: the sum of the absolute values of all its integer coefficients. -/
noncomputable def len (P : ℤ[X][X]) : ℕ :=
  ∑ r ∈ P.support, ∑ h ∈ (P.coeff r).support, ((P.coeff r).coeff h).natAbs

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
  refine ⟨(Transcendence.length_mul_le P Q).trans (Nat.mul_le_mul hP.1 hQ.1), fun r => ?_,
    Polynomial.natDegree_mul_le.trans (Nat.add_le_add hP.2.2 hQ.2.2)⟩
  rw [Polynomial.coeff_mul]
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun x _ =>
    Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hP.2.1 x.1) (hQ.2.1 x.2))

lemma sz_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ[X][X]) {b d : ℕ}
    (h : ∀ i ∈ s, Sz (f i) b d) : Sz (∑ i ∈ s, f i) (s.card * b) d := by
  refine ⟨(Transcendence.length_sum_le s f).trans ?_, fun r => ?_,
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

lemma exists_bound_fin2 (w : Fin 2 → ℕ) : ∃ W, ∀ p, w p ≤ W :=
  ⟨∑ p, w p, fun p => Finset.single_le_sum (f := w) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)⟩

lemma phi_CC (φ : ℤ[X][X] →+* ℂ) (z : ℤ) : φ (C (C z)) = (z : ℂ) :=
  eq_intCast (φ.comp ((C : ℤ[X] →+* ℤ[X][X]).comp (C : ℤ →+* ℤ[X]))) z

/-! ### The column `y₂`: powers of an algebraic number -/

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

/-! ### The column `y₁`: powers of a presented number -/

/-- `φ(D)^N αⁿ` as an integer polynomial, for `n ≤ N`, from `φ(H) = α φ(D)` alone. -/
noncomputable def colfac (Hp Dp : ℤ[X][X]) (N n : ℕ) : ℤ[X][X] :=
  Hp ^ n * Dp ^ (N - n)

lemma colfac_eval (φ : ℤ[X][X] →+* ℂ) {Hp Dp : ℤ[X][X]} {α : ℂ} (hH : α * φ Dp = φ Hp)
    {N n : ℕ} (hn : n ≤ N) : φ (colfac Hp Dp N n) = φ Dp ^ N * α ^ n := by
  have hsplit : φ Dp ^ N = φ Dp ^ n * φ Dp ^ (N - n) := by
    rw [← pow_add, Nat.add_sub_of_le hn]
  rw [colfac, map_mul φ, map_pow φ, map_pow φ, ← hH, mul_pow, hsplit]
  ring

lemma sz_colfac {Hp Dp : ℤ[X][X]} {c : ℕ} (hH : Sz Hp c c) (hD : Sz Dp c c) {N n : ℕ}
    (hn : n ≤ N) : Sz (colfac Hp Dp N n) (c ^ N) (N * c) := by
  refine sz_mono (sz_mul (sz_pow hH n) (sz_pow hD (N - n))) ?_ ?_
  · rw [← pow_add, Nat.add_sub_of_le hn]
  · rw [← Nat.add_mul, Nat.add_sub_of_le hn]

/-! ### The exponential factor -/

/-- The product of the four factors, presenting `Λ₁ e^((j x₁ + k x₂)(a y₁ + b y₂))`. -/
noncomputable def epart (ℓ : Fin 2 → ℕ) (r : Fin 2 → ℕ → ℕ → ℤ) (L : Fin 2 → ℤ)
    (H : Fin 2 → Fin 2 → ℤ[X][X]) (Dp : ℤ[X][X]) (Na N a b j k : ℕ) : ℤ[X][X] :=
  colfac (H 0 0) Dp Na (j * a) * fac (ℓ 0) (r 0) (L 0) (H 0 1) Dp N (j * b) *
    colfac (H 1 0) Dp Na (k * a) * fac (ℓ 1) (r 1) (L 1) (H 1 1) Dp N (k * b)

/-- The constant `Λ₁ = δ^(T a) δ^(ℓ₀-1) L₀^N δ^(T a) δ^(ℓ₁-1) L₁^N`. -/
noncomputable def lam (δ : ℂ) (ℓ : Fin 2 → ℕ) (L : Fin 2 → ℤ) (Na N : ℕ) : ℂ :=
  δ ^ Na * (δ ^ (ℓ 0 - 1) * (L 0 : ℂ) ^ N) * δ ^ Na * (δ ^ (ℓ 1 - 1) * (L 1 : ℂ) ^ N)

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

lemma epart_eval (φ : ℤ[X][X] →+* ℂ) (x₁ x₂ y₁ y₂ : ℂ) (ℓ : Fin 2 → ℕ)
    (r : Fin 2 → ℕ → ℕ → ℤ) (L : Fin 2 → ℤ) (H : Fin 2 → Fin 2 → ℤ[X][X]) (Dp : ℤ[X][X])
    (hH : ∀ p q, Complex.exp (![x₁, x₂] p * ![y₁, y₂] q) * φ Dp = φ (H p q))
    (hr : ∀ p n, (L p : ℂ) ^ n * Complex.exp (![x₁, x₂] p * ![y₁, y₂] 1) ^ n =
      ∑ t ∈ Finset.range (ℓ p), (r p n t : ℂ) * Complex.exp (![x₁, x₂] p * ![y₁, y₂] 1) ^ t)
    {Na N a b j k : ℕ} (h1 : j * a ≤ Na) (h2 : j * b ≤ N) (h3 : k * a ≤ Na) (h4 : k * b ≤ N) :
    φ (epart ℓ r L H Dp Na N a b j k) = lam (φ Dp) ℓ L Na N *
      Complex.exp (((j : ℂ) * x₁ + (k : ℂ) * x₂) * ((a : ℂ) * y₁ + (b : ℂ) * y₂)) := by
  rw [epart, map_mul φ, map_mul φ, map_mul φ, colfac_eval φ (hH 0 0) h1,
    fac_eval φ _ _ _ _ _ (hH 0 1) (hr 0) h2, colfac_eval φ (hH 1 0) h3,
    fac_eval φ _ _ _ _ _ (hH 1 1) (hr 1) h4, exp_split x₁ x₂ y₁ y₂ a b j k, lam]
  ring

lemma sz_epart (ℓ : Fin 2 → ℕ) (r : Fin 2 → ℕ → ℕ → ℤ) (L : Fin 2 → ℤ) (A : Fin 2 → ℕ)
    {H : Fin 2 → Fin 2 → ℤ[X][X]} {Dp : ℤ[X][X]} {c W : ℕ}
    (hH : ∀ p q, Sz (H p q) c c) (hD : Sz Dp c c) (hr : ∀ p n t, (r p n t).natAbs ≤ A p ^ n)
    (hW : ∀ p, ℓ p * c ^ (ℓ p - 1) ≤ W ∧ (ℓ p - 1) * c ≤ W ∧ (L p).natAbs ≤ W ∧ A p ≤ W)
    {Na N a b j k : ℕ} (h1 : j * a ≤ Na) (h2 : j * b ≤ N) (h3 : k * a ≤ Na) (h4 : k * b ≤ N) :
    Sz (epart ℓ r L H Dp Na N a b j k) (c ^ (2 * Na) * W ^ (2 * (N + 1)))
      (2 * (Na * c) + 2 * W) := by
  have hf : ∀ p n, n ≤ N → Sz (fac (ℓ p) (r p) (L p) (H p 1) Dp N n) (W ^ (N + 1)) W :=
    fun p n hn => sz_fac (ℓ p) (r p) (L p) (hH p 1) hD (hr p) (hW p) hn
  exact sz_mono (sz_mul (sz_mul (sz_mul (sz_colfac (hH 0 0) hD h1) (hf 0 _ h2))
    (sz_colfac (hH 1 0) hD h3)) (hf 1 _ h4)) (le_of_eq (by ring)) (le_of_eq (by ring))

lemma lam_ne_zero {δ : ℂ} (hδ : δ ≠ 0) (ℓ : Fin 2 → ℕ) {L : Fin 2 → ℤ} (hL : ∀ p, L p ≠ 0)
    (Na N : ℕ) : lam δ ℓ L Na N ≠ 0 := by
  have hf : ∀ p, δ ^ (ℓ p - 1) * (L p : ℂ) ^ N ≠ 0 := fun p =>
    mul_ne_zero (pow_ne_zero _ hδ) (pow_ne_zero _ (Int.cast_ne_zero.2 (hL p)))
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hδ) (hf 0)) (pow_ne_zero _ hδ)) (hf 1)

lemma norm_mul_le_pow {x y : ℂ} {C : ℝ} {p q : ℕ} (hx : ‖x‖ ≤ C ^ p) (hy : ‖y‖ ≤ C ^ q) :
    ‖x * y‖ ≤ C ^ (p + q) := by
  rw [norm_mul, pow_add]
  exact mul_le_mul hx hy (norm_nonneg y) ((norm_nonneg x).trans hx)

lemma norm_pow_le_pow {x : ℂ} {C : ℝ} (hx : ‖x‖ ≤ C) (n : ℕ) : ‖x ^ n‖ ≤ C ^ n := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg x) hx n

lemma norm_lam_le {δ : ℂ} {C : ℝ} (hδ : ‖δ‖ ≤ C) (ℓ : Fin 2 → ℕ) {L : Fin 2 → ℤ}
    (hL : ∀ p, ‖(L p : ℂ)‖ ≤ C) (Na N : ℕ) :
    ‖lam δ ℓ L Na N‖ ≤ C ^ (Na + (ℓ 0 - 1 + N) + Na + (ℓ 1 - 1 + N)) := by
  have hf : ∀ p, ‖δ ^ (ℓ p - 1) * (L p : ℂ) ^ N‖ ≤ C ^ (ℓ p - 1 + N) := fun p =>
    norm_mul_le_pow (norm_pow_le_pow hδ _) (norm_pow_le_pow (hL p) N)
  exact norm_mul_le_pow (norm_mul_le_pow (norm_mul_le_pow (norm_pow_le_pow hδ Na) (hf 0))
    (norm_pow_le_pow hδ Na)) (hf 1)

end T2_exists_iteratedDeriv_presentation_column

open T2_exists_iteratedDeriv_presentation_column in
theorem solution
    (x₁ x₂ y₁ y₂ : ℂ)
    (hexp₂ : ∀ i : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * y₂)))
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
        (∀ i j k r, ((P i j k).coeff r).natDegree ≤ c * (1 + m + S + T * a)) ∧
        (∀ i j k, (P i j k).natDegree ≤ c * (1 + m + S + T * a)) ∧
        ∀ f : Fin S → Fin T → Fin T → ℂ,
          Λ * iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
              f i j k * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
            ((a : ℂ) * y₁ + (b : ℂ) * y₂) =
          ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
            f i j k * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (P i j k) := by
  -- the shared node, and `φ` as a ring homomorphism
  obtain ⟨c₁, hSH⟩ :=
    FourExp.exists_iteratedDeriv_presentation_of_exp_factor x₁ x₂ y₁ y₂ ω ω₁ D E G hE hG
  obtain ⟨φ, hφ⟩ : ∃ φ : Polynomial (Polynomial ℤ) →+* ℂ, ∀ P,
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ P = φ P :=
    ⟨Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁, fun _ => rfl⟩
  simp only [hφ] at hD hH hSH ⊢
  -- integer relations for the powers of the two algebraic exponentials of the column `y₂`
  choose ℓ A Lc hLc hr using fun p : Fin 2 => Transcendence.exists_int_pow_repr
    (α := Complex.exp (![x₁, x₂] p * ![y₁, y₂] 1)) (hexp₂ p)
  choose r hr1 hr2 using hr
  -- a common size `c₀` for `D` and `H`, and the constants of the two algebraic factors
  obtain ⟨cD, hcD⟩ := sz_exists D
  obtain ⟨cH, hcH⟩ := sz_exists_fam (fun pq : Fin 2 × Fin 2 => H pq.1 pq.2)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = cD + cH + 1 := ⟨_, rfl⟩
  have hD0 : Sz D c₀ c₀ := sz_mono hcD (by omega) (by omega)
  have hH0 : ∀ p q, Sz (H p q) c₀ c₀ := fun p q => sz_mono (hcH (p, q)) (by omega) (by omega)
  obtain ⟨W, hW⟩ := exists_bound_fin2 fun p =>
    ℓ p * c₀ ^ (ℓ p - 1) + (ℓ p - 1) * c₀ + (Lc p).natAbs + A p + ℓ p
  have hW' : ∀ p, ℓ p * c₀ ^ (ℓ p - 1) ≤ W ∧ (ℓ p - 1) * c₀ ≤ W ∧ (Lc p).natAbs ≤ W ∧
      A p ≤ W ∧ ℓ p ≤ W := fun p => by
    have h : ℓ p * c₀ ^ (ℓ p - 1) + (ℓ p - 1) * c₀ + (Lc p).natAbs + A p + ℓ p ≤ W := hW p
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨CL, hCL⟩ := exists_bound_fin2 fun p => ⌈‖(Lc p : ℂ)‖⌉₊
  obtain ⟨c, hc⟩ : ∃ c, c = c₁ + 4 * (W + c₀ + CL + ⌈‖φ D‖⌉₊ + 1) := ⟨_, rfl⟩
  refine ⟨c, fun S T a b m => ?_⟩
  obtain ⟨Na, hNa⟩ : ∃ Na, Na = T * a := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = T * b := ⟨_, rfl⟩
  have hX : T * (a + b) = Na + N := by rw [hNa, hN, Nat.mul_add]
  rw [hX, ← hNa]
  have hja : ∀ j : Fin T, (j : ℕ) * a ≤ Na := fun j => hNa ▸ Nat.mul_le_mul_right a j.2.le
  have hjb : ∀ j : Fin T, (j : ℕ) * b ≤ N := fun j => hN ▸ Nat.mul_le_mul_right b j.2.le
  -- the exponential factor, presented
  have hszU : ∀ j k : Fin T, Sz (epart ℓ r Lc H D Na N a b j k)
      (c₀ ^ (2 * Na) * W ^ (2 * (N + 1))) (2 * (Na * c₀) + 2 * W) := fun j k =>
    sz_epart ℓ r Lc A hH0 hD0 hr2
      (fun p => ⟨(hW' p).1, (hW' p).2.1, (hW' p).2.2.1, (hW' p).2.2.2.1⟩)
      (hja j) (hjb j) (hja k) (hjb k)
  obtain ⟨P, hPl, hPx, hPy, hPid⟩ := hSH S T a b m (lam (φ D) ℓ Lc Na N) _ _
    (fun j k => epart ℓ r Lc H D Na N a b j k) (fun j k => (hszU j k).1)
    (fun j k => (hszU j k).2.1) (fun j k => (hszU j k).2.2)
    (fun j k => epart_eval φ x₁ x₂ y₁ y₂ ℓ r Lc H D hH hr1 (hja j) (hjb j) (hja k) (hjb k))
  have hdeg : c₁ * (1 + m + S) + (2 * (Na * c₀) + 2 * W) ≤ c * (1 + m + S + Na) := by
    have e1 : c * (1 + m + S + Na) = c * (1 + m + S) + c * Na := by ring
    have e2 : (c₁ + 2 * W) * (1 + m + S) ≤ c * (1 + m + S) := Nat.mul_le_mul_right _ (by omega)
    have e3 : (c₁ + 2 * W) * (1 + m + S) = c₁ * (1 + m + S) + 2 * W * (1 + m + S) := by ring
    have e4 : 2 * W ≤ 2 * W * (1 + m + S) := Nat.le_mul_of_pos_right _ (by omega)
    have e5 : 2 * c₀ * Na ≤ c * Na := Nat.mul_le_mul_right _ (by omega)
    have e6 : 2 * (Na * c₀) = 2 * c₀ * Na := by ring
    omega
  refine ⟨φ D ^ (m + S) * lam (φ D) ℓ Lc Na N,
    mul_ne_zero (pow_ne_zero _ hD) (lam_ne_zero hD ℓ hLc Na N), ?_, P, fun i j k => ?_,
    fun i j k r' => (hPx i j k r').trans hdeg, fun i j k => (hPy i j k).trans hdeg, hPid⟩
  · -- the size of `Λ`
    have h1 : (1 : ℝ) ≤ c := Nat.one_le_cast.2 (by omega)
    have hδc : ‖φ D‖ ≤ (c : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.2 (by omega))
    have hLc' : ∀ p, ‖(Lc p : ℂ)‖ ≤ (c : ℝ) := fun p =>
      (Nat.le_ceil _).trans (Nat.cast_le.2 ((hCL p).trans (by omega)))
    refine (norm_mul_le_pow (norm_pow_le_pow hδc (m + S)) (norm_lam_le hδc ℓ hLc' Na N)).trans
      (pow_le_pow_right₀ h1 ?_)
    have e1 : c * (1 + m + S + (Na + N)) = c + c * (m + S + Na + N) := by ring
    have e2 : 4 * (m + S + Na + N) ≤ c * (m + S + Na + N) := Nat.mul_le_mul_right _ (by omega)
    have := (hW' 0).2.2.2.2
    have := (hW' 1).2.2.2.2
    omega
  · -- the length of `P_{ijk}`
    have hc1 : 1 ≤ c := by omega
    have hY : 1 ≤ 1 + m + S + T + a + b := by omega
    have hexp : c₁ * (1 + m + S) + (2 * Na + 2 * (N + 1)) ≤ c * (1 + m + S + (Na + N)) := by
      have f1 : c * (1 + m + S + (Na + N)) = c * (1 + m + S) + c * (Na + N) := by ring
      have f2 : (c₁ + 2) * (1 + m + S) ≤ c * (1 + m + S) := Nat.mul_le_mul_right _ (by omega)
      have f3 : (c₁ + 2) * (1 + m + S) = c₁ * (1 + m + S) + 2 * (1 + m + S) := by ring
      have f4 : 2 * (Na + N) ≤ c * (Na + N) := Nat.mul_le_mul_right _ (by omega)
      omega
    calc len (P i j k)
        ≤ c₁ ^ (c₁ * (1 + m + S)) * (1 + m + S + T + a + b) ^ (c₁ * (1 + m + S)) *
            (c₀ ^ (2 * Na) * W ^ (2 * (N + 1))) := hPl i j k
      _ ≤ c ^ (c₁ * (1 + m + S)) * (1 + m + S + T + a + b) ^ (c * (1 + m + S)) *
            (c ^ (2 * Na) * c ^ (2 * (N + 1))) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _)
            (Nat.pow_le_pow_right hY (Nat.mul_le_mul_right _ (by omega))))
            (Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_left (by omega) _))
      _ = c ^ (c₁ * (1 + m + S) + (2 * Na + 2 * (N + 1))) *
            (1 + m + S + T + a + b) ^ (c * (1 + m + S)) := by rw [pow_add, pow_add]; ring
      _ ≤ c ^ (c * (1 + m + S + (Na + N))) * (1 + m + S + T + a + b) ^ (c * (1 + m + S)) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hc1 hexp)
