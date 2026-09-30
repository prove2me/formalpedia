-- Prove2me | solution 1 for FourExp.exists_iteratedDeriv_presentation_of_exp_factor
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T08:36:18.808215+00:00
-- url     : https://prove2.me/submissions/64e66694-7395-43a4-b9b1-3e07022c5257

import Mathlib
import Theorems.Thm_Transcendence_length_mul_le
import Theorems.Thm_Transcendence_length_sum_le

/-!
# Integer presentations of the derivatives, from a presented exponential factor

Write `φ(P) = P(ω, ω₁)` for `P ∈ ℤ[X][Y]`, `δ = φ(D)`, `β = j x₁ + k x₂` and `ζ = a y₁ + b y₂`.
The exponential factor is given: integer polynomials `U_{jk}` with `φ(U_{jk}) = Λ₁ e^(βζ)`, of
length at most `L` and degrees at most `d`.

* **Leibniz.** `(z^i e^(βz))⁽ᵐ⁾(ζ) = ∑_{l ≤ m} C(m,l) i(i-1)⋯(i-l+1) ζ^(i-l) β^(m-l) e^(βζ)`,
  and the `m`-th derivative is linear in the coefficients `f_{ijk}`.
* **Polynomial factors.** Since `δβ = φ(j E₀ + k E₁)` and `δζ = φ(a G₀ + b G₁)`, for `l ≤ i < S`
  the number `δ^(m+S) ζ^(i-l) β^(m-l) Λ₁ e^(βζ)` is `φ` of
  `D^l (j E₀ + k E₁)^(m-l) (a G₀ + b G₁)^(i-l) D^(S-i+l) U_{jk}`. For `l > i` the Leibniz term
  vanishes.
* **Sizes.** Lengths are controlled by `len(PQ) ≤ len(P) len(Q)` and `len(∑ Pᵢ) ≤ ∑ len(Pᵢ)`; the
  degrees in `X` and `Y` add up under products. If `c₀` bounds the lengths and degrees of `D`, `E`
  and `G`, the lengths of the `P_{ijk}` are at most `K^(4m+S) L` with `K = 2(1+m+S+T+a+b)c₀`,
  and their degrees at most `(2m+S)c₀ + d`. For `c = 2c₀ + 4`,
  `K^(4m+S) ≤ c^(c(1+m+S)) (1+m+S+T+a+b)^(c(1+m+S))`.

The helpers are those of the accepted proof of `FourExp.exists_iteratedDeriv_presentation`, which
is this statement with the exponential factor presented from four algebraic exponentials.
-/

namespace T2_exists_iteratedDeriv_presentation_of_exp_factor

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

/-! ### The presentation, from a presented exponential factor -/

/-- The polynomial `P_{ijk}`, from the polynomial `ep = U_{jk}` presenting the exponential
factor. -/
noncomputable def Ppol (D : ℤ[X][X]) (E G : Fin 2 → ℤ[X][X]) (ep : ℤ[X][X]) (S a b m i j k : ℕ) :
    ℤ[X][X] :=
  pres D (C (C (j : ℤ)) * E 0 + C (C (k : ℤ)) * E 1) (C (C (a : ℤ)) * G 0 + C (C (b : ℤ)) * G 1)
    ep S m i

/-- The statement, for an arbitrary ring homomorphism `φ : ℤ[X][Y] → ℂ`. -/
theorem main (x₁ x₂ y₁ y₂ : ℂ) (φ : ℤ[X][X] →+* ℂ) (D : ℤ[X][X]) (E G : Fin 2 → ℤ[X][X])
    (hE : ∀ i, ![x₁, x₂] i * φ D = φ (E i)) (hG : ∀ j, ![y₁, y₂] j * φ D = φ (G j)) :
    ∃ c : ℕ, ∀ (S T a b m : ℕ) (Λ₁ : ℂ) (L d : ℕ) (U : Fin T → Fin T → ℤ[X][X]),
      (∀ j k, len (U j k) ≤ L) → (∀ j k r, ((U j k).coeff r).natDegree ≤ d) →
      (∀ j k, (U j k).natDegree ≤ d) →
      (∀ j k : Fin T, φ (U j k) = Λ₁ * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) *
        ((a : ℂ) * y₁ + (b : ℂ) * y₂))) →
      ∃ P : Fin S → Fin T → Fin T → ℤ[X][X],
        (∀ i j k, len (P i j k) ≤
          c ^ (c * (1 + m + S)) * (1 + m + S + T + a + b) ^ (c * (1 + m + S)) * L) ∧
        (∀ i j k r, ((P i j k).coeff r).natDegree ≤ c * (1 + m + S) + d) ∧
        (∀ i j k, (P i j k).natDegree ≤ c * (1 + m + S) + d) ∧
        ∀ f : Fin S → Fin T → Fin T → ℂ,
          φ D ^ (m + S) * Λ₁ * iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T,
              ∑ k : Fin T, f i j k * z ^ (i : ℕ) *
                Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
            ((a : ℂ) * y₁ + (b : ℂ) * y₂) =
          ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T, f i j k * φ (P i j k) := by
  -- a common size `c₀` for the data
  obtain ⟨cD, hcD⟩ := sz_exists D
  obtain ⟨cE, hcE⟩ := sz_exists_fam E
  obtain ⟨cG, hcG⟩ := sz_exists_fam G
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = cD + cE + cG + 1 := ⟨_, rfl⟩
  have hD0 : Sz D c₀ c₀ := sz_mono hcD (by omega) (by omega)
  have hE0 : ∀ p, Sz (E p) c₀ c₀ := fun p => sz_mono (hcE p) (by omega) (by omega)
  have hG0 : ∀ q, Sz (G q) c₀ c₀ := fun q => sz_mono (hcG q) (by omega) (by omega)
  obtain ⟨c, hc⟩ : ∃ c, c = 2 * c₀ + 4 := ⟨_, rfl⟩
  refine ⟨c, fun S T a b m Λ₁ L d U hUl hUx hUy hU => ?_⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 1 + m + S + T + a + b := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = 2 * Q * c₀ := ⟨_, rfl⟩
  rw [← hQ]
  -- elementary inequalities
  have hQK : 2 * Q ≤ K := by
    rw [hK]
    calc 2 * Q = 2 * Q * 1 := (Nat.mul_one _).symm
      _ ≤ 2 * Q * c₀ := Nat.mul_le_mul_left _ (by omega)
  have hc₀K : c₀ ≤ K := by
    rw [hK]
    calc c₀ = 1 * c₀ := (Nat.one_mul _).symm
      _ ≤ 2 * Q * c₀ := Nat.mul_le_mul_right _ (by omega)
  have hmS : 4 * m + S ≤ c * (1 + m + S) := by
    have : 4 * (1 + m + S) ≤ c * (1 + m + S) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hdeg : (2 * m + S) * c₀ + d ≤ c * (1 + m + S) + d := by
    have e1 : (2 * m + S) * c₀ ≤ (2 * m + 2 * S) * c₀ := Nat.mul_le_mul_right c₀ (by omega)
    have e2 : (2 * m + 2 * S) * c₀ = 2 * c₀ * (m + S) := by ring
    have e3 : 2 * c₀ * (m + S) ≤ c * (m + S) := Nat.mul_le_mul_right (m + S) (by omega)
    have e4 : c * (1 + m + S) = c + c * (m + S) := by ring
    omega
  -- sizes of the `P_{ijk}`
  have hsz : ∀ (i : Fin S) (j k : Fin T), Sz (Ppol D E G (U j k) S a b m i j k)
      (K ^ (4 * m + S) * L) ((2 * m + S) * c₀ + d) := fun i j k =>
    sz_pres (sz_mono hD0 hc₀K le_rfl)
      (sz_mono (sz_lin (hE0 0) (hE0 1) (j : ℕ) (k : ℕ))
        (by rw [hK]; exact Nat.mul_le_mul_right c₀ (by omega)) le_rfl)
      (sz_mono (sz_lin (hG0 0) (hG0 1) a b)
        (by rw [hK]; exact Nat.mul_le_mul_right c₀ (by omega)) le_rfl)
      ⟨hUl j k, hUx j k, hUy j k⟩ i.2 (by have := i.2; omega)
  refine ⟨fun i j k => Ppol D E G (U j k) S a b m i j k, fun i j k => ?_,
    fun i j k r => ((hsz i j k).2.1 r).trans hdeg, fun i j k => (hsz i j k).2.2.trans hdeg,
    fun f => ?_⟩
  · -- the length of `P_{ijk}`
    calc len (Ppol D E G (U j k) S a b m i j k)
        ≤ K ^ (4 * m + S) * L := (hsz i j k).1
      _ = (2 * c₀) ^ (4 * m + S) * Q ^ (4 * m + S) * L := by rw [hK]; ring
      _ ≤ c ^ (c * (1 + m + S)) * Q ^ (c * (1 + m + S)) * L :=
          Nat.mul_le_mul_right L (Nat.mul_le_mul
            ((Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hmS))
            (Nat.pow_le_pow_right (by omega) hmS))
  · -- the identity, by Leibniz's rule
    rw [iteratedDeriv_expPoly S T m x₁ x₂ f, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only [Ppol]
    rw [pres_eval φ (lin_eval φ (u := x₁) (v := x₂) (hE 0) (hE 1) (j : ℕ) (k : ℕ))
      (lin_eval φ (u := y₁) (v := y₂) (hG 0) (hG 1) a b) (hU j k) i.2]
    exact mul_left_comm _ _ _

end T2_exists_iteratedDeriv_presentation_of_exp_factor

open T2_exists_iteratedDeriv_presentation_of_exp_factor in
theorem solution
    (x₁ x₂ y₁ y₂ : ℂ) (ω ω₁ : ℂ) (D : Polynomial (Polynomial ℤ))
    (E G : Fin 2 → Polynomial (Polynomial ℤ))
    (hE : ∀ i, ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i))
    (hG : ∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j)) :
    ∃ c : ℕ, ∀ (S T a b m : ℕ) (Λ₁ : ℂ) (L d : ℕ)
      (U : Fin T → Fin T → Polynomial (Polynomial ℤ)),
      (∀ j k, ∑ r ∈ (U j k).support, ∑ h ∈ ((U j k).coeff r).support,
          (((U j k).coeff r).coeff h).natAbs ≤ L) →
      (∀ j k r, ((U j k).coeff r).natDegree ≤ d) →
      (∀ j k, (U j k).natDegree ≤ d) →
      (∀ j k : Fin T, Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (U j k) =
        Λ₁ * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) *
          ((a : ℂ) * y₁ + (b : ℂ) * y₂))) →
      ∃ P : Fin S → Fin T → Fin T → Polynomial (Polynomial ℤ),
        (∀ i j k, ∑ r ∈ (P i j k).support, ∑ h ∈ ((P i j k).coeff r).support,
            (((P i j k).coeff r).coeff h).natAbs ≤
          c ^ (c * (1 + m + S)) * (1 + m + S + T + a + b) ^ (c * (1 + m + S)) * L) ∧
        (∀ i j k r, ((P i j k).coeff r).natDegree ≤ c * (1 + m + S) + d) ∧
        (∀ i j k, (P i j k).natDegree ≤ c * (1 + m + S) + d) ∧
        ∀ f : Fin S → Fin T → Fin T → ℂ,
          Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ^ (m + S) * Λ₁ *
              iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
                f i j k * z ^ (i : ℕ) *
                  Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
              ((a : ℂ) * y₁ + (b : ℂ) * y₂) =
            ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
              f i j k *
                Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (P i j k) := by
  exact main x₁ x₂ y₁ y₂
    (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁) D E G hE hG
