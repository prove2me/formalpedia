-- Prove2me | solution 1 for DiazModulus.boxHilb_chain_bound
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:15:14.947998+00:00
-- url     : https://prove2.me/submissions/1e7cea53-4085-4f9a-aa5b-7c81f5fafc12

import Mathlib
import Definitions.Def_DiazHilbertBox
import Theorems.Thm_DiazModulus_boxHilb_mono
import Theorems.Thm_DiazModulus_boxHilb_sup_span_add_le
import Theorems.Thm_DiazModulus_nat_telescope_iter

open Complex ComplexConjugate

/-! # The regular chain bound: `2^{r(r−1)/2} u^r h_{I+(P)}(uD) ≤ h_I(2^r uD)`

Put `I_k = I + (P_j)_{j<k}` for `k ≤ r`, so `I_0 = I`, `I_r = I + (P_0, …, P_{r−1})` and
`I_{k+1} = I_k + (P_k)`, and let `f_k(v) = h_{I_k}(v D)`. Each `f_{k+1}` is monotone in `v`
(`boxHilb_mono`, since `v ≤ w` gives `v D ≤ w D`). For `k < r` the element `P_k ∈ F(D)` is
regular on `S ⧸ I_k`, so Lemma 8.5 (`boxHilb_sup_span_add_le` with `T = v D`, using
`(v + 1) D = v D + D`) gives `f_{k+1}(v+1) + f_k(v) ≤ f_k(v+1)`. The iterated telescope
`nat_telescope_iter` with `j = r` then gives `2^{r(r−1)/2} u^r f_r(u) ≤ f_0(2^r u)`, which is the
claim after rewriting `I_0` and `I_r`. -/

namespace C11_chainBound

open DiazModulus

/-- The partial chain ideal `I_k = I + (P_j)_{j<k}`. -/
def chainIdeal {S : Type*} [CommRing S] (I : Ideal S) {r : ℕ} (P : Fin r → S) (k : ℕ) :
    Ideal S :=
  I ⊔ Ideal.span (P '' {j | j.val < k})

theorem chainIdeal_zero {S : Type*} [CommRing S] (I : Ideal S) {r : ℕ} (P : Fin r → S) :
    chainIdeal I P 0 = I := by
  simp [chainIdeal]

theorem chainIdeal_top {S : Type*} [CommRing S] (I : Ideal S) {r : ℕ} (P : Fin r → S) :
    chainIdeal I P r = I ⊔ Ideal.span (Set.range P) := by
  have : {j : Fin r | j.val < r} = Set.univ := Set.eq_univ_of_forall fun j => j.isLt
  rw [chainIdeal, this, Set.image_univ]

theorem chainIdeal_succ {S : Type*} [CommRing S] (I : Ideal S) {r : ℕ} (P : Fin r → S)
    (k : ℕ) (hk : k < r) :
    chainIdeal I P (k + 1) = chainIdeal I P k ⊔ Ideal.span {P ⟨k, hk⟩} := by
  have : {j : Fin r | j.val < k + 1} = {j | j.val < k} ∪ {⟨k, hk⟩} := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
    omega
  rw [chainIdeal, chainIdeal, this, Set.image_union, Set.image_singleton, Ideal.span_union,
    sup_assoc]

theorem nsmul_le_nsmul {B : Type*} (D : B → ℕ) {v w : ℕ} (h : v ≤ w) : v • D ≤ w • D :=
  fun b => by simpa using Nat.mul_le_mul_right (D b) h

end C11_chainBound

open DiazModulus C11_chainBound in
theorem solution {K S B : Type*} [Field K] [CommRing S] [Algebra K S] (F : (B → ℕ) → Submodule K S)
    (hFmono : Monotone F)
    (hFmul : ∀ {Tₑ Uₑ : B → ℕ} {aₑ bₑ : S}, aₑ ∈ F Tₑ → bₑ ∈ F Uₑ → aₑ * bₑ ∈ F (Tₑ + Uₑ))
    (hFfin : ∀ Tₑ, FiniteDimensional K ↥(F Tₑ)) (I : Ideal S) (D : B → ℕ) (r : ℕ)
    (P : Fin r → S) (hP : ∀ k, P k ∈ F D)
    (hreg : ∀ k : Fin r, IsSMulRegular (S ⧸ (I ⊔ Ideal.span (P '' {j | j < k}))) (P k)) (u : ℕ) :
    2 ^ (r * (r - 1) / 2) * u ^ r * boxHilb F (I ⊔ Ideal.span (Set.range P)) (u • D)
      ≤ boxHilb F I ((2 ^ r * u) • D) := by
  let f : ℕ → ℕ → ℕ := fun k v => boxHilb F (chainIdeal I P k) (v • D)
  have hmono : ∀ k < r, Monotone (f (k + 1)) := fun k _ v w hvw =>
    DiazModulus.boxHilb_mono F hFmono hFfin _ (nsmul_le_nsmul D hvw)
  have hstep : ∀ k < r, ∀ v, f (k + 1) (v + 1) + f k v ≤ f k (v + 1) := by
    intro k hk v
    have h1 := DiazModulus.boxHilb_sup_span_add_le F hFmul hFfin (chainIdeal I P k)
      (P ⟨k, hk⟩) D (v • D) (hP _) (hreg ⟨k, hk⟩)
    simp only [f]
    rw [chainIdeal_succ I P k hk, succ_nsmul]
    exact h1
  have := DiazModulus.nat_telescope_iter f r hmono hstep u
  simp only [f, chainIdeal_zero, chainIdeal_top] at this
  exact this
