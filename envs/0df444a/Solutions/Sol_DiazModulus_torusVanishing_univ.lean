-- Prove2me | solution 1 for DiazModulus.torusVanishing_univ
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:03:58.564511+00:00
-- url     : https://prove2.me/submissions/736835c7-2733-4d3e-a18c-c90357151a08

import Mathlib
import Definitions.Def_DiazMultiplicity
import Theorems.Thm_DiazModulus_isPrime_iInf_ker_eval_of_analytic
import Theorems.Thm_DiazModulus_le_height_torusVanishing

open Complex ComplexConjugate

/-! # The ideal of the whole torus: `I(G) = J₀`, prime, of height `≥ |A₁|`

`J₀ ≤ I(G)`: each `Y_iZ_i − 1` vanishes at `(x, y, y⁻¹)`. Conversely let `f` vanish on `G`, and let `N` bound every
`Z`-exponent of `f`. Shift each exponent `m = (a, b, c)` to `φ(m) = (a, N + b − c, 0)` and put
`q = Σ_m f_m X^{φ(m)}`. At any point `p` with `p(Y_i) ≠ 0`, `q(p) = Π_i p(Y_i)^N · f(x, y, y⁻¹)` with `y_i = p(Y_i)`,
so `q · Π_i Y_i` vanishes everywhere and `q = 0` (`MvPolynomial.funext`, `ℂ` infinite, `R` a domain). In
`R/J₀`, where `Y_iZ_i = 1`, the same exponent identity (`prod_pow_shift`, any commutative ring) gives
`f ≡ Π_i Z_i^N · q = 0`, so `f ∈ J₀`. Primality: `I(G)` is the ideal of the image of the analytic map
`(x, u) ↦ (x, exp u, exp(−u))` (surjective onto the torus points by `Complex.exp_log`), prime by the imported node
`isPrime_iInf_ker_eval_of_analytic`. The height bound is the imported node `le_height_torusVanishing`, after
reindexing `⨅_{x, y}` as `⨅_{g ∈ G}`. -/

namespace C13_V3
open DiazModulus MvPolynomial

/-- The exponent shift `φ_N(a, b, c) = (a, N + b − c, 0)`. -/
noncomputable def shift {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (N : ℕ)
    (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) : A₀ ⊕ (A₁ × Bool) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim (fun h => m (Sum.inl h)) fun p =>
    if p.2 = true then N + m (Sum.inr (p.1, true)) - m (Sum.inr (p.1, false)) else 0)

/-- The exponent identity behind both halves: if `P` and `P'` agree on `X, Y` and `P'(Y_i) P'(Z_i) = 1`, then
`P^{φ_N(m)} = (Π_i P'(Y_i)^N) · P'^m` whenever the `Z`-exponents of `m` are `≤ N`. -/
theorem prod_pow_shift {S : Type*} [CommRing S] {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (N : ℕ)
    (P P' : A₀ ⊕ (A₁ × Bool) → S) (hx : ∀ h, P (Sum.inl h) = P' (Sum.inl h))
    (hy : ∀ i, P (Sum.inr (i, true)) = P' (Sum.inr (i, true)))
    (hyz : ∀ i, P' (Sum.inr (i, true)) * P' (Sum.inr (i, false)) = 1)
    (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) (hm : ∀ i, m (Sum.inr (i, false)) ≤ N) :
    ∏ v, P v ^ shift N m v = (∏ i, P' (Sum.inr (i, true)) ^ N) * ∏ v, P' v ^ m v := by
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool, shift,
    Finsupp.coe_equivFunOnFinite_symm, Sum.elim_inl, Sum.elim_inr]
  simp only [if_true, Bool.false_eq_true, if_false, pow_zero, mul_one]
  have h1 : ∏ h, P (Sum.inl h) ^ m (Sum.inl h) = ∏ h, P' (Sum.inl h) ^ m (Sum.inl h) :=
    Finset.prod_congr rfl fun h _ => by rw [hx]
  have h2 : ∏ i, P (Sum.inr (i, true)) ^ (N + m (Sum.inr (i, true)) - m (Sum.inr (i, false))) =
      ∏ i, (P' (Sum.inr (i, true)) ^ N * (P' (Sum.inr (i, true)) ^ m (Sum.inr (i, true)) *
        P' (Sum.inr (i, false)) ^ m (Sum.inr (i, false)))) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hy]
    have hb := hm i
    calc P' (Sum.inr (i, true)) ^ (N + m (Sum.inr (i, true)) - m (Sum.inr (i, false)))
        = P' (Sum.inr (i, true)) ^ (N + m (Sum.inr (i, true)) - m (Sum.inr (i, false))) *
          (P' (Sum.inr (i, true)) * P' (Sum.inr (i, false))) ^ m (Sum.inr (i, false)) := by
          rw [hyz, one_pow, mul_one]
      _ = P' (Sum.inr (i, true)) ^ (N + m (Sum.inr (i, true)) - m (Sum.inr (i, false)) +
            m (Sum.inr (i, false))) * P' (Sum.inr (i, false)) ^ m (Sum.inr (i, false)) := by
          rw [mul_pow, pow_add, mul_assoc]
      _ = _ := by rw [Nat.sub_add_cancel (by omega), pow_add, mul_assoc]
  rw [h1, h2, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

/-- A polynomial vanishing at every torus point lies in `J₀`. -/
theorem mem_torusIdeal_of_eval {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁]
    (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) (hf : ∀ g : TorusGroup ℂ A₀ A₁, eval (torusPt g) f = 0) :
    f ∈ torusIdeal ℂ A₀ A₁ := by
  classical
  set N := f.support.sup fun m => ∑ i, m (Sum.inr (i, false)) with hNdef
  have hN : ∀ m ∈ f.support, ∀ i, m (Sum.inr (i, false)) ≤ N := fun m hm i =>
    (Finset.single_le_sum (f := fun j => m (Sum.inr (j, false))) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i)).trans (Finset.le_sup (f := fun m => ∑ i, m (Sum.inr (i, false))) hm)
  set q : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ := ∑ m ∈ f.support, monomial (shift N m) (coeff m f) with hqdef
  -- `q = 0`: `q · Π Y_i` vanishes at every point
  have hq : q = 0 := by
    have hY : (∏ i, X (Sum.inr (i, true)) : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i _ => X_ne_zero _
    have h0 : q * ∏ i, X (Sum.inr (i, true)) = 0 := by
      apply MvPolynomial.funext
      intro p
      rw [map_mul, map_prod, map_zero]
      by_cases hp : ∀ i, p (Sum.inr (i, true)) ≠ 0
      · let g : TorusGroup ℂ A₀ A₁ :=
          (Multiplicative.ofAdd fun h => p (Sum.inl h), fun i => Units.mk0 _ (hp i))
        have hyz : ∀ i, torusPt g (Sum.inr (i, true)) * torusPt g (Sum.inr (i, false)) = 1 := by
          intro i; simp [g, torusPt, torusPoint, hp i]
        have hev : eval p q = (∏ i, torusPt g (Sum.inr (i, true)) ^ N) * eval (torusPt g) f := by
          rw [hqdef, map_sum, MvPolynomial.eval_eq', Finset.mul_sum]
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
            prod_pow_shift N p (torusPt g) (fun _ => rfl) (fun _ => rfl) hyz m (hN m hm)]
          ring
        rw [hev, hf g, mul_zero, zero_mul]
      · simp only [not_forall, not_not] at hp
        obtain ⟨i, hi⟩ := hp
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [eval_X]; exact hi), mul_zero]
    exact (mul_eq_zero.1 h0).resolve_right hY
  -- `f ≡ Π Z_i^N · q` modulo `J₀`
  have hA : f - (∏ i, X (Sum.inr (i, false)) ^ N) * q ∈ torusIdeal ℂ A₀ A₁ := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    let φ := Ideal.Quotient.mkₐ ℂ (torusIdeal ℂ A₀ A₁)
    let P : A₀ ⊕ (A₁ × Bool) → _ := fun v => φ (X v)
    have hφ : ∀ r, Ideal.Quotient.mk (torusIdeal ℂ A₀ A₁) r = aeval P r := fun r =>
      DFunLike.congr_fun (MvPolynomial.aeval_unique φ) r
    have hyz : ∀ i, P (Sum.inr (i, true)) * P (Sum.inr (i, false)) = 1 := by
      intro i
      simp only [P, ← map_mul, ← map_one φ]
      exact Ideal.Quotient.eq.2 (Ideal.subset_span ⟨i, rfl⟩)
    have hone : (∏ i, P (Sum.inr (i, false)) ^ N) * (∏ i, P (Sum.inr (i, true)) ^ N) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun i _ => by rw [← mul_pow, mul_comm, hyz, one_pow]
    rw [hφ, hφ, map_mul, map_prod, hqdef, map_sum, Finset.mul_sum]
    conv_lhs => rw [← f.support_sum_monomial_coeff]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [aeval_monomial, aeval_X, map_pow, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rw [prod_pow_shift N P P (fun _ => rfl) (fun _ => rfl) hyz m (hN m hm)]
    linear_combination (-(algebraMap ℂ _ (coeff m f) * ∏ v, P v ^ m v)) * hone
  rw [hq, mul_zero, sub_zero] at hA
  exact hA

/-- The analytic parametrisation `(x, u) ↦ (x, exp u, exp(−u))` of the torus points. -/
noncomputable def expParam {A₀ A₁ : Type*} (p : (A₀ → ℂ) × (A₁ → ℂ)) : A₀ ⊕ (A₁ × Bool) → ℂ :=
  Sum.elim p.1 fun q : A₁ × Bool => if q.2 then Complex.exp (p.2 q.1) else Complex.exp (-p.2 q.1)

theorem expParam_analytic {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (v : A₀ ⊕ (A₁ × Bool)) :
    AnalyticOnNhd ℂ (fun p : (A₀ → ℂ) × (A₁ → ℂ) => expParam p v) Set.univ := by
  intro p _
  rcases v with h | ⟨i, b⟩
  · simp only [expParam, Sum.elim_inl]
    exact ((ContinuousLinearMap.proj h : (A₀ → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.fst ℂ (A₀ → ℂ) (A₁ → ℂ))).analyticAt p
  · have hu : AnalyticAt ℂ (fun p : (A₀ → ℂ) × (A₁ → ℂ) => p.2 i) p :=
      ((ContinuousLinearMap.proj i : (A₁ → ℂ) →L[ℂ] ℂ).comp
        (ContinuousLinearMap.snd ℂ (A₀ → ℂ) (A₁ → ℂ))).analyticAt p
    simp only [expParam, Sum.elim_inr]
    split_ifs
    · exact analyticAt_cexp.comp hu
    · exact analyticAt_cexp.comp hu.neg

theorem iInf_expParam {A₀ A₁ : Type*} :
    (⨅ p : (A₀ → ℂ) × (A₁ → ℂ), RingHom.ker (MvPolynomial.eval (expParam p) :
      MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ →+* ℂ)) = torusVanishing (Set.univ : Set (TorusGroup ℂ A₀ A₁)) := by
  ext f
  simp only [torusVanishing, Submodule.mem_iInf, RingHom.mem_ker, Set.mem_univ, forall_const]
  constructor
  · intro hf g
    have := hf (Multiplicative.toAdd g.1, fun i => Complex.log (g.2 i))
    convert this using 2
    congr 1
    funext v
    rcases v with h | ⟨i, b⟩
    · rfl
    · cases b <;> simp [expParam, torusPt, torusPoint, Complex.exp_neg, Complex.exp_log (g.2 i).ne_zero]
  · intro hf p
    have := hf (Multiplicative.ofAdd p.1, fun i => Units.mk0 (Complex.exp (p.2 i)) (Complex.exp_ne_zero _))
    convert this using 2
    congr 1
    funext v
    rcases v with h | ⟨i, b⟩
    · rfl
    · cases b <;> simp [expParam, torusPt, torusPoint, Complex.exp_neg]

theorem iInf_torusPoint {A₀ A₁ : Type*} :
    (⨅ (x : A₀ → ℂ) (y : A₁ → ℂˣ), RingHom.ker (MvPolynomial.eval (torusPoint x y) :
      MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ →+* ℂ)) = torusVanishing (Set.univ : Set (TorusGroup ℂ A₀ A₁)) := by
  ext f
  simp only [torusVanishing, Submodule.mem_iInf, RingHom.mem_ker, Set.mem_univ, forall_const]
  exact ⟨fun hf g => hf _ _, fun hf x y => hf (Multiplicative.ofAdd x, y)⟩

end C13_V3

open DiazModulus C13_V3 in
theorem solution {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] :
    torusVanishing (Set.univ : Set (TorusGroup ℂ A₀ A₁)) = torusIdeal ℂ A₀ A₁ ∧ (torusIdeal ℂ A₀ A₁).IsPrime ∧
      (Fintype.card A₁ : ℕ∞) ≤ (torusIdeal ℂ A₀ A₁).height := by
  have hI : torusVanishing (Set.univ : Set (TorusGroup ℂ A₀ A₁)) = torusIdeal ℂ A₀ A₁ := by
    apply le_antisymm
    · intro f hf
      simp only [torusVanishing, Submodule.mem_iInf, RingHom.mem_ker] at hf
      exact mem_torusIdeal_of_eval f fun g => hf g (Set.mem_univ _)
    · rw [torusIdeal, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, torusVanishing, Submodule.mem_iInf, RingHom.mem_ker]
      intro g _
      simp [torusPt, torusPoint]
  refine ⟨hI, ?_, ?_⟩
  · rw [← hI, ← iInf_expParam]
    exact DiazModulus.isPrime_iInf_ker_eval_of_analytic _ fun v => expParam_analytic v
  · rw [← hI, ← iInf_torusPoint]
    exact DiazModulus.le_height_torusVanishing
