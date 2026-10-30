-- Prove2me | solution 1 for DiazModulus.exists_translation_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:06:54.274992+00:00
-- url     : https://prove2.me/submissions/2ebf8471-1048-4a8b-9767-ce77fa3ce2f8

import Mathlib
import Definitions.Def_DiazHilbertBox

open Complex ComplexConjugate

/-! # Translations of the torus model

For `a : A₀ → K` and `b : A₁ × Bool → Kˣ` let `tr a b` be the `K`-algebra endomorphism of
`R = K[X, Y, Z]` with `X_h ↦ X_h + a_h` and `W_p ↦ b_p W_p` on the variables `Y_i`, `Z_i`
(`MvPolynomial.aeval`). Then `tr a b ∘ tr (−a) b⁻¹ = id` on the variables, so
`AlgEquiv.ofAlgHom` gives the automorphism `e`, with `b_{(i,true)} = y_i`, `b_{(i,false)} = y_i⁻¹`.
Each `tr a b (W_v)` is supported on monomials `≤ single v 1`; supports add under products
(`restrictSupport_add`), so `tr a b` sends a monomial `X^m` into the span of the monomials
`≤ m` (induction on `m`). Every block box is a lower set of exponents, so it is mapped into
itself by `tr a b` and by the inverse translation, hence onto itself. Finally
`e (Y_i Z_i − 1) = y_i y_i⁻¹ Y_i Z_i − 1 = Y_i Z_i − 1`, so `Ideal.map_span` gives `e(J₀) = J₀`. -/

namespace C11_T6
open DiazModulus MvPolynomial

variable {K : Type*} [Field K]

theorem mul_mem_Iic {σ : Type*} {f g : MvPolynomial σ K} {m m' : σ →₀ ℕ}
    (hf : f ∈ restrictSupport K (Set.Iic m)) (hg : g ∈ restrictSupport K (Set.Iic m')) :
    f * g ∈ restrictSupport K (Set.Iic (m + m')) := by
  have := Submodule.mul_mem_mul hf hg
  rw [← restrictSupport_add] at this
  refine restrictSupport_mono K ?_ this
  rintro _ ⟨u, hu, w, hw, rfl⟩
  exact add_le_add (Set.mem_Iic.mp hu) (Set.mem_Iic.mp hw)

theorem pow_mem_Iic {σ : Type*} {f : MvPolynomial σ K} {m : σ →₀ ℕ}
    (hf : f ∈ restrictSupport K (Set.Iic m)) (k : ℕ) :
    f ^ k ∈ restrictSupport K (Set.Iic (k • m)) := by
  induction k with
  | zero =>
    rw [pow_zero, zero_smul, ← C_1, ← monomial_zero']
    exact (monomial_mem_restrictSupport K).2 (Or.inl (Set.mem_Iic.2 le_rfl))
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_Iic ih hf

theorem map_monomial_mem_Iic {σ : Type*} (φ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K)
    (hφ : ∀ v, φ (X v) ∈ restrictSupport K (Set.Iic (Finsupp.single v 1))) (m : σ →₀ ℕ) :
    φ (monomial m 1) ∈ restrictSupport K (Set.Iic m) := by
  induction m using Finsupp.induction with
  | zero =>
    rw [monomial_zero', C_1, map_one, ← C_1, ← monomial_zero']
    exact (monomial_mem_restrictSupport K).2 (Or.inl (Set.mem_Iic.2 le_rfl))
  | single_add v k m _ _ ih =>
    rw [← mul_one (1 : K), ← monomial_mul, map_mul, ← X_pow_eq_monomial, map_pow]
    have h := pow_mem_Iic (hφ v) k
    rw [Finsupp.smul_single, smul_eq_mul, mul_one] at h
    exact mul_mem_Iic h ih

theorem map_blockBox_le {σ ι : Type*} (φ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K)
    (hφ : ∀ v, φ (X v) ∈ restrictSupport K (Set.Iic (Finsupp.single v 1))) (β : σ → ι)
    (T : ι → ℕ) : (blockBox K β T).map φ.toLinearMap ≤ blockBox K β T := by
  rw [blockBox, restrictSupport_eq_span, Submodule.map_span_le]
  rintro _ ⟨m, hm, rfl⟩
  rw [← restrictSupport_eq_span]
  refine restrictSupport_mono K ?_ (map_monomial_mem_Iic φ hφ m)
  intro m' (hm' : m' ≤ m) b
  refine le_trans ?_ (hm b)
  rw [← add_tsub_cancel_of_le hm', Finsupp.mapDomain_add, Finsupp.add_apply]
  exact Nat.le_add_right _ _

variable {A₀ A₁ : Type*}

/-- The translation `X_h ↦ X_h + a_h`, `W_p ↦ b_p W_p`. -/
noncomputable def tr (a : A₀ → K) (b : A₁ × Bool → Kˣ) :
    MvPolynomial (A₀ ⊕ (A₁ × Bool)) K →ₐ[K] MvPolynomial (A₀ ⊕ (A₁ × Bool)) K :=
  aeval (Sum.elim (fun h => X (Sum.inl h) + C (a h)) fun p => C (b p : K) * X (Sum.inr p))

theorem tr_X (a : A₀ → K) (b : A₁ × Bool → Kˣ) (v : A₀ ⊕ (A₁ × Bool)) :
    tr a b (X v) = Sum.elim (fun h => X (Sum.inl h) + C (a h)) (fun p => C (b p : K) * X (Sum.inr p)) v := by
  simp [tr]

theorem tr_X_mem (a : A₀ → K) (b : A₁ × Bool → Kˣ) (v : A₀ ⊕ (A₁ × Bool)) :
    tr a b (X v) ∈ restrictSupport K (Set.Iic (Finsupp.single v 1)) := by
  rw [tr_X]
  cases v with
  | inl h =>
    refine add_mem ?_ ?_
    · rw [X, monomial_mem_restrictSupport]; exact Or.inl (Set.mem_Iic.2 le_rfl)
    · rw [← monomial_zero', monomial_mem_restrictSupport]; exact Or.inl (Set.mem_Iic.2 zero_le)
  | inr p =>
    rw [Sum.elim_inr, C_mul_X_eq_monomial, monomial_mem_restrictSupport]
    exact Or.inl (Set.mem_Iic.2 le_rfl)

theorem tr_comp (a : A₀ → K) (b : A₁ × Bool → Kˣ) :
    (tr a b).comp (tr (-a) b⁻¹) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro v
  cases v with
  | inl h => simp [tr]
  | inr p =>
    simp only [AlgHom.comp_apply, tr_X, Sum.elim_inr, map_mul, algHom_C, AlgHom.id_apply]
    rw [algebraMap_eq, ← mul_assoc, ← map_mul, Pi.inv_apply, Units.val_inv_eq_inv_val,
      inv_mul_cancel₀ (b p).ne_zero, map_one, one_mul]

end C11_T6

open DiazModulus C11_T6 in
theorem solution {K A₀ A₁ : Type*} [Field K] (x : A₀ → K) (y : A₁ → Kˣ) :
    ∃ e : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K ≃ₐ[K] MvPolynomial (A₀ ⊕ (A₁ × Bool)) K,
      (∀ v, e (MvPolynomial.X v) = Sum.elim (fun h => MvPolynomial.X (Sum.inl h) + MvPolynomial.C (x h))
        (fun p : A₁ × Bool => MvPolynomial.C (torusPoint x y (Sum.inr p)) * MvPolynomial.X (Sum.inr p)) v) ∧
      (∀ T : A₀ ⊕ A₁ → ℕ, (torusBox K A₀ A₁ T).map e.toLinearMap = torusBox K A₀ A₁ T) ∧
      (torusIdeal K A₀ A₁).map e = torusIdeal K A₀ A₁ := by
  set b : A₁ × Bool → Kˣ := fun p => if p.2 then y p.1 else (y p.1)⁻¹ with hb
  have hbv : ∀ p, (b p : K) = torusPoint x y (Sum.inr p) := by
    rintro ⟨i, _ | _⟩ <;> simp [hb, torusPoint]
  have hinv : (tr (-(-x)) b⁻¹⁻¹ : _ →ₐ[K] MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) = tr x b := by
    rw [neg_neg, inv_inv]
  let e := AlgEquiv.ofAlgHom (tr x b) (tr (-x) b⁻¹) (tr_comp x b) (by rw [← hinv]; exact tr_comp _ _)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro v
    change tr x b (MvPolynomial.X v) = _
    rw [tr_X]
    cases v with
    | inl h => rfl
    | inr p => simp only [Sum.elim_inr, hbv]
  · intro T
    apply le_antisymm (map_blockBox_le (tr x b) (tr_X_mem x b) _ T)
    have h2 := map_blockBox_le (K := K) (tr (-x) b⁻¹) (tr_X_mem _ _) (Sum.map id Prod.fst) T
    have h3 := Submodule.map_mono (f := e.toLinearMap) h2
    refine le_trans ?_ h3
    intro f hf
    refine ⟨(tr (-x) b⁻¹) f, ⟨f, hf, rfl⟩, ?_⟩
    change (tr x b).comp (tr (-x) b⁻¹) f = f
    rw [tr_comp]; rfl
  · rw [torusIdeal, Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    change tr x b _ = _
    simp only [map_sub, map_mul, map_one, tr_X, Sum.elim_inr, hb]
    rw [mul_mul_mul_comm, ← map_mul]
    simp
