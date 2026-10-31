-- Prove2me | solution 1 for DiazModulus.exists_tangent_dual
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:00:57.221313+00:00
-- url     : https://prove2.me/submissions/f0542c27-eee7-474f-9f36-44fea10bca86

import Mathlib
import Definitions.Def_DiazMultiplicity

open Complex ComplexConjugate

/-! # Dual pairs of invariant derivations and polynomials vanishing on a standard subgroup (DALAG Lemma 8.14)

Let `β(ξ, η) = ((Σ_{h'} ℓ_{h h'} ξ_{h'})_h, (Σ_{i'} ψ_{i i'} η_{i'})_i)`; its kernel is `V × L` by the definitions
of `V` and `L`. On `E = span{linForm ℓ_h, torusMono ψ_k − 1}` the derivation `D_w` acts by constants modulo
`I(S)`: `D_w(linForm ℓ_h) = (β w)₁ h` (a constant) and `D_w(torusMono ψ_k) = (β w)₂ k · torusMono ψ_k`, while
`linForm ℓ_h` and `torusMono ψ_k − 1` vanish on `S ⊆ V × T_ψ`. Take a basis `b` of `U = β(W)`, preimages
`w_i ∈ W` of `b_i`, a left inverse `g` of `U ↪ K^{A₀} × K^{A₁}` (vector spaces), and the functionals
`φ_j = b.coord j ∘ g`, so `φ_j(β w_i) = δ_ij`. Writing `φ_j` in coordinates gives `P_j ∈ E` with
`D_{w_i} P_j ≡ φ_j(β w_i) = δ_ij` modulo `I(S)`. Rank–nullity for `β|_W` gives
`dim U + dim (W ⊓ V × L) = dim W`. -/

namespace C13_W1
open DiazModulus MvPolynomial

theorem mem_torusVanishing_iff {K A₀ A₁ : Type*} [Field K] {S : Set (TorusGroup K A₀ A₁)}
    {f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K} :
    f ∈ torusVanishing S ↔ ∀ g ∈ S, eval (torusPt g) f = 0 := by
  simp [torusVanishing, Submodule.mem_iInf, RingHom.mem_ker]

theorem eig_mul {K σ : Type*} [Field K] (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    {a b : MvPolynomial σ K} {c d : K} (ha : D a = C c * a) (hb : D b = C d * b) :
    D (a * b) = C (c + d) * (a * b) := by
  rw [Derivation.leibniz, ha, hb, smul_eq_mul, smul_eq_mul, map_add]; ring

theorem eig_pow {K σ : Type*} [Field K] (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    {a : MvPolynomial σ K} {c : K} (ha : D a = C c * a) (n : ℕ) :
    D (a ^ n) = C ((n : K) * c) * a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, eig_mul D ih ha]; congr 2; push_cast; ring

theorem eig_prod {K σ ι : Type*} [Field K] (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    (s : Finset ι) (f : ι → MvPolynomial σ K) (c : ι → K) (h : ∀ i, D (f i) = C (c i) * f i) :
    D (∏ i ∈ s, f i) = C (∑ i ∈ s, c i) * ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, eig_mul D (h a) ih]

theorem torusDeriv_torusMono {K A₀ A₁ : Type*} [Field K] [Fintype A₁] (w : (A₀ → K) × (A₁ → K))
    (φ : A₁ → ℤ) :
    torusDeriv w (torusMono (A₀ := A₀) φ) = C (∑ i, (φ i : K) * w.2 i) * torusMono (A₀ := A₀) φ := by
  refine eig_prod (torusDeriv w) Finset.univ _ (fun i => (φ i : K) * w.2 i) (fun i => ?_)
  have hY : torusDeriv w (X (Sum.inr (i, true)) : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)
      = C (w.2 i) * X (Sum.inr (i, true)) := by simp
  have hZ : torusDeriv w (X (Sum.inr (i, false)) : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)
      = C (-w.2 i) * X (Sum.inr (i, false)) := by simp
  rw [eig_mul _ (eig_pow _ hY _) (eig_pow _ hZ _)]
  congr 2
  have : (((φ i).toNat : ℕ) : K) - (((-φ i).toNat : ℕ) : K) = (φ i : K) := by
    have h := congrArg (Int.cast : ℤ → K) (Int.toNat_sub_toNat_neg (φ i))
    push_cast at h; exact h
  rw [← this]; ring

theorem torusDeriv_linForm {K A₀ A₁ : Type*} [Field K] [Fintype A₀] (w : (A₀ → K) × (A₁ → K))
    (a : A₀ → K) : torusDeriv w (linForm (A₁ := A₁) a) = C (∑ h, a h * w.1 h) := by
  simp [linForm, map_sum]

theorem eval_linForm {K A₀ A₁ : Type*} [Field K] [Fintype A₀] (g : TorusGroup K A₀ A₁) (a : A₀ → K) :
    eval (torusPt g) (linForm (A₁ := A₁) a) = ∑ h, a h * Multiplicative.toAdd g.1 h := by
  simp [linForm, torusPt, torusPoint]

theorem eval_torusMono {K A₀ A₁ : Type*} [Field K] [Fintype A₁] (g : TorusGroup K A₀ A₁)
    (φ : A₁ → ℤ) : eval (torusPt g) (torusMono (A₀ := A₀) φ) = ((∏ i, g.2 i ^ φ i : Kˣ) : K) := by
  simp only [torusMono, map_prod, map_mul, map_pow, eval_X, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rcases Int.eq_nat_or_neg (φ i) with ⟨k, hk | hk⟩ <;> rw [hk] <;> simp [torusPt, torusPoint]

theorem lin_decomp {K A₀ A₁ : Type*} [Field K] [Fintype A₀] [Fintype A₁] [DecidableEq A₀] [DecidableEq A₁]
    (f : ((A₀ → K) × (A₁ → K)) →ₗ[K] K) (x : (A₀ → K) × (A₁ → K)) :
    f x = ∑ h, f ((fun h' => if h = h' then (1 : K) else 0), 0) * x.1 h +
      ∑ k, f (0, fun k' => if k = k' then (1 : K) else 0) * x.2 k := by
  have h1 := LinearMap.pi_apply_eq_sum_univ (f.comp (LinearMap.inl K _ (A₁ → K))) x.1
  have h2 := LinearMap.pi_apply_eq_sum_univ (f.comp (LinearMap.inr K (A₀ → K) _)) x.2
  simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply, smul_eq_mul] at h1 h2
  calc f x = f (x.1, 0) + f (0, x.2) := by rw [← map_add]; simp
    _ = _ := by
      rw [h1, h2]
      congr 1 <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

end C13_W1

open DiazModulus C13_W1 MvPolynomial in
theorem solution {K A₀ A₁ : Type*} [Field K] [Fintype A₀] [Fintype A₁] (ℓ : A₀ → A₀ → K) (ψ : A₁ → A₁ → ℤ)
    (V : Submodule K (A₀ → K)) (L : Submodule K (A₁ → K))
    (hV : ∀ v, v ∈ V ↔ ∀ h, ∑ h', ℓ h h' * v h' = 0) (hL : ∀ v, v ∈ L ↔ ∀ i, ∑ i', (ψ i i' : K) * v i' = 0)
    (W : Submodule K ((A₀ → K) × (A₁ → K))) (S : Set (TorusGroup K A₀ A₁)) (hS : S ⊆ standardSet V ψ) :
    ∃ (n : ℕ) (w : Fin n → (A₀ → K) × (A₁ → K)) (P : Fin n → (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)),
      n + Module.finrank K ↥(W ⊓ V.prod L) = Module.finrank K ↥W ∧ (∀ i, w i ∈ W) ∧
      (∀ j, P j ∈ torusVanishing S) ∧
      ∀ i j, torusDeriv (w i) (P j) - (if i = j then 1 else 0) ∈ torusVanishing S := by
  classical
  let β : ((A₀ → K) × (A₁ → K)) →ₗ[K] ((A₀ → K) × (A₁ → K)) :=
    LinearMap.prodMap (Matrix.mulVecLin (Matrix.of ℓ))
      (Matrix.mulVecLin (Matrix.of fun i i' => (ψ i i' : K)))
  have hβ1 : ∀ w h, (β w).1 h = ∑ h', ℓ h h' * w.1 h' := fun w h => by
    simp [β, Matrix.mulVec, dotProduct]
  have hβ2 : ∀ w i, (β w).2 i = ∑ i', (ψ i i' : K) * w.2 i' := fun w i => by
    simp [β, Matrix.mulVec, dotProduct]
  have hker : LinearMap.ker β = V.prod L := by
    ext w
    simp only [LinearMap.mem_ker, Submodule.mem_prod, hV, hL, Prod.ext_iff, funext_iff, hβ1, hβ2,
      Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
  set U := W.map β with hU
  let bU := Module.finBasis K U
  have hpre : ∀ i, ∃ w ∈ W, β w = bU i := fun i => Submodule.mem_map.mp (bU i).2
  choose w hwW hwβ using hpre
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective U.subtype (Submodule.ker_subtype U)
  let φ : Fin (Module.finrank K U) → ((A₀ → K) × (A₁ → K)) →ₗ[K] K := fun j => (bU.coord j).comp g
  have hφ : ∀ i j, φ j (β (w i)) = if i = j then 1 else 0 := by
    intro i j
    have : g (β (w i)) = bU i := by
      rw [hwβ]; exact LinearMap.congr_fun hg (bU i)
    simp [φ, this, Finsupp.single_apply]
  let P : Fin (Module.finrank K U) → MvPolynomial (A₀ ⊕ (A₁ × Bool)) K := fun j =>
    ∑ h, C (φ j ((fun h' => if h = h' then (1 : K) else 0), 0)) * linForm (A₁ := A₁) (ℓ h) +
    ∑ k, C (φ j (0, fun k' => if k = k' then (1 : K) else 0)) * (torusMono (A₀ := A₀) (ψ k) - 1)
  refine ⟨Module.finrank K U, w, P, ?_, hwW, ?_, ?_⟩
  · have h1 := LinearMap.finrank_range_add_finrank_ker (β.domRestrict W)
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, hker] at h1
    have h2 : (V.prod L).comap W.subtype = (W ⊓ V.prod L).comap W.subtype := by
      rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
    have h3 := LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (inf_le_left : W ⊓ V.prod L ≤ W))
    rw [h2, h3] at h1
    exact h1
  · intro j
    rw [mem_torusVanishing_iff]
    intro z hz
    obtain ⟨hx, hy⟩ := hS hz
    simp [P, eval_linForm, eval_torusMono, hy, (hV _).1 hx]
  · intro i j
    rw [mem_torusVanishing_iff]
    intro z hz
    obtain ⟨hx, hy⟩ := hS hz
    have hite : eval (torusPt z) (if i = j then (1 : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) else 0)
        = φ j (β (w i)) := by
      rw [hφ]; split_ifs <;> simp
    rw [map_sub, hite, lin_decomp (φ j) (β (w i)), sub_eq_zero]
    simp [P, torusDeriv_linForm, torusDeriv_torusMono, eval_torusMono, hy, hβ1, hβ2,
      map_sum]
