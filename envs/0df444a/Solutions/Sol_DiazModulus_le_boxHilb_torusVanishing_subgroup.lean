-- Prove2me | solution 1 for DiazModulus.le_boxHilb_torusVanishing_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:01:02.604625+00:00
-- url     : https://prove2.me/submissions/807e8516-a91b-4d86-9c79-a3c887d5d2e1

import Mathlib
import Definitions.Def_DiazMultiplicity
import Theorems.Thm_DiazModulus_linearIndependent_on_subgroup
import Theorems.Thm_DiazModulus_card_le_boxHilb_of_linearIndependent

open Complex ComplexConjugate

/-! # The ideal of a subgroup has a large Hilbert function

Index the box monomials `X_H^a Y_J^{λ⁺} Z_J^{λ⁻}` by `a : H → [0, T_h]` and `c : J → [0, 2T_j]`, with `λ_j = c_j − T_j`;
there are `Π_H (T_h + 1) · Π_J (2T_j + 1)` of them, and the exponent map is injective (`Int.toNat`, `omega`).
Each monomial lies in `torusBox T`: its block degree is `a_h ≤ T_h` on `X_h` and `λ_j⁺ + λ_j⁻ = |λ_j| ≤ T_j` on the
pair `(Y_j, Z_j)` (the block degree is a sum over the fibre of `Sum.map id Prod.fst`). Their images modulo
`I(Γ)` are linearly independent: a vanishing combination `f = Σ c_i X^{m_i}` lies in `I(Γ)`, is reduced
(`min(λ⁺, λ⁻) = 0`) and only involves `X_H, Y_J, Z_J`, so the imported node `linearIndependent_on_subgroup` (G6)
gives `f = 0`, and the monomials are independent (`MvPolynomial.basisMonomials`). The imported node
`card_le_boxHilb_of_linearIndependent` (F3) then bounds `h_{I(Γ)}(T)` from below by the number of monomials;
`torusBox` is finite-dimensional because its exponents lie in an `Iic` of `σ →₀ ℕ` (as in C1.1's T1). -/

namespace C13_Z5
open DiazModulus MvPolynomial

/-- The fibre-sum formula for `Finsupp.mapDomain` over a finite type. -/
theorem mapDomain_apply_eq_sum {σ ι : Type*} [Fintype σ] [DecidableEq ι] (β : σ → ι) (m : σ →₀ ℕ) (b : ι) :
    m.mapDomain β b = ∑ v, if β v = b then m v else 0 := by
  rw [Finsupp.mapDomain, Finsupp.sum_fintype _ _ (fun _ => Finsupp.single_zero _), Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

/-- (C1.1, T1) An exponent is bounded by its block degree. -/
theorem le_mapDomain {σ ι : Type*} (β : σ → ι) (m : σ →₀ ℕ) (s : σ) :
    m s ≤ m.mapDomain β (β s) := by
  conv_rhs => rw [← Finsupp.single_add_erase s m]
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.add_apply, Finsupp.single_eq_same]
  exact Nat.le_add_right _ _

/-- (C1.1, T1) The exponents of a block box form a finite set. -/
theorem finite_box {σ ι : Type*} [Finite σ] (β : σ → ι) (T : ι → ℕ) :
    Set.Finite {m : σ →₀ ℕ | ∀ b, m.mapDomain β b ≤ T b} := by
  classical
  have := Fintype.ofFinite σ
  let M : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun s => T (β s)
  refine (Set.finite_Iic M).subset ?_
  intro m hm s
  show m s ≤ T (β s)
  exact (le_mapDomain β m s).trans (hm (β s))

theorem finiteDimensional_torusBox (A₀ A₁ : Type*) [Fintype A₀] [Fintype A₁] (T : A₀ ⊕ A₁ → ℕ) :
    FiniteDimensional ℂ ↥(torusBox ℂ A₀ A₁ T) := by
  have := (finite_box (Sum.map id Prod.fst : A₀ ⊕ (A₁ × Bool) → A₀ ⊕ A₁) T).to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport ℂ _)

/-- The index set: `a : H → [0, T_h]` and `c : J → [0, 2T_j]`. -/
abbrev Idx {A₀ A₁ : Type*} (H : Finset A₀) (J : Finset A₁) (T : A₀ ⊕ A₁ → ℕ) :=
  (∀ h : ↥H, Fin (T (Sum.inl h.1) + 1)) × (∀ j : ↥J, Fin (2 * T (Sum.inr j.1) + 1))

open Classical in
/-- The exponent of the monomial `X_H^a Y_J^{λ⁺} Z_J^{λ⁻}`, `λ = c − T`. -/
noncomputable def expo {A₀ A₁ : Type*} (H : Finset A₀) (J : Finset A₁) (T : A₀ ⊕ A₁ → ℕ) (i : Idx H J T) :
    A₀ ⊕ (A₁ × Bool) → ℕ
  | Sum.inl h => if hh : h ∈ H then (i.1 ⟨h, hh⟩ : ℕ) else 0
  | Sum.inr (j, true) => if hj : j ∈ J then ((i.2 ⟨j, hj⟩ : ℤ) - T (Sum.inr j)).toNat else 0
  | Sum.inr (j, false) => if hj : j ∈ J then ((T (Sum.inr j) : ℤ) - i.2 ⟨j, hj⟩).toNat else 0

/-- The exponent as a finitely supported function. -/
noncomputable def expoF {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (H : Finset A₀) (J : Finset A₁)
    (T : A₀ ⊕ A₁ → ℕ) (i : Idx H J T) : A₀ ⊕ (A₁ × Bool) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (expo H J T i)

theorem expoF_apply {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (H : Finset A₀) (J : Finset A₁)
    (T : A₀ ⊕ A₁ → ℕ) (i : Idx H J T) (v : A₀ ⊕ (A₁ × Bool)) : expoF H J T i v = expo H J T i v := rfl

theorem expoF_injective {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (H : Finset A₀) (J : Finset A₁)
    (T : A₀ ⊕ A₁ → ℕ) : Function.Injective (expoF H J T) := by
  intro i i' hii
  have hv : ∀ v, expo H J T i v = expo H J T i' v := fun v => by
    rw [← expoF_apply, ← expoF_apply, hii]
  refine Prod.ext (funext fun h => Fin.ext ?_) (funext fun j => Fin.ext ?_)
  · obtain ⟨h, hh⟩ := h
    have := hv (Sum.inl h)
    simpa [expo, hh] using this
  · obtain ⟨j, hj⟩ := j
    have h1 := hv (Sum.inr (j, true))
    have h2 := hv (Sum.inr (j, false))
    simp only [expo, hj, dite_true] at h1 h2
    omega

theorem expoF_mem_box {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (H : Finset A₀) (J : Finset A₁)
    (T : A₀ ⊕ A₁ → ℕ) (i : Idx H J T) :
    monomial (expoF H J T i) (1 : ℂ) ∈ torusBox ℂ A₀ A₁ T := by
  classical
  rw [torusBox, blockBox, monomial_mem_restrictSupport]
  left
  intro b
  rw [mapDomain_apply_eq_sum]
  rcases b with h | j
  · simp only [Fintype.sum_sum_type, Sum.map_inl, id, Sum.inl.injEq, Sum.map_inr, reduceCtorEq,
      if_false, Finset.sum_const_zero, add_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, expoF_apply, expo]
    split_ifs with hh
    · exact Nat.lt_succ_iff.mp (i.1 ⟨h, hh⟩).2
    · exact Nat.zero_le _
  · simp [Fintype.sum_sum_type, Fintype.sum_prod_type, expoF_apply, expo, Finset.sum_add_distrib]
    split_ifs with hj
    · have hc : (i.2 ⟨j, hj⟩ : ℕ) < 2 * T (Sum.inr j) + 1 := (i.2 ⟨j, hj⟩).isLt
      omega
    · simp

end C13_Z5

open DiazModulus C13_Z5 MvPolynomial in
theorem solution {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (Γ : Subgroup (TorusGroup ℂ A₀ A₁)) (H : Finset A₀)
    (J : Finset A₁) (hH : ∀ x : A₀ → ℂ, ∃ v ∈ Submodule.span ℂ {v | ∃ g ∈ Γ, Multiplicative.toAdd g.1 = v}, ∀ h ∈ H, v h = x h)
    (hJ : ∀ φ : A₁ → ℤ, (∀ i ∉ J, φ i = 0) → (∀ g ∈ Γ, ∏ i, g.2 i ^ φ i = 1) → φ = 0)
    (T : A₀ ⊕ A₁ → ℕ) :
    (∏ h ∈ H, (T (Sum.inl h) + 1)) * ∏ j ∈ J, (2 * T (Sum.inr j) + 1)
      ≤ boxHilb (torusBox ℂ A₀ A₁) (torusVanishing (Γ : Set (TorusGroup ℂ A₀ A₁))) T := by
  classical
  let e : Idx H J T → MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ := fun i => monomial (expoF H J T i) 1
  have hcard : Fintype.card (Idx H J T) = (∏ h ∈ H, (T (Sum.inl h) + 1)) * ∏ j ∈ J, (2 * T (Sum.inr j) + 1) := by
    rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_coe_sort H (fun h => T (Sum.inl h) + 1), Finset.prod_coe_sort J (fun j => 2 * T (Sum.inr j) + 1)]
  have hred : ∀ i, e i ∈ restrictSupport ℂ (torusReduced A₀ A₁) := by
    intro i
    rw [monomial_mem_restrictSupport]
    left
    intro j
    simp only [expoF_apply, expo]
    split_ifs <;> omega
  have hsupp : ∀ i, e i ∈ restrictSupport ℂ {m : A₀ ⊕ (A₁ × Bool) →₀ ℕ |
      (∀ h ∉ H, m (Sum.inl h) = 0) ∧ ∀ i ∉ J, ∀ b, m (Sum.inr (i, b)) = 0} := by
    intro i
    rw [monomial_mem_restrictSupport]
    left
    refine ⟨fun h hh => by simp [expoF_apply, expo, hh], fun j hj b => ?_⟩
    cases b <;> simp [expoF_apply, expo, hj]
  have hli : LinearIndependent ℂ (fun i => Ideal.Quotient.mk (torusVanishing (Γ : Set (TorusGroup ℂ A₀ A₁))) (e i)) := by
    rw [linearIndependent_iff']
    intro s g hg
    set f := ∑ i ∈ s, g i • e i with hf
    have hmk : Ideal.Quotient.mkₐ ℂ (torusVanishing (Γ : Set (TorusGroup ℂ A₀ A₁))) f = 0 := by
      rw [hf, map_sum]
      simpa [map_smul] using hg
    have hfI : f ∈ torusVanishing (Γ : Set (TorusGroup ℂ A₀ A₁)) := Ideal.Quotient.eq_zero_iff_mem.mp hmk
    have hf0 : f = 0 := by
      refine DiazModulus.linearIndependent_on_subgroup Γ H J hH hJ f ?_ ?_ ?_
      · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hred i)
      · intro m hm
        have hmem : f ∈ restrictSupport ℂ {m : A₀ ⊕ (A₁ × Bool) →₀ ℕ |
            (∀ h ∉ H, m (Sum.inl h) = 0) ∧ ∀ i ∉ J, ∀ b, m (Sum.inr (i, b)) = 0} :=
          Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hsupp i)
        exact (mem_restrictSupport_iff ℂ).mp hmem hm
      · intro g hg
        have := hfI
        simp only [torusVanishing, Submodule.mem_iInf] at this
        exact this g hg
    have hlin : LinearIndependent ℂ e := by
      have := (MvPolynomial.basisMonomials (A₀ ⊕ (A₁ × Bool)) ℂ).linearIndependent.comp _
        (expoF_injective H J T)
      simpa [MvPolynomial.coe_basisMonomials, Function.comp_def] using this
    exact linearIndependent_iff'.mp hlin s g hf0.symm.symm
  have key := DiazModulus.card_le_boxHilb_of_linearIndependent (torusBox ℂ A₀ A₁)
    (finiteDimensional_torusBox A₀ A₁) (torusVanishing (Γ : Set (TorusGroup ℂ A₀ A₁))) T e
    (fun i => expoF_mem_box H J T i) hli
  rw [hcard] at key
  exact key
