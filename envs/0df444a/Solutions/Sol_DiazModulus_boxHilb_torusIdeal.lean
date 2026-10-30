-- Prove2me | solution 1 for DiazModulus.boxHilb_torusIdeal
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:09:26.835027+00:00
-- url     : https://prove2.me/submissions/cd9edede-c4fd-4a8a-8d4e-e266b303540e

import Mathlib
import Definitions.Def_DiazHilbertBox
import Theorems.Thm_DiazModulus_restrictSupport_block_filtration
import Theorems.Thm_DiazModulus_torus_reduce_mem_restrictSupport
import Theorems.Thm_DiazModulus_torus_reduced_inf_eq_bot
import Theorems.Thm_DiazModulus_boxHilb_add_finrank_inf

open Complex ComplexConjugate

/-! # The Hilbert function of the torus ideal on the per-coordinate box

Let `B = torusBox T`, `R` the reduced combinations and `J = J₀` (as a `K`-subspace). The boxes are
finite-dimensional (`restrictSupport_block_filtration`). By `torus_reduce_mem_restrictSupport`
every `f ∈ B` is `g + (f − g)` with `g ∈ B ⊓ R` and `f − g ∈ B ⊓ J`, so `B = (B ⊓ R) ⊔ (B ⊓ J)`;
by `torus_reduced_inf_eq_bot` the two pieces meet in `0`. Grassmann's formula
(`Submodule.finrank_sup_add_finrank_inf_eq`) gives `dim B = dim (B ⊓ R) + dim (B ⊓ J)`, and
`boxHilb_add_finrank_inf` gives `h_{J₀}(T) + dim (B ⊓ J) = dim B`, so `h_{J₀}(T) = dim (B ⊓ R)`.
Now `B ⊓ R` is `restrictSupport` of the reduced exponents in the box, with the monomial basis,
so its dimension is the number of such exponents. These are `X^a Y^b Z^c` with `a_h ≤ T_h`,
`b_i + c_i ≤ T_i` and `min(b_i, c_i) = 0`; `(b_i, c_i) ↦ T_i + b_i − c_i ∈ [0, 2T_i]` is a bijection
(inverse `s ↦ (s − T_i, T_i − s)`), so they are counted by `Π_h (T_h + 1) · Π_i (2T_i + 1)`. -/

namespace C11_T4
open DiazModulus

variable {A₀ A₁ : Type*}

theorem mapDomain_inl (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) (h : A₀) :
    m.mapDomain (Sum.map id Prod.fst) (Sum.inl h) = m (Sum.inl h) := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [Finsupp.mapDomain_add, hp, hq]
  | single a n =>
    rcases a with h' | ⟨j, b⟩ <;> simp [Finsupp.mapDomain_single, Finsupp.single_apply]

theorem mapDomain_inr (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) (i : A₁) :
    m.mapDomain (Sum.map id Prod.fst) (Sum.inr i)
      = m (Sum.inr (i, true)) + m (Sum.inr (i, false)) := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [Finsupp.mapDomain_add, Finsupp.add_apply, hp, hq]; omega
  | single a n =>
    rcases a with h' | ⟨j, b⟩
    · simp [Finsupp.mapDomain_single]
    · by_cases hj : j = i
      · subst hj; cases b <;> simp [Finsupp.mapDomain_single]
      · simp [Finsupp.mapDomain_single, hj]

/-- The reduced exponents in the box `T`, coordinatewise. -/
def RedBox (T : A₀ ⊕ A₁ → ℕ) (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) : Prop :=
  (∀ h, m (Sum.inl h) ≤ T (Sum.inl h)) ∧
    ∀ i, m (Sum.inr (i, true)) + m (Sum.inr (i, false)) ≤ T (Sum.inr i) ∧
      (m (Sum.inr (i, true)) = 0 ∨ m (Sum.inr (i, false)) = 0)

theorem redBox_iff (T : A₀ ⊕ A₁ → ℕ) (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) :
    m ∈ {m : A₀ ⊕ (A₁ × Bool) →₀ ℕ | ∀ b, m.mapDomain (Sum.map id Prod.fst) b ≤ T b} ∩
        torusReduced A₀ A₁ ↔ RedBox T m := by
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, torusReduced, RedBox]
  constructor
  · rintro ⟨hb, hr⟩
    refine ⟨fun h => (mapDomain_inl m h) ▸ hb (Sum.inl h), fun i => ⟨?_, hr i⟩⟩
    exact (mapDomain_inr m i) ▸ hb (Sum.inr i)
  · rintro ⟨h0, h1⟩
    refine ⟨fun b => ?_, fun i => (h1 i).2⟩
    rcases b with h | i
    · rw [mapDomain_inl]; exact h0 h
    · rw [mapDomain_inr]; exact (h1 i).1

/-- The number of values of each coordinate block. -/
def width (T : A₀ ⊕ A₁ → ℕ) (v : A₀ ⊕ A₁) : ℕ :=
  Sum.elim (fun h => T (Sum.inl h) + 1) (fun i => 2 * T (Sum.inr i) + 1) v

/-- The inverse of the count: `s ↦ (s − T_i, T_i − s)` on each `Y`/`Z` pair. -/
noncomputable def unfold [Finite A₀] [Finite A₁] (T : A₀ ⊕ A₁ → ℕ)
    (z : ∀ v, Fin (width T v)) : A₀ ⊕ (A₁ × Bool) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun u => match u with
    | Sum.inl h => (z (Sum.inl h) : ℕ)
    | Sum.inr (i, b) => if b then (z (Sum.inr i) : ℕ) - T (Sum.inr i)
        else T (Sum.inr i) - (z (Sum.inr i) : ℕ)

theorem unfold_redBox [Finite A₀] [Finite A₁] (T : A₀ ⊕ A₁ → ℕ) (z : ∀ v, Fin (width T v)) :
    RedBox T (unfold T z) := by
  refine ⟨fun h => ?_, fun i => ?_⟩
  · have := (z (Sum.inl h)).isLt
    simp only [unfold, Finsupp.equivFunOnFinite_symm_apply_apply, width, Sum.elim_inl] at this ⊢
    omega
  · have := (z (Sum.inr i)).isLt
    simp only [unfold, Finsupp.equivFunOnFinite_symm_apply_apply, width, Sum.elim_inr,
      if_true, Bool.false_eq_true, if_false] at this ⊢
    omega

/-- The count: reduced exponents in the box ↔ `Π_v Fin (width T v)`. -/
noncomputable def countEquiv [Finite A₀] [Finite A₁] (T : A₀ ⊕ A₁ → ℕ) :
    {m // RedBox T m} ≃ ∀ v, Fin (width T v) where
  toFun m v := match v with
    | Sum.inl h => ⟨m.1 (Sum.inl h), Nat.lt_succ_of_le (m.2.1 h)⟩
    | Sum.inr i => ⟨T (Sum.inr i) + m.1 (Sum.inr (i, true)) - m.1 (Sum.inr (i, false)), by
        have := (m.2.2 i).1
        simp only [width, Sum.elim_inr]
        omega⟩
  invFun z := ⟨unfold T z, unfold_redBox T z⟩
  left_inv m := by
    obtain ⟨m, hm0, hm1⟩ := m
    refine Subtype.ext (Finsupp.ext fun u => ?_)
    rcases u with h | ⟨i, b⟩
    · simp [unfold]
    · have := hm1 i
      cases b <;> simp only [unfold, Finsupp.equivFunOnFinite_symm_apply_apply, if_true,
        Bool.false_eq_true, if_false] <;> omega
  right_inv z := by
    funext v
    rcases v with h | i
    · rfl
    · refine Fin.ext ?_
      have := (z (Sum.inr i)).isLt
      simp only [unfold, Finsupp.equivFunOnFinite_symm_apply_apply, if_true,
        Bool.false_eq_true, if_false]
      simp only [width, Sum.elim_inr] at this
      omega

end C11_T4

open DiazModulus C11_T4 in
theorem solution {K A₀ A₁ : Type*} [Field K] [Fintype A₀] [Fintype A₁] (T : A₀ ⊕ A₁ → ℕ) :
    boxHilb (torusBox K A₀ A₁) (torusIdeal K A₀ A₁) T
      = (∏ h, (T (Sum.inl h) + 1)) * ∏ i, (2 * T (Sum.inr i) + 1) := by
  classical
  have hfin : ∀ T' : A₀ ⊕ A₁ → ℕ, FiniteDimensional K ↥(torusBox K A₀ A₁ T') :=
    (DiazModulus.restrictSupport_block_filtration (K := K) (Sum.map id Prod.fst)).2.1
  have hF1 := DiazModulus.boxHilb_add_finrank_inf (torusBox K A₀ A₁) hfin (torusIdeal K A₀ A₁) T
  set B := torusBox K A₀ A₁ T
  set R := MvPolynomial.restrictSupport K (torusReduced A₀ A₁)
  set J := Submodule.restrictScalars K (torusIdeal K A₀ A₁)
  have := hfin T
  have hsup : (B ⊓ R) ⊔ (B ⊓ J) = B := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) fun f hf => ?_
    obtain ⟨g, hg, hfg⟩ := DiazModulus.torus_reduce_mem_restrictSupport T f hf
    refine Submodule.mem_sup.mpr ⟨g, hg, f - g, ⟨B.sub_mem hf (Submodule.mem_inf.mp hg).1, hfg⟩,
      add_sub_cancel g f⟩
  have hinf : (B ⊓ R) ⊓ (B ⊓ J) = ⊥ := by
    refine eq_bot_iff.mpr fun f hf => ?_
    rw [← DiazModulus.torus_reduced_inf_eq_bot (K := K) (A₀ := A₀) (A₁ := A₁)]
    exact ⟨hf.1.2, hf.2.2⟩
  have hG := Submodule.finrank_sup_add_finrank_inf_eq (B ⊓ R) (B ⊓ J)
  rw [hsup, hinf, finrank_bot] at hG
  have hBR : B ⊓ R = MvPolynomial.restrictSupport K {m | RedBox T m} := by
    ext f
    simp only [Submodule.mem_inf, B, R, torusBox, blockBox, MvPolynomial.mem_restrictSupport_iff]
    rw [← Set.subset_inter_iff]
    exact Iff.of_eq (congrArg _ (Set.ext fun m => redBox_iff T m))
  have hcount : Module.finrank K ↥(B ⊓ R)
      = (∏ h, (T (Sum.inl h) + 1)) * ∏ i, (2 * T (Sum.inr i) + 1) := by
    rw [hBR, Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport K _)]
    rw [show Nat.card ↥{m | RedBox T m} = Nat.card {m // RedBox T m} from rfl,
      Nat.card_congr (countEquiv T), Nat.card_pi]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [Fintype.prod_sum_type]
    rfl
  omega
