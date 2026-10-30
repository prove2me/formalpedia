-- Prove2me | solution 1 for DiazModulus.obstruction_1123
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:14:41.380996+00:00
-- url     : https://prove2.me/submissions/09ee6d4d-69d5-4bcd-958b-07d5071c7bc4

import Mathlib
import Definitions.Def_DiazModulus
import Definitions.Def_MultiplicityEstimateElem
import Theorems.Thm_DiazModulus_exists_coord_complement

open Complex ComplexConjugate

/-! # Step 6 of DALAG Th. 11.21: the obstruction subgroup from the multiplicity estimate

Apply the multiplicity estimate `hME` to the kernel vector `c` at `(D₀, D₁, M₀, M₁) = (T₀, T₁, S₀, S₁)`;
the vanishing premise is `hvan` verbatim. It returns `(V, φ, L₁, ℓ)` with the first three
properties of the conclusion and a counting bound valid for every finite `R` of integer vectors in
the box `|s_j| ≤ S₁` that is injective modulo the relation subgroup
`H = {s | Σ s_j u_j ∈ V ∧ ∀ k, Π_i (Π_j a_ji^{s_j})^{φ_ki} = 1}`. By `exists_coord_complement`
(O1), `span_ℚ H` has a coordinate complement `J` with `|J| + rank = |κ₁|`. Take `R` the box on `J`
(coordinates off `J` are zero); it has `(2S₁+1)^{|J|}` points, and two points of `R` differing by an
element of `H` differ by a vector of `span_ℚ H` supported on `J`, hence are equal. Finally
`(S₀+1)^ℓ ≤ (S₀+1)⋯(S₀+ℓ) = ℓ!·C(S₀+ℓ, ℓ)` (`Nat.pow_succ_le_ascFactorial`,
`Nat.ascFactorial_eq_factorial_mul_choose`), and multiplying the counting bound by `ℓ!` concludes. -/

namespace C14_O2
open DiazModulus

theorem box_card {κ : Type} [Fintype κ] [DecidableEq κ] (J : Finset κ) (M : ℕ) :
    (Fintype.piFinset fun j : κ => if j ∈ J then Finset.Icc (-(M : ℤ)) M else {0}).card
      = (2 * M + 1) ^ J.card := by
  rw [Fintype.card_piFinset]
  have h : ∀ j : κ, (if j ∈ J then Finset.Icc (-(M : ℤ)) M else {0}).card
      = if j ∈ J then 2 * M + 1 else 1 := by
    intro j
    split_ifs
    · rw [Int.card_Icc]; omega
    · rfl
  simp_rw [h]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

end C14_O2

open DiazModulus C14_O2 in
theorem solution (hME : DiazModulus.MultiplicityEstimateElem)
    {ι₀ ι₁ κ₀ κ₁ : Type} [Fintype ι₀] [Fintype ι₁] [Fintype κ₀] [Fintype κ₁]
    [DecidableEq ι₀] [DecidableEq ι₁]
    (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (u : κ₁ → ι₀ → ℂ) (a : κ₁ → ι₁ → ℂ) (T₀ T₁ S₀ S₁ : ℕ)
    (c : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) → ℂ) (hT₀ : 1 ≤ T₀) (hT₁ : 1 ≤ T₁) (ha : ∀ j i, a j i ≠ 0) (hc : c ≠ 0)
    (hvan : ∀ (rₑ : ℕ) (kₑ : Fin rₑ → κ₀) (sₑ : κ₁ → ℤ), rₑ ≤ (Fintype.card ι₀ + Fintype.card ι₁) * S₀ → (∀ j, |sₑ j| ≤ (((Fintype.card ι₀ + Fintype.card ι₁) * S₁ : ℕ) : ℤ)) →
        ∑ l, c l * (MvPolynomial.eval (∑ j, ((sₑ j : ℤ) : ℂ) • u j)
          ((List.ofFn fun k : Fin rₑ =>
            ((∑ h, (w (kₑ k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w (kₑ k)).2 i * (((l.2 i : ℕ) : ℂ) - T₁)) • LinearMap.id :
                Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod
            (∏ h, MvPolynomial.X h ^ (l.1 h : ℕ)))
        * ∏ i, (∏ j, a j i ^ sₑ j) ^ (((l.2 i : ℕ) : ℤ) - T₁)) = 0) :
    ∃ (V : Submodule ℂ (ι₀ → ℂ)) (q : ℕ) (φ : Fin q → ι₁ → ℤ) (L₁ : Submodule ℂ (ι₁ → ℂ)) (ℓ : ℕ),
      (∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0) ∧
      ℓ + Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w) ⊓ V.prod L₁)
        = Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w)) ∧
      Module.finrank ℂ ↥V + Module.finrank ℂ ↥L₁ < Fintype.card ι₀ + Fintype.card ι₁ ∧
      (S₀ + 1) ^ ℓ * (2 * S₁ + 1) ^ (Fintype.card κ₁ - Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : κ₁ → ℤ => fun j => (s j : ℚ)) ''
          {s : κ₁ → ℤ | (∑ j, (s j : ℂ) • u j) ∈ V ∧
            ∀ k, ∏ i, (∏ j, a j i ^ s j) ^ φ k i = 1})))
          * T₀ ^ Module.finrank ℂ ↥V * T₁ ^ Module.finrank ℂ ↥L₁
        ≤ ℓ.factorial * (2 ^ ((Fintype.card ι₀ + Fintype.card ι₁) * (Fintype.card ι₀ + Fintype.card ι₁ + 1) / 2)
            * (Fintype.card ι₀ + Fintype.card ι₁).factorial * 2 ^ Fintype.card ι₁
            * Fintype.card ι₀ ^ Fintype.card ι₀) * T₀ ^ Fintype.card ι₀ * T₁ ^ Fintype.card ι₁ := by
  classical
  obtain ⟨V, q, φ, L₁, ℓ, hL, hℓ, hdim, hcount⟩ :=
    hME ι₀ ι₁ κ₀ κ₁ w u a T₀ T₁ S₀ S₁ c hT₀ hT₁ ha hc hvan
  refine ⟨V, q, φ, L₁, ℓ, hL, hℓ, hdim, ?_⟩
  set H : Set (κ₁ → ℤ) := {s : κ₁ → ℤ | (∑ j, (s j : ℂ) • u j) ∈ V ∧
      ∀ k, ∏ i, (∏ j, a j i ^ s j) ^ φ k i = 1} with hH
  obtain ⟨J, hJ, hJc⟩ := DiazModulus.exists_coord_complement H
  set R := Fintype.piFinset fun j : κ₁ => if j ∈ J then Finset.Icc (-(S₁ : ℤ)) S₁ else {0}
    with hR
  have hRbox : ∀ s ∈ R, ∀ j, |s j| ≤ (S₁ : ℤ) := by
    intro s hs j
    have := Fintype.mem_piFinset.1 hs j
    split_ifs at this with hj
    · rw [Finset.mem_Icc] at this; exact abs_le.2 this
    · rw [Finset.mem_singleton] at this; rw [this]; simp
  have hRzero : ∀ s ∈ R, ∀ j ∉ J, s j = 0 := by
    intro s hs j hj
    have := Fintype.mem_piFinset.1 hs j
    rw [if_neg hj, Finset.mem_singleton] at this; exact this
  have hRinj : ∀ s ∈ R, ∀ s' ∈ R,
      ((∑ j, ((s j - s' j : ℤ) : ℂ) • u j) ∈ V ∧
        ∀ k, ∏ i, (∏ j, a j i ^ (s j - s' j)) ^ φ k i = 1) → s = s' := by
    intro s hs s' hs' hss
    have hmem : (fun j => ((s j - s' j : ℤ) : ℚ)) ∈
        Submodule.span ℚ ((fun s : κ₁ → ℤ => fun j => (s j : ℚ)) '' H) :=
      Submodule.subset_span ⟨fun j => s j - s' j, hss, rfl⟩
    have h0 := hJc _ hmem (fun j hj => by simp [hRzero s hs j hj, hRzero s' hs' j hj])
    funext j
    have := congrFun h0 j
    simp only [Pi.zero_apply, Int.cast_eq_zero] at this
    omega
  have hb := hcount R hRbox hRinj
  have hcard : R.card = (2 * S₁ + 1) ^ (Fintype.card κ₁ - Module.finrank ℚ ↥(Submodule.span ℚ
      ((fun s : κ₁ → ℤ => fun j => (s j : ℚ)) '' H))) := by
    rw [hR, box_card]; congr 1; omega
  have hasc : (S₀ + 1) ^ ℓ ≤ ℓ.factorial * (S₀ + ℓ).choose ℓ := by
    rw [← Nat.ascFactorial_eq_factorial_mul_choose]; exact Nat.pow_succ_le_ascFactorial _ _
  rw [← hcard]
  calc (S₀ + 1) ^ ℓ * R.card * T₀ ^ Module.finrank ℂ ↥V * T₁ ^ Module.finrank ℂ ↥L₁
      ≤ (ℓ.factorial * (S₀ + ℓ).choose ℓ) * R.card * T₀ ^ Module.finrank ℂ ↥V
          * T₁ ^ Module.finrank ℂ ↥L₁ := by gcongr
    _ = ℓ.factorial * ((S₀ + ℓ).choose ℓ * R.card * T₀ ^ Module.finrank ℂ ↥V
          * T₁ ^ Module.finrank ℂ ↥L₁) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hb
    _ = _ := by ring
