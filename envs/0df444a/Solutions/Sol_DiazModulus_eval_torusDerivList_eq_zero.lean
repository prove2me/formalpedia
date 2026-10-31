-- Prove2me | solution 1 for DiazModulus.eval_torusDerivList_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T09:57:54.463814+00:00
-- url     : https://prove2.me/submissions/54b14969-451b-405e-8d08-0f333c2ed314

import Mathlib
import Definitions.Def_DiazMultiplicity
import Theorems.Thm_DiazModulus_eval_torusDerivList_torusCoeffPoly

open Complex ComplexConjugate

/-! # hME's premise kills the derivatives of `P` along `W` at the points `g_s`

Fix `s` with `|s_j| ≤ dM₁` and let `V_n` be the span of the `D_{wₑ(k₁)} ⋯ D_{wₑ(k_n)} P` over all `k : Fin n → B₀`.
At `g_s = hmePoint uₑ a s`, `torusPt g_s` is `torusPoint (Σ_j s_j uₑ_j) (Π_j a_j^{s_j})`, and the imported node
`eval_torusDerivList_torusCoeffPoly` (O4) turns `eval (D_{wₑ ∘ k} P)` into hME's premise sum; with `a = aₑ`
(`Units.coe_prod`, `Units.val_zpow_eq_zpow_val`) it is `0` whenever `n ≤ dM₀`. So the linear form `eval (torusPt g_s)`
kills `V_n` for `n ≤ dM₀` (`Submodule.span_induction`). It remains that `D_l P ∈ V_{|l|}` for every list `l` in
`W = span(range wₑ)`: by induction on `l`, using `D_w (V_n) ⊆ V_{n+1}` for `w ∈ W`. The map `w ↦ D_w` is linear
(`MvPolynomial.derivation_ext` on the variables), so it suffices to take `w = wₑ b`, and then
`D_{wₑ b} D_{wₑ ∘ k} P = D_{wₑ ∘ Fin.cons b k} P` (`List.ofFn_succ`). -/

namespace C13_O5
open DiazModulus MvPolynomial

variable {K A₀ A₁ : Type*} [Field K]

theorem torusDeriv_add (w w' : (A₀ → K) × (A₁ → K)) : torusDeriv (w + w') = torusDeriv w + torusDeriv w' := by
  apply MvPolynomial.derivation_ext
  rintro (h | ⟨i, b⟩)
  · simp
  · cases b <;> simp <;> ring

theorem torusDeriv_smul (c : K) (w : (A₀ → K) × (A₁ → K)) : torusDeriv (c • w) = c • torusDeriv w := by
  apply MvPolynomial.derivation_ext
  rintro (h | ⟨i, b⟩)
  · simp [smul_eq_C_mul]
  · cases b <;> simp [smul_eq_C_mul] <;> ring

theorem torusDeriv_zero : torusDeriv (0 : (A₀ → K) × (A₁ → K)) = 0 := by
  simpa using torusDeriv_smul (0 : K) (0 : (A₀ → K) × (A₁ → K))

theorem torusDerivList_cons (w : (A₀ → K) × (A₁ → K)) (l : List ((A₀ → K) × (A₁ → K)))
    (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) :
    torusDerivList (w :: l) f = torusDeriv w (torusDerivList l f) := by
  simp [torusDerivList, Module.End.mul_apply]

/-- `V_n`, the span of the `D_{wₑ ∘ k} P` with `k : Fin n → B₀`. -/
noncomputable def Vn {B₀ : Type*} (wₑ : B₀ → (A₀ → K) × (A₁ → K)) (P : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)
    (n : ℕ) : Submodule K (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) :=
  Submodule.span K {Q | ∃ k : Fin n → B₀, Q = torusDerivList (List.ofFn fun i => wₑ (k i)) P}

theorem torusDeriv_mem_Vn {B₀ : Type*} (wₑ : B₀ → (A₀ → K) × (A₁ → K)) (P : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)
    (n : ℕ) (Q : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) (hQ : Q ∈ Vn wₑ P n) (w : (A₀ → K) × (A₁ → K))
    (hw : w ∈ Submodule.span K (Set.range wₑ)) : torusDeriv w Q ∈ Vn wₑ P (n + 1) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, rfl⟩ := hw
    have hle : Vn wₑ P n ≤ (Vn wₑ P (n + 1)).comap (torusDeriv (wₑ b)).toLinearMap := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      refine Submodule.subset_span ⟨Fin.cons b k, ?_⟩
      simp only [Derivation.coeFn_coe, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, torusDerivList_cons]
    exact hle hQ
  | zero => simp [torusDeriv_zero]
  | add w w' _ _ h h' => rw [torusDeriv_add, Derivation.add_apply]; exact Submodule.add_mem _ h h'
  | smul c w _ h => rw [torusDeriv_smul, Derivation.smul_apply]; exact Submodule.smul_mem _ c h

theorem torusDerivList_mem_Vn {B₀ : Type*} (wₑ : B₀ → (A₀ → K) × (A₁ → K))
    (P : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) (l : List ((A₀ → K) × (A₁ → K)))
    (hl : ∀ w ∈ l, w ∈ Submodule.span K (Set.range wₑ)) : torusDerivList l P ∈ Vn wₑ P l.length := by
  induction l with
  | nil => exact Submodule.subset_span ⟨Fin.elim0, by simp⟩
  | cons w l ih =>
    rw [torusDerivList_cons, List.length_cons]
    exact torusDeriv_mem_Vn wₑ P _ _ (ih fun w' h => hl w' (by simp [h])) w (hl w (by simp))

end C13_O5

open DiazModulus C13_O5 in
theorem solution {A₀ A₁ B₀ B₁ : Type*} [Fintype A₀] [Fintype A₁] [Fintype B₁]
    [DecidableEq A₀] [DecidableEq A₁]
    (wₑ : B₀ → (A₀ → ℂ) × (A₁ → ℂ)) (uₑ : B₁ → A₀ → ℂ) (aₑ : B₁ → A₁ → ℂ) (D₀ D₁ M₀ M₁ : ℕ)
    (cₑ : (A₀ → Fin (D₀ + 1)) × (A₁ → Fin (2 * D₁ + 1)) → ℂ)
    (a : B₁ → A₁ → ℂˣ) (ha : ∀ j i, (a j i : ℂ) = aₑ j i)
    (hprem : (∀ (rₑ : ℕ) (kₑ : Fin rₑ → B₀) (sₑ : B₁ → ℤ), rₑ ≤ (Fintype.card A₀ + Fintype.card A₁) * M₀ → (∀ j, |sₑ j| ≤ (((Fintype.card A₀ + Fintype.card A₁) * M₁ : ℕ) : ℤ)) →
        ∑ l, cₑ l * (MvPolynomial.eval (∑ j, ((sₑ j : ℤ) : ℂ) • uₑ j)
          ((List.ofFn fun k : Fin rₑ =>
            ((∑ h, (wₑ (kₑ k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (wₑ (kₑ k)).2 i * (((l.2 i : ℕ) : ℂ) - D₁)) • LinearMap.id :
                Module.End ℂ (MvPolynomial A₀ ℂ)))).prod
            (∏ h, MvPolynomial.X h ^ (l.1 h : ℕ)))
        * ∏ i, (∏ j, aₑ j i ^ sₑ j) ^ (((l.2 i : ℕ) : ℤ) - D₁)) = 0)) :
    ∀ l : List ((A₀ → ℂ) × (A₁ → ℂ)), l.length ≤ (Fintype.card A₀ + Fintype.card A₁) * M₀ → (∀ w ∈ l, w ∈ Submodule.span ℂ (Set.range wₑ)) →
      ∀ s : B₁ → ℤ, (∀ b, |s b| ≤ (((Fintype.card A₀ + Fintype.card A₁) * M₁ : ℕ) : ℤ)) →
        MvPolynomial.eval (torusPt (hmePoint uₑ a s)) (torusDerivList l (torusCoeffPoly D₀ D₁ cₑ)) = 0 := by
  intro l hl hW s hs
  suffices key : ∀ Q ∈ Vn wₑ (torusCoeffPoly D₀ D₁ cₑ) l.length, MvPolynomial.eval (torusPt (hmePoint uₑ a s)) Q = 0 from
    key _ (torusDerivList_mem_Vn wₑ _ l hW)
  intro Q hQ
  induction hQ using Submodule.span_induction with
  | mem Q hQ =>
    obtain ⟨k, rfl⟩ := hQ
    have hpt : torusPt (hmePoint uₑ a s) = torusPoint (∑ j, ((s j : ℤ) : ℂ) • uₑ j) (fun i => ∏ j, a j i ^ s j) :=
      rfl
    rw [hpt, DiazModulus.eval_torusDerivList_torusCoeffPoly]
    simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, ha]
    exact hprem _ k s hl hs
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [MvPolynomial.smul_eval, hx, mul_zero]
