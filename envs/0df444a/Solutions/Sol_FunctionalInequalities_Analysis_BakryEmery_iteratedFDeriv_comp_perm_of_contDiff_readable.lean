-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_perm_of_contDiff_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:41.911432+00:00
-- url     : https://prove2.me/submissions/077571af-5836-4c9d-aac5-1bc208ba403c

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IteratedDerivative
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_comp_swap_zero_one_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_succ_comp_perm_of_fix_zero_readable

noncomputable section
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Symmetry
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- Symmetry of the iterated derivatives of a `C^∞` map from a real inner product space to a real
normed space:
`∇ⁿf(x)(v ∘ σ) = ∇ⁿf(x)(v)` for every permutation `σ`. (Mathlib's
`ContDiffAt.iteratedFDeriv_comp_perm` requires analyticity.) -/
theorem solution {f : E → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : E)
    (v : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by
    induction n generalizing x with
    | zero =>
        have hv : v ∘ σ = v := Subsingleton.elim _ _
        rw [hv]
    | succ n ih =>
        have hfix :
            ∀ (y : E) (w : Fin (n + 1) → E) (τ : Equiv.Perm (Fin (n + 1))),
              τ 0 = 0 →
                iteratedFDeriv ℝ (n + 1) f y (w ∘ τ) =
                  iteratedFDeriv ℝ (n + 1) f y w := by
          intro y w τ hτ
          exact
            FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_succ_comp_perm_of_fix_zero_readable hf
              (fun z u ρ => ih z u ρ) y w τ hτ
        have hmul :
            ∀ (α β : Equiv.Perm (Fin (n + 1))),
              (∀ (y : E) (w : Fin (n + 1) → E),
                iteratedFDeriv ℝ (n + 1) f y (w ∘ α) =
                  iteratedFDeriv ℝ (n + 1) f y w) →
              (∀ (y : E) (w : Fin (n + 1) → E),
                iteratedFDeriv ℝ (n + 1) f y (w ∘ β) =
                  iteratedFDeriv ℝ (n + 1) f y w) →
              ∀ (y : E) (w : Fin (n + 1) → E),
                iteratedFDeriv ℝ (n + 1) f y
                    (w ∘ (α * β : Equiv.Perm (Fin (n + 1)))) =
                  iteratedFDeriv ℝ (n + 1) f y w := by
          intro α β hα hβ y w
          have hcomp :
              w ∘ (α * β : Equiv.Perm (Fin (n + 1))) =
                (w ∘ α) ∘ β := by
            ext z
            rfl
          calc
            iteratedFDeriv ℝ (n + 1) f y
                (w ∘ (α * β : Equiv.Perm (Fin (n + 1)))) =
                iteratedFDeriv ℝ (n + 1) f y ((w ∘ α) ∘ β) := by
                  rw [hcomp]
            _ = iteratedFDeriv ℝ (n + 1) f y (w ∘ α) :=
              hβ y (w ∘ α)
            _ = iteratedFDeriv ℝ (n + 1) f y w :=
              hα y w
        cases n with
        | zero =>
            have hσ : σ 0 = 0 := Fin.eq_zero _
            exact hfix x v σ hσ
        | succ m =>
            let s : Equiv.Perm (Fin (m + 2)) := Equiv.swap 0 1
            have hs :
                ∀ (y : E) (w : Fin (m + 2) → E),
                  iteratedFDeriv ℝ (m + 2) f y (w ∘ s) =
                    iteratedFDeriv ℝ (m + 2) f y w := by
              intro y w
              simpa [s] using
                (FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_swap_zero_one_readable (f := f) hf m y w)
            by_cases hk : σ 0 = 0
            · exact hfix x v σ hk
            · let a : Equiv.Perm (Fin (m + 2)) := Equiv.swap 1 (σ 0)
              let σ₁ : Equiv.Perm (Fin (m + 2)) := s * a * σ
              have h01 : (0 : Fin (m + 2)) ≠ 1 := by
                intro h
                have hh : (0 : ℕ) = 1 := congrArg Fin.val h
                exact Nat.zero_ne_one hh
              have h0k : (0 : Fin (m + 2)) ≠ σ 0 := by
                intro h
                apply hk
                exact h.symm
              have ha0 : a 0 = 0 := by
                simp [a, Equiv.swap_apply_of_ne_of_ne, h01, h0k]
              have hak : a (σ 0) = 1 := by
                simp [a]
              have hσ₁0 : σ₁ 0 = 0 := by
                simp only [σ₁, Equiv.Perm.coe_mul]
                simp [s, hak]
              have ha :
                  ∀ (y : E) (w : Fin (m + 2) → E),
                    iteratedFDeriv ℝ (m + 2) f y (w ∘ a) =
                      iteratedFDeriv ℝ (m + 2) f y w := by
                intro y w
                exact hfix y w a ha0
              have hσ₁ :
                  ∀ (y : E) (w : Fin (m + 2) → E),
                    iteratedFDeriv ℝ (m + 2) f y (w ∘ σ₁) =
                      iteratedFDeriv ℝ (m + 2) f y w := by
                intro y w
                exact hfix y w σ₁ hσ₁0
              have hσeq : a * s * σ₁ = σ := by
                calc
                  a * s * σ₁ = a * s * (s * a * σ) := by
                    rfl
                  _ = a * (s * s) * (a * σ) := by
                    simp only [mul_assoc]
                  _ = σ := by
                    simp [s, a]
              have hp :
                  iteratedFDeriv ℝ (m + 2) f x
                      (v ∘ (a * s * σ₁ : Equiv.Perm (Fin (m + 2)))) =
                    iteratedFDeriv ℝ (m + 2) f x v := by
                exact
                  hmul (a * s : Equiv.Perm (Fin (m + 2))) σ₁
                    (hmul a s ha hs) hσ₁ x v
              simpa [hσeq] using hp
