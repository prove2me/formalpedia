-- Prove2me | solution 1 for BellmanDP.ExistUnique.fundamental_inequality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:34:48.968404+00:00
-- url     : https://prove2.me/submissions/7d16f0ee-22aa-4971-91d9-abd00890a585

import Mathlib

open MeasureTheory


namespace BellmanDP.ExistUnique

theorem fi_core {N : ℕ} {S : Type*}
    (D : Set (EuclideanSpace ℝ (Fin N))) (p : EuclideanSpace ℝ (Fin N))
    (G : EuclideanSpace ℝ (Fin N) → S → Measure (EuclideanSpace ℝ (Fin N)))
    (g h : EuclideanSpace ℝ (Fin N) → S → ℝ) (f₁ F₁ : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf₁ : ∀ q : S, IntegrableOn f₁ D (G p q)) (hF₁ : ∀ q : S, IntegrableOn F₁ D (G p q))
    (f₂ F₂ : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf₂ : IsLUB (Set.range fun q : S => g p q + ∫ r in D, f₁ r ∂(G p q)) (f₂ p))
    (hF₂ : IsLUB (Set.range fun q : S => h p q + ∫ r in D, F₁ r ∂(G p q)) (F₂ p))
    (M : ℝ) (hM : ∀ q : S, |g p q - h p q| + ∫ r in D, |f₁ r - F₁ r| ∂(G p q) ≤ M) :
    |f₂ p - F₂ p| ≤ M := by
  have key : ∀ q : S, |(g p q + ∫ r in D, f₁ r ∂(G p q)) - (h p q + ∫ r in D, F₁ r ∂(G p q))| ≤ M := by
    intro q
    have h1 : (∫ r in D, f₁ r ∂(G p q)) - (∫ r in D, F₁ r ∂(G p q))
        = ∫ r in D, (f₁ r - F₁ r) ∂(G p q) := (integral_sub (hf₁ q) (hF₁ q)).symm
    have h2 : |∫ r in D, (f₁ r - F₁ r) ∂(G p q)| ≤ ∫ r in D, |f₁ r - F₁ r| ∂(G p q) := by
      have := norm_integral_le_integral_norm (μ := (G p q).restrict D) (fun r => f₁ r - F₁ r)
      simpa [Real.norm_eq_abs] using this
    have h3 := hM q
    calc _ = |(g p q - h p q) + ((∫ r in D, f₁ r ∂(G p q)) - (∫ r in D, F₁ r ∂(G p q)))| := by ring_nf
      _ ≤ |g p q - h p q| + |(∫ r in D, f₁ r ∂(G p q)) - (∫ r in D, F₁ r ∂(G p q))| := abs_add_le _ _
      _ ≤ M := by rw [h1]; linarith
  have A : f₂ p ≤ F₂ p + M := by
    apply hf₂.2
    rintro _ ⟨q, rfl⟩
    have := hF₂.1 ⟨q, rfl⟩
    have := (abs_le.mp (key q)).2
    simp only at *
    linarith
  have B : F₂ p ≤ f₂ p + M := by
    apply hF₂.2
    rintro _ ⟨q, rfl⟩
    have := hf₂.1 ⟨q, rfl⟩
    have := (abs_le.mp (key q)).1
    simp only at *
    linarith
  rw [abs_le]; constructor <;> linarith

end BellmanDP.ExistUnique

open BellmanDP.ExistUnique


theorem solution {N : ℕ} {S : Type*}
    (D : Set (EuclideanSpace ℝ (Fin N))) (p : EuclideanSpace ℝ (Fin N))
    (G : EuclideanSpace ℝ (Fin N) → S → Measure (EuclideanSpace ℝ (Fin N)))
    (g h : EuclideanSpace ℝ (Fin N) → S → ℝ) (f₁ F₁ : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf₁ : ∀ q : S, IntegrableOn f₁ D (G p q)) (hF₁ : ∀ q : S, IntegrableOn F₁ D (G p q))
    (f₂ F₂ : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf₂ : IsLUB (Set.range fun q : S => g p q + ∫ r in D, f₁ r ∂(G p q)) (f₂ p))
    (hF₂ : IsLUB (Set.range fun q : S => h p q + ∫ r in D, F₁ r ∂(G p q)) (F₂ p))
    (M : ℝ) (hM : ∀ q : S, |g p q - h p q| + ∫ r in D, |f₁ r - F₁ r| ∂(G p q) ≤ M) :
    |f₂ p - F₂ p| ≤ M := by
  exact fi_core D p G g h f₁ F₁ hf₁ hF₁ f₂ F₂ hf₂ hF₂ M hM
