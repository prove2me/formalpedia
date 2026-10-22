-- Prove2me | solution 1 for CertDRO.Conc.cover_implication
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:01:53.10361+00:00
-- url     : https://prove2.me/submissions/0a0167c2-6f52-4297-9eba-2d2b51b60c55

import Mathlib
import Definitions.Def_CertDRO_Conc_model

set_option autoImplicit false

theorem solution {d : ℕ} (Θ S : Set (CertDRO.SGD.Param d)) (C : Finset (CertDRO.SGD.Param d))
    (g : CertDRO.SGD.Param d → ℝ)
    (Lzz Lzθ γ Lc t : ℝ) (hγ : Lzz < γ) (hLc : 0 < Lc) (hLzθ : 0 < Lzθ) (ht : 0 < t)
    (hΘS : Θ ⊆ S) (hCS : ∀ x ∈ C, x ∈ S)
    (hcover : Θ ⊆ ⋃ x ∈ C, Metric.closedBall x ((γ - Lzz) * t / (4 * Lc * Lzθ)))
    (hg : ∀ θ₁ ∈ S, ∀ θ₂ ∈ S, |g θ₁ - g θ₂| ≤ 2 * Lc * Lzθ / (γ - Lzz) * ‖θ₁ - θ₂‖)
    (hC : ∀ θ ∈ C, |g θ| ≤ t / 2) :
    ⨆ θ : Θ, |g θ| ≤ t := by
  have hγ' : 0 < γ - Lzz := sub_pos.mpr hγ
  have hLL : 0 < Lc * Lzθ := mul_pos hLc hLzθ
  haveI : Nonempty (Set.Elem Θ) ∨ IsEmpty (Set.Elem Θ) := by
    by_cases h : Nonempty (Set.Elem Θ)
    · exact Or.inl h
    · exact Or.inr (not_nonempty_iff.mp h)
  rcases this with hne | hemp
  · apply ciSup_le
    rintro ⟨θ, hθ⟩
    have := hcover hθ
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hx, hxd⟩ := this
    have hd : ‖θ - x‖ ≤ (γ - Lzz) * t / (4 * Lc * Lzθ) := by
      simpa [dist_eq_norm] using hxd
    have h1 := hg θ (hΘS hθ) x (hCS x hx)
    have h2 := hC x hx
    have h3 : 2 * Lc * Lzθ / (γ - Lzz) * ‖θ - x‖ ≤ t / 2 := by
      calc 2 * Lc * Lzθ / (γ - Lzz) * ‖θ - x‖
          ≤ 2 * Lc * Lzθ / (γ - Lzz) * ((γ - Lzz) * t / (4 * Lc * Lzθ)) := by
            apply mul_le_mul_of_nonneg_left hd
            positivity
        _ = t / 2 := by field_simp; ring
    show |g θ| ≤ t
    have : |g θ| ≤ |g θ - g x| + |g x| := by
      calc |g θ| = |(g θ - g x) + g x| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    linarith
  · simp [Real.iSup_of_isEmpty, ht.le]
