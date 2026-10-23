-- Prove2me | solution 1 for FoodTrace.Adoption.proposition_3
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:57:28.621877+00:00
-- url     : https://prove2.me/submissions/a41a1d81-e4e5-43c9-8e16-2aeda1184561

import Mathlib
import Definitions.Def_FoodTrace_Adoption_Model

open FoodTrace.Adoption

/-- Parameters with `ρ_e = 0` (allowed by `Standing`): `n = 2`, `ρ = 1/2`, `e = 1`, `c_p = 1/2`. -/
noncomputable def g80_P : Params := ⟨2, 1/2, 0, 1, 1/2⟩

theorem g80_standing : Standing g80_P := by
  refine ⟨le_refl _, le_refl _, by norm_num [g80_P], by norm_num [g80_P], by norm_num [g80_P],
    by norm_num [g80_P], ?_⟩
  norm_num [cpBar, ρτ, g80_P]

theorem g80_wNe : wNe g80_P = 2 := by
  norm_num [wNe, pNe, ell, ρτ, g80_P]

theorem g80_wTe : wTe g80_P = 3 := by
  norm_num [wTe, ρτ, g80_P]

theorem g80_rTe : rTe g80_P = 5 := by
  norm_num [rTe, ρτ, g80_P]

theorem g80_pi0Te (r : ℝ) : pi0Te g80_P r = 2 * (r - 3) := by
  rw [pi0Te, g80_wTe]; norm_num [g80_P]

theorem g80_pi0Ne (r : ℝ) : pi0Ne g80_P r = 2 * (r - 2) := by
  rw [pi0Ne, g80_wNe]; norm_num [g80_P]

theorem g80_bpc : BPC g80_P := by
  unfold BPC; rw [g80_pi0Te, g80_pi0Ne]; norm_num

theorem solution : ¬ (∀ (P : Params) (hP : Standing P) (hBPC : BPC P),
    ∃ r₁ r₂ : ℝ, rNe P < r₁ ∧ r₁ < rTe P ∧ rTe P < r₂ ∧
      pi0To P r₁ = pi0Ne P r₁ ∧ pi0Te P r₂ = pi0Ne P r₂ ∧
      (∀ r : ℝ, (∃ s : Strategy P, IsSPNE .N P r s) ∧ (∃ s : Strategy P, IsSPNE .T P r s)) ∧
      ∀ (r : ℝ) (sN sT : Strategy P), IsSPNE .N P r sN → IsSPNE .T P r sT →
        (r₁ < r → r < r₂ → retailerProfit .T P r sT < retailerProfit .N P r sN) ∧
        (¬ (r₁ < r ∧ r < r₂) → retailerProfit .N P r sN ≤ retailerProfit .T P r sT)) := by
  intro h
  obtain ⟨r₁, r₂, -, -, -, -, h2, -⟩ := h g80_P g80_standing g80_bpc
  rw [g80_pi0Te, g80_pi0Ne] at h2
  linarith
