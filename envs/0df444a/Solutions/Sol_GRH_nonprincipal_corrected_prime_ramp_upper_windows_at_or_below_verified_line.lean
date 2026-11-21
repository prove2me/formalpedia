-- Prove2me | solution 1 for GRH.nonprincipal_corrected_prime_ramp_upper_windows_at_or_below_verified_line
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T03:46:42.267948+00:00
-- url     : https://prove2.me/submissions/fca438ed-1891-4bfd-aede-10967846ea80
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_corrected_prime_ramp_changeLevel_le
import Theorems.Thm_GRH_primitive_nonprincipal_corrected_prime_ramp_upper_windows_at_or_below_verified_line
import Mathlib

open Finset ArithmeticFunction Set

theorem solution :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ θ : ℝ, 1/2 < θ → θ ≤ (0.8749570698:ℝ) → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
        ∀ X : ℝ, 1 ≤ X → ∃ Y : ℝ, X ≤ Y ∧ ∀ y ∈ Icc Y (Y^(1+δ)),
          (∑ n ∈ range (⌊y⌋₊+1), vonMangoldt n * (χ (n:ZMod q)).re * max (y/(n:ℝ)-1) 0) +
              y * (deriv χ.LFunction 1 / χ.LFunction 1).re ≤ C*y^θ := by
  intro q hq χ hχ θ hθ hθ'
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hn : χ.primitiveCharacter ≠ 1 := by
    intro e
    apply hχ
    calc
      χ = DirichletCharacter.changeLevel χ.conductor_dvd_level χ.primitiveCharacter :=
        χ.changeLevel_primitiveCharacter.symm
      _ = 1 := by rw [e, map_one]
  obtain ⟨δ,C,hδ,hC,hw⟩ :=
    GRH.primitive_nonprincipal_corrected_prime_ramp_upper_windows_at_or_below_verified_line
      χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hn θ hθ hθ'
  obtain ⟨D,hD,hb⟩ := GRH.corrected_prime_ramp_changeLevel_le q θ (by linarith) (by linarith)
  refine ⟨δ, C+D, hδ, add_nonneg hC hD, ?_⟩
  intro X hX
  obtain ⟨Y,hY,hy⟩ := hw X hX
  refine ⟨Y,hY,?_⟩
  intro y hmem
  have hd := hb χ.conductor χ.conductor_dvd_level χ.primitiveCharacter hn y (hX.trans (hY.trans hmem.1))
  rw [χ.changeLevel_primitiveCharacter] at hd
  have hd' := (abs_le.mp hd).2
  have hp := hy y hmem
  rw [add_mul]
  try dsimp only at hd'
  linarith only [hd', hp]
