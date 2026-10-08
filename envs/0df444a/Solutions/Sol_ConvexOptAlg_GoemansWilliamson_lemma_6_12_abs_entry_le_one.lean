-- Prove2me | solution 1 for ConvexOptAlg.GoemansWilliamson.lemma_6_12_abs_entry_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:11:42.911386+00:00
-- url     : https://prove2.me/submissions/c4e2a018-1704-4a7c-8c60-3dce9b196332

import Mathlib
import Definitions.Def_ConvexOptAlg_GoemansWilliamson_Defs

set_option autoImplicit false

lemma gw3fd_quad {n : ℕ} (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hpsd : Sig.PosSemidef) (i j : Fin n) (hij : i ≠ j) (s : ℝ) :
    0 ≤ Sig i i + s * Sig i j + s * Sig j i + s * s * Sig j j := by
  have h := hpsd.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j s)
  simp [Pi.single_apply, hij, hij.symm, Matrix.mulVec, mul_comm, mul_left_comm, mul_assoc,
    add_assoc] at h
  linarith

open ConvexOptAlg.GoemansWilliamson in
theorem solution {n : ℕ} (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hpsd : Sig.PosSemidef) (hdiag : ∀ i, Sig i i = 1) (i j : Fin n) :
    |Sig i j| ≤ 1 := by
  by_cases hij : i = j
  · subst hij; rw [hdiag]; simp
  have hsym : Sig j i = Sig i j := by
    have := hpsd.isHermitian.apply i j
    simpa using this
  have h1 := gw3fd_quad Sig hpsd i j hij 1
  have h2 := gw3fd_quad Sig hpsd i j hij (-1)
  rw [hdiag, hdiag, hsym] at h1 h2
  rw [abs_le]; constructor <;> nlinarith
