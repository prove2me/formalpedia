-- Prove2me | solution 1 for BSPConvex.CMM.lifted_set_convex
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:48:58.430572+00:00
-- url     : https://prove2.me/submissions/f9ff6440-55e1-497e-b2c3-713871a6972d

import Mathlib
import Definitions.Def_BSPConvex_CMM_Model
import Theorems.Thm_BSPConvex_CMM_lemma_6

open Matrix
open scoped MatrixOrder

open BSPConvex.CMM in
theorem BSPCMMAuxC.simplex_convex (m : ℕ) : Convex ℝ (simplex m) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    nlinarith [hx.2, hy.2, mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]

open BSPConvex.CMM in
theorem solution {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosSemidef) :
    Convex ℝ {p : (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ |
      (CFC.sqrt (Tmat Sig p.1) - p.2).PosSemidef ∧ p.1 ∈ simplex m} := by
  intro p hp p' hp' a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  obtain ⟨h1, hx⟩ := hp
  obtain ⟨h2, hy⟩ := hp'
  refine ⟨?_, BSPCMMAuxC.simplex_convex m hx hy ha hb (by ring)⟩
  have hL := lemma_6 Sig hSig p.1 p'.1 hx hy a ⟨ha, by linarith⟩
  have hsum := (hL.add (h1.smul ha)).add (h2.smul hb)
  convert hsum using 1
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  module
