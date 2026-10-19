-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.genX_genY2_commute
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:40:15.27713+00:00
-- url     : https://prove2.me/submissions/d4f2bce8-33f6-4c7f-83f6-afd5a56161f4

import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
-- Generated from ChapterNavierStokesGaugeY2.lean — theorem BookProof.NavierStokesGaugeY2.genX_genY2_commute
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY2



open MvPolynomial BookProof.NavierStokesGaugeY
noncomputable def h43_DY2 (k : Fin 3) : Derivation ℂ NSAlg NSAlg :=
  MvPolynomial.pderiv (NSVar.y k)
    - ((MvPolynomial.X (NSVar.uD 0 k) : NSAlg) • MvPolynomial.pderiv (NSVar.u 0)
      + (MvPolynomial.X (NSVar.uD 1 k) : NSAlg) • MvPolynomial.pderiv (NSVar.u 1)
      + (MvPolynomial.X (NSVar.uD 2 k) : NSAlg) • MvPolynomial.pderiv (NSVar.u 2))
    - ((MvPolynomial.X (NSVar.uL 0) : NSAlg) • MvPolynomial.pderiv (NSVar.uD 0 k)
      + (MvPolynomial.X (NSVar.uL 1) : NSAlg) • MvPolynomial.pderiv (NSVar.uD 1 k)
      + (MvPolynomial.X (NSVar.uL 2) : NSAlg) • MvPolynomial.pderiv (NSVar.uD 2 k))

theorem h43_DY2_eq (k : Fin 3) : (h43_DY2 k : Module.End ℂ NSAlg) = genY2 k := by
  apply LinearMap.ext; intro p
  simp [h43_DY2, genY2, Fin.sum_univ_three, Derivation.sub_apply, smul_eq_mul]

theorem h43_v_x (k a : Fin 3) : h43_DY2 k (X (NSVar.x a)) = 0 := by
  simp [h43_DY2, pderiv_X, Pi.single_apply]
theorem h43_v_y (k a : Fin 3) : h43_DY2 k (X (NSVar.y a)) = if a = k then 1 else 0 := by
  simp [h43_DY2, pderiv_X, Pi.single_apply]
theorem h43_v_u (k a : Fin 3) : h43_DY2 k (X (NSVar.u a)) = -X (NSVar.uD a k) := by
  fin_cases a <;> simp [h43_DY2, pderiv_X, Pi.single_apply]
theorem h43_v_uD (k a b : Fin 3) :
    h43_DY2 k (X (NSVar.uD a b)) = if b = k then -X (NSVar.uL a) else 0 := by
  by_cases hb : b = k
  · subst hb; fin_cases a <;> simp [h43_DY2, pderiv_X, Pi.single_apply]
  · simp [h43_DY2, pderiv_X, Pi.single_apply, hb]
theorem h43_v_uL (k a : Fin 3) : h43_DY2 k (X (NSVar.uL a)) = 0 := by
  simp [h43_DY2, pderiv_X, Pi.single_apply]
theorem h43_v_const (k : Fin 3) (c : Prop) [Decidable c] :
    h43_DY2 k (if c then (1 : NSAlg) else 0) = 0 := by
  split_ifs <;> simp

theorem h43_Y2Y2 (j k : Fin 3) : ⁅genY2 j, genY2 k⁆ = 0 := by
  rw [← h43_DY2_eq, ← h43_DY2_eq, ← Derivation.commutator_coe_linear_map]
  have : ⁅h43_DY2 j, h43_DY2 k⁆ = 0 := by
    apply MvPolynomial.derivation_ext; intro v
    rw [Derivation.commutator_apply]
    cases v with
    | x a => simp only [h43_v_x, map_zero, sub_zero]; rfl
    | y a => rw [h43_v_y, h43_v_y, h43_v_const, h43_v_const, sub_zero]; rfl
    | u a =>
      rw [h43_v_u, h43_v_u, map_neg, map_neg, h43_v_uD, h43_v_uD]
      by_cases h : j = k
      · subst h; simp
      · rw [if_neg h, if_neg (Ne.symm h)]; simp
    | uD a b =>
      rw [h43_v_uD, h43_v_uD]
      split_ifs <;> simp [h43_v_uL]
    | uL a => simp only [h43_v_uL, map_zero, sub_zero]; rfl
  rw [this]; rfl

theorem solution (j k : Fin 3) : ⁅genX j, genY2 k⁆ = 0 := by
  rw [← h43_DY2_eq, show genX j = ((pderiv (NSVar.x j) : Derivation ℂ NSAlg NSAlg) : Module.End ℂ NSAlg) from rfl,
    ← Derivation.commutator_coe_linear_map]
  have : ⁅(pderiv (NSVar.x j) : Derivation ℂ NSAlg NSAlg), h43_DY2 k⁆ = 0 := by
    apply MvPolynomial.derivation_ext; intro v
    rw [Derivation.commutator_apply]
    cases v <;> simp [h43_DY2, pderiv_X, Pi.single_apply, smul_eq_mul] <;> split_ifs <;>
      simp [pderiv_X, Pi.single_apply]
  rw [this]; rfl

