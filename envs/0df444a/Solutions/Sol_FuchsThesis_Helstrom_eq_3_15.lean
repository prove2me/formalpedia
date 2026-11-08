-- Prove2me | solution 1 for FuchsThesis.Helstrom.eq_3_15
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:19:46.313123+00:00
-- url     : https://prove2.me/submissions/e6dbd489-1533-4d74-ae3a-a630944119b1

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_FuchsThesis_Helstrom_binaryError
import Definitions.Def_FuchsThesis_Helstrom_gammaOp

open scoped ComplexOrder

open FuchsThesis.Helstrom in
theorem solution {n : Type} [Fintype n] [DecidableEq n] (π0 π1 : ℝ) (hπ0 : 0 ≤ π0)
    (hπ1 : 0 ≤ π1) (hπ : π0 + π1 = 1) (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1)
    (E : Fin 2 → Matrix n n ℂ) (hE : FuchsVdGraaf.IsPOVM E) :
    binaryError π0 π1 ρ0 ρ1 E = π0 + (Matrix.trace (gammaOp π0 π1 ρ0 ρ1 * E 0)).re := by
  have hs := hE.2
  rw [Fin.sum_univ_two] at hs
  have hE1 : E 1 = 1 - E 0 := eq_sub_of_add_eq' hs
  unfold binaryError gammaOp FuchsVdGraaf.outcomeDist
  rw [hE1, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, h0.2, Matrix.sub_mul,
    Matrix.trace_sub, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_smul]
  simp only [Complex.sub_re, Complex.one_re, smul_eq_mul, Complex.re_ofReal_mul]
  ring
