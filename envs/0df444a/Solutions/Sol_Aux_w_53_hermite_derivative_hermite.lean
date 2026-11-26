-- Prove2me | solution 1 for Aux_w_53_hermite.derivative_hermite
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:38:21.281914+00:00
-- url     : https://prove2.me/submissions/83a7232e-0da6-4c35-bf67-2912e4e13f9d

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Mathlib
set_option autoImplicit false
namespace Aux_w_53_hermite
end Aux_w_53_hermite
open Aux_w_53_hermite
open MeasureTheory Filter Polynomial QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped Real Topology Nat ENNReal
theorem solution (j : ℕ) :
    Polynomial.derivative (Polynomial.hermite (j + 1)) = C ((j + 1 : ℕ) : ℤ) * Polynomial.hermite j := by
  induction j with
  | zero =>
    rw [Polynomial.hermite_one, Polynomial.hermite_zero]
    simp
  | succ j ih =>
    rw [Polynomial.hermite_succ (j + 1), Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_X, one_mul, ih, Polynomial.derivative_C_mul]
    have hmul : Polynomial.X * (C ((j + 1 : ℕ) : ℤ) * Polynomial.hermite j) -
        C ((j + 1 : ℕ) : ℤ) * Polynomial.derivative (Polynomial.hermite j) =
        C ((j + 1 : ℕ) : ℤ) * (Polynomial.X * Polynomial.hermite j -
          Polynomial.derivative (Polynomial.hermite j)) := by ring
    rw [← Polynomial.hermite_succ j] at hmul
    calc
      Polynomial.hermite (j + 1) + Polynomial.X * (C ((j + 1 : ℕ) : ℤ) * Polynomial.hermite j) -
          C ((j + 1 : ℕ) : ℤ) * Polynomial.derivative (Polynomial.hermite j)
          = Polynomial.hermite (j + 1) + (Polynomial.X * (C ((j + 1 : ℕ) : ℤ) * Polynomial.hermite j) -
              C ((j + 1 : ℕ) : ℤ) * Polynomial.derivative (Polynomial.hermite j)) := by ring
      _ = Polynomial.hermite (j + 1) + C ((j + 1 : ℕ) : ℤ) * Polynomial.hermite (j + 1) := by rw [hmul]
      _ = C (((j + 1 + 1 : ℕ) : ℤ)) * Polynomial.hermite (j + 1) := by
        have hC : C (((j + 1 + 1 : ℕ) : ℤ)) = 1 + C ((j + 1 : ℕ) : ℤ) := by
          push_cast; simp [map_add, map_one]; ring
        rw [hC]; ring
