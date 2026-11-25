-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.divSq_lcm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:53:50.17357+00:00
-- url     : https://prove2.me/submissions/aaf2a109-09b1-44da-b050-2d2cc31de341

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZMoll
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensDiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution {a b : ℕ} (ha : 1 ≤ a) :
    Nat.lcm a b = Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b) := by
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have h1 : Nat.gcd a b * (a / Nat.gcd a b) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have h2 : Nat.gcd a b * (b / Nat.gcd a b) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  apply Nat.eq_of_mul_eq_mul_left hg
  calc Nat.gcd a b * Nat.lcm a b = a * b := Nat.gcd_mul_lcm a b
    _ = (Nat.gcd a b * (a / Nat.gcd a b)) * (Nat.gcd a b * (b / Nat.gcd a b)) := by rw [h1, h2]
    _ = Nat.gcd a b * (Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b)) := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
