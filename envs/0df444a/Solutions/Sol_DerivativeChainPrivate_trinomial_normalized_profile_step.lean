-- Prove2me | solution 1 for DerivativeChainPrivate.trinomial_normalized_profile_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-19T05:07:21.344984+00:00
-- url     : https://prove2.me/submissions/5077022b-e995-4056-89e2-69dbbcd5ecce

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial















end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate









end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution (x d e : ℝ)
    (hd : 0 < d) (hde : d ≤ e) (hex : e < x) :
    1 ≤ (1 - d / x) ^ (e / d) / (1 - e / x) := by
  have hx : 0 < x := lt_of_lt_of_le hd (hde.trans hex.le)
  have hdx : d / x ≤ 1 := (div_le_one hx).mpr (hde.trans hex.le)
  have hed : 1 ≤ e / d := (one_le_div hd).mpr hde
  have hden : 0 < 1 - e / x := sub_pos.mpr ((div_lt_one hx).mpr hex)
  have hb := one_add_mul_self_le_rpow_one_add
    (s := -(d / x)) (p := e / d) (by linarith) hed
  have heq : 1 + e / d * -(d / x) = 1 - e / x := by
    field_simp
    ring
  rw [heq, show 1 + -(d / x) = 1 - d / x by ring] at hb
  exact (one_le_div hden).mpr hb
