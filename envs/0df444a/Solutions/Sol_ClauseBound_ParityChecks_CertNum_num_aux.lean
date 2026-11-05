-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertNum.num_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:29:08.330748+00:00
-- url     : https://prove2.me/submissions/925f921a-2494-490c-96fa-ca2b5dc2cef5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_powZ_polyT
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_poly
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.mul



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertNum
open Groundwork PaddedDescent.F ClauseBound.Alg.CertGridG ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertNum
theorem _root_.solution {m nb r i₀ j nI nR nC : α → ℕ} {nP : α → ℤ} (hm : Unary m) (hnb : Unary nb) (hr : Unary r) (hi : Unary i₀) (hj : PolyT j) (hP : PolyT nP)
    (hI : PolyT nI) (hR : PolyT nR) (hC : PolyT nC) :
    PolyT fun x => (5 : ℤ) ^ (r x - 1 - j x) * nP x * ((8 * m x * r x * (nb x + 1) ^ (m x + r x) : ℕ) : ℤ) +
      ((nI x * (2 * 8 ^ (r x - 1 - j x) * nb x ^ i₀ x * (nb x + 1) ^ (m x + r x)) +
        nR x * (2 * 8 ^ (r x - 1 - j x) * nb x ^ i₀ x * m x * (nb x + 1) ^ r x) +
        nC x * (2 * 8 ^ (r x - 1 - j x) * nb x ^ i₀ x * r x * (nb x + 1) ^ m x) : ℕ) : ℤ) := by
  have hk : Unary fun x => r x - 1 - j x := unary_sub (unary_sub hr (PolyT.const 1)) hj
  have hn1 : PolyT fun x => nb x + 1 := PolyT.add hnb.poly (PolyT.const 1)
  have h5 : PolyT fun x => (5 : ℤ) ^ (r x - 1 - j x) := powZ_polyT (PolyT.const 5) hk
  have h8 : PolyT fun x => 8 ^ (r x - 1 - j x) := PolyT.pow_unary (PolyT.const 8) hk
  have hni : PolyT fun x => nb x ^ i₀ x := PolyT.pow_unary hnb.poly hi
  have hmr : PolyT fun x => (nb x + 1) ^ (m x + r x) := PolyT.pow_unary hn1 (hm.add hr)
  have hnr : PolyT fun x => (nb x + 1) ^ r x := PolyT.pow_unary hn1 hr
  have hnm : PolyT fun x => (nb x + 1) ^ m x := PolyT.pow_unary hn1 hm
  have c0 : PolyT fun x => 2 * 8 ^ (r x - 1 - j x) * nb x ^ i₀ x := PolyT.mul (PolyT.mul (PolyT.const 2) h8) hni
  have a1 : PolyT fun x => 8 * m x * r x * (nb x + 1) ^ (m x + r x) := PolyT.mul (PolyT.mul (PolyT.mul (PolyT.const 8) hm.poly) hr.poly) hmr
  have a2 : PolyT fun x => nI x * (2 * 8 ^ (r x - 1 - j x) * nb x ^ i₀ x * (nb x + 1) ^ (m x + r x)) +
        nR x * (2 * 8 ^ (r x - 1 - j x) * nb x ^ i₀ x * m x * (nb x + 1) ^ r x) +
        nC x * (2 * 8 ^ (r x - 1 - j x) * nb x ^ i₀ x * r x * (nb x + 1) ^ m x) :=
    PolyT.add (PolyT.add (PolyT.mul hI (PolyT.mul c0 hmr)) (PolyT.mul hR (PolyT.mul (PolyT.mul c0 hm.poly) hnr)))
      (PolyT.mul hC (PolyT.mul (PolyT.mul c0 hr.poly) hnm))
  exact PolyT.addZ (PolyT.mulZ (PolyT.mulZ h5 hP) (PolyT.natCast a1)) (PolyT.natCast a2)
end ClauseBound.ParityChecks.CertNum
