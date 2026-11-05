-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertNum.numP_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:29:14.064199+00:00
-- url     : https://prove2.me/submissions/5ef09b89-ce38-473e-a120-01d06f6a9738

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_min_right
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_map_range_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_powZ_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_unary_min_right
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertNum
open Groundwork PaddedDescent.F ClauseBound.Alg.CertGridG ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertNum
theorem _root_.solution {nb i₀ : α → ℕ} {A : α → ℤ} {B : α → ℕ → ℤ} (hnb : Unary nb) (hi : Unary i₀) (hA : PolyT A) (hB : PolyT fun p : α × ℕ => B p.1 p.2) :
    PolyT fun x => A x * (nb x : ℤ) ^ i₀ x + ((List.range (i₀ x + 1)).map fun i => (-2 : ℤ) ^ i * (nb x : ℤ) ^ (i₀ x - i) * B x i).sum := by
  have hn1 : Unary fun x => i₀ x + 1 := hi.add (Unary.const 1)
  have hmin : Unary fun p : α × ℕ => min p.2 (i₀ p.1 + 1) := CertLib.unary_min_right PolyT.id'.snd (hn1.comp PolyT.id'.fst)
  have hB' : PolyT fun p : α × ℕ => B p.1 (min p.2 (i₀ p.1 + 1)) :=
    PolyT.comp (g := fun p : α × ℕ => (p.1, min p.2 (i₀ p.1 + 1))) hB (PolyT.prodMk PolyT.id'.fst hmin.poly)
  have hnbZ : PolyT fun p : α × ℕ => (nb p.1 : ℤ) := PolyT.natCast (PolyT.comp hnb.poly PolyT.id'.fst)
  have h1 : PolyT fun p : α × ℕ => (-2 : ℤ) ^ min p.2 (i₀ p.1 + 1) * (nb p.1 : ℤ) ^ (i₀ p.1 - min p.2 (i₀ p.1 + 1)) * B p.1 (min p.2 (i₀ p.1 + 1)) :=
    PolyT.mulZ (PolyT.mulZ (powZ_polyT (PolyT.const (-2)) hmin) (powZ_polyT hnbZ (unary_sub (hi.comp PolyT.id'.fst) hmin.poly))) hB'
  have h2 : PolyT fun x => (List.range (i₀ x + 1)).map fun i => (-2 : ℤ) ^ i * (nb x : ℤ) ^ (i₀ x - i) * B x i :=
    map_range_polyT (f := fun x i => (-2 : ℤ) ^ i * (nb x : ℤ) ^ (i₀ x - i) * B x i) hn1 h1
  exact PolyT.addZ (PolyT.mulZ hA (powZ_polyT (PolyT.natCast hnb.poly) hi)) (sumZ_polyT h2)
end ClauseBound.ParityChecks.CertNum
