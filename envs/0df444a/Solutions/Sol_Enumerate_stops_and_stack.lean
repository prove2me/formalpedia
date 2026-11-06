-- Prove2me | solution 1 for Enumerate.stops_and_stack
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:44:10.411702+00:00
-- url     : https://prove2.me/submissions/be2db95d-233e-48f5-92d7-4c066e8b23d9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Enumerate_Defs
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_SparsificationLemma_Geo_Thr
import Definitions.Def_SparsificationLemma_Geo_Tau
import Definitions.Def_SparsificationLemma_Geo_Eps
import Definitions.Def_UniformInK_Spars_Thresholds
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_Enumerate_Enumeration
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_SparsificationLemma_Geo_stThrGeo
import Theorems.Thm_SparsificationLemma_stCountOfExactlyOne
import Theorems.Thm_SparsificationLemma_stExactlyOne
import Theorems.Thm_SparsificationLemma_stOutputsSame
import Theorems.Thm_SparsificationLemma_stTreeG
import Theorems.Thm_UniformInK_stBetaSumU
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Enumerate
open Finset Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma SparsificationLemma.Geo
namespace Enumerate
theorem _root_.solution {τ : ℕ} (hτ : 24 ≤ τ) (n : ℕ) (φ : PFml) (hφ : IsKCNF 3 n φ) :
    (∀ x ∈ leaves (rule τ) (depth τ n) (start n φ), rule τ x = none) ∧
    ∀ i, ((Sparsify.round (rule τ))^[i] ([start n φ], [])).1.length ≤ depth τ n + 1 ∧
      ∀ x ∈ ((Sparsify.round (rule τ))^[i] ([start n φ], [])).1,
        x.1.length ≤ φ.length * 2 ^ 3 ∧ x.2.length ≤ 2 * n ∧ (∀ C ∈ x.1, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n := by
  obtain ⟨-, c2, -, c4⟩ := stTreeG stExactlyOne stCountOfExactlyOne stOutputsSame 3 τ n (bsumU τ 3 * n) (thetaU τ) (betaSU τ) (by norm_num) (by omega)
    (stThrGeo 3 τ (by norm_num) (by omega)) (Nat.mul_le_mul_right _ (stBetaSumU τ 3 (by omega))) φ hφ
  exact ⟨fun x hx => (c2 x hx).1, c4⟩
end Enumerate
