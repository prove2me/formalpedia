-- Prove2me | solution 1 for Enumerate.stEnumeratesTau
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:54:09.2822+00:00
-- url     : https://prove2.me/submissions/f1aa9235-91f0-49dc-b12f-e8b21e8e6907

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
import Theorems.Thm_Enumerate_stProducedIsList
import Theorems.Thm_Enumerate_out_polyT
import Theorems.Thm_Enumerate_stops_and_stack
import Theorems.Thm_Enumerate_sat_iff_of_exactlyOne
import Theorems.Thm_CountKSat_Poly_certStepC
import Theorems.Thm_Groundwork_Stepped_length_visits
import Theorems.Thm_SparsificationLemma_Geo_stThmTau
import Theorems.Thm_SparsificationLemma_stLenOfOcc


set_option autoImplicit false
section
section
open Enumerate
open Finset Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma SparsificationLemma.Geo
namespace Enumerate
theorem _root_.solution : StEnumeratesTau := by
  intro τ ε hτ hε
  have hε' : (((3 : ℕ) : ℝ) / (τ : ℝ)) * Real.logb 2 (Real.exp 1 * (τ : ℝ) * (bsumU τ 3 : ℝ)) ≤ ε := by rw [Nat.cast_ofNat]; exact hε
  have hT := fun (n : ℕ) (φ : PFml) (hφ : IsKCNF 3 n φ) => stThmTau 3 n τ ε φ (by norm_num) (by omega) hε' hφ
  refine ⟨fun n φ hφ => (stops_and_stack hτ n φ hφ).1, fun n φ hφ => ?_, fun n φ hφ Φ hΦ => ?_, fun n φ hφ => ?_, fun n φ => ?_,
    Poly.certStepC (thetaU τ) 3, out_polyT, fun n φ hφ => (stops_and_stack hτ n φ hφ).2⟩
  · rw [stProducedIsList]
    exact (hT n φ hφ).2.2.1
  · rw [stProducedIsList] at hΦ
    obtain ⟨-, t2, -, -, t5⟩ := hT n φ hφ
    exact ⟨(t2 Φ hΦ).1, (t2 Φ hΦ).2, stLenOfOcc 3 n (τ ^ 6) Φ (t2 Φ hΦ).1 (t5 Φ hΦ)⟩
  · rw [stProducedIsList]
    exact sat_iff_of_exactlyOne (hT n φ hφ).2.2.2.1
  · rw [produced, List.length_map]
    exact length_visits (rule τ) (depth τ n) (start n φ) []
end Enumerate
