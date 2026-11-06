-- Prove2me | solution 1 for FixedWidthSteps.sentenceFromTheSteps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:18:37.349009+00:00
-- url     : https://prove2.me/submissions/78ca6723-fb97-4aad-8a88-b6e84c64bc11

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_RouteDefs
import Definitions.Def_FixedWidthSteps_Sentence
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open FixedWidthSteps
open Turing Groundwork ClauseBound.Alg MainTheoremForms TwoMachines PairsToBound FixedWidth
namespace FixedWidthSteps
theorem _root_.solution : SentenceFromTheSteps := by
  intro hVariablesA hHyp hRate hChoose hFront hEx hEvery ρ c x₀ hPieces hx hc hProv
  obtain ⟨P, A, val, hP⟩ := hPieces
  obtain ⟨num, hnum, hb⟩ := hProv
  obtain ⟨C₀, h⟩ := hHyp c
  obtain ⟨Q, hpoly, hK, -, hNB⟩ := h ρ x₀ P A val hP hx hc
  obtain ⟨M, C', hMfin, hM⟩ := hVariablesA _ _ _ _ Q hpoly num (hNB num hnum hb)
  obtain ⟨Mb, cb, -, hMbfin, hMb, -⟩ := hEx
  obtain ⟨⟨pre, hprePoly, hpre⟩, hT⟩ := hFront
  obtain ⟨test, htestPoly, htest⟩ := hT ((solverOf (GeneralPieces.Tied.recOf P val c)).K (Q.idx 0))
  obtain ⟨_, _, N, _, q, hNfin, _, hN⟩ := hChoose M Mb hMfin hMbfin test pre id id id htestPoly hprePoly PolyT.id' PolyT.id' PolyT.id'
  have hρ0 : 0 < ρ := by have := hP.rho_ge; linarith
  have hα : 0 < AppRunningTime.alpha' ρ := Real.logb_pos one_lt_two (by rw [lt_div_iff₀ hρ0]; linarith [hP.rho_lt])
  exact ⟨N, hNfin, fun k hk => hEvery _ _ _ _ Q (AppRunningTime.alpha' ρ) (3 * x₀ + 6) hα (fun l => by rw [hK l]; exact hRate ρ x₀ l hP.rho_ge hP.rho_lt hx)
    M C' hM Mb cb hMb pre test hpre htest N q hN k hk⟩
end FixedWidthSteps
