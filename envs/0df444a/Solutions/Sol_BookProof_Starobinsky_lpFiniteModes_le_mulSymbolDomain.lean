-- Prove2me | solution 1 for BookProof.Starobinsky.lpFiniteModes_le_mulSymbolDomain
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:11:03.579303+00:00
-- url     : https://prove2.me/submissions/c1434fff-f2d0-4a34-a5e6-279b307b82b1

-- Generated from ChapterStarobinskyPotential.lean — solution of BookProof.Starobinsky.lpFiniteModes_le_mulSymbolDomain
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.Starobinsky












open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow
open BookProof.QuantumGravityDensitized BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℕ → ℝ) :
    (lpFiniteModes ℕ : Submodule ℂ L2Nat) ≤ mulSymbolDomain lam := by

  intro f hf
  have hsupp : (Function.support (mulSymbolFun lam ((f : L2Nat) : ℕ → ℂ))).Finite := by
    refine Set.Finite.subset hf (fun n hn => ?_)
    simp only [Function.mem_support, mulSymbolFun, ne_eq, mul_eq_zero, not_or] at hn
    exact hn.2
  classical
  change Memℓp (mulSymbolFun lam ((f : L2Nat) : ℕ → ℂ)) 2
  refine (memℓp_gen_iff (by norm_num)).2 ?_
  refine summable_of_ne_finset_zero (s := hsupp.toFinset) fun n hn => ?_
  have : mulSymbolFun lam ((f : L2Nat) : ℕ → ℂ) n = 0 := by
    by_contra hc
    exact hn (hsupp.mem_toFinset.2 hc)
  simp [this]
