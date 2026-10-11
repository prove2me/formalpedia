-- Prove2me | solution 1 for FredholmBanach.isFredholm_iff_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T18:12:58.325+00:00
-- url     : https://prove2.me/submissions/c6ad0994-6bad-4a2f-bfeb-a7a981b2f6d1

import Definitions.Def_FredholmBanach_Setting
import Theorems.Thm_FredholmBanach_isClosed_range_of_finiteDimensional_coker
import Mathlib.Analysis.LocallyConvex.HahnBanach

open Topology

theorem solution {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (u : E →L[𝕜] F) :
    u.IsFredholm ↔ FiniteDimensional 𝕜 u.ker ∧ FiniteDimensional 𝕜 (F ⧸ u.range) := by
  refine ⟨fun h => ⟨h.finite_ker, h.finite_coker⟩, fun ⟨hk, hc⟩ => ?_⟩
  obtain ⟨hcl, hst⟩ := FredholmBanach.isClosed_range_of_finiteDimensional_coker u hc
  exact
    { isStrictMap := hst
      isClosed_range := hcl
      finite_ker := hk
      finite_coker := hc
      closedComplemented_ker := Submodule.ClosedComplemented.of_finiteDimensional _ }
