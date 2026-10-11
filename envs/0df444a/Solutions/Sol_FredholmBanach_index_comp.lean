-- Prove2me | solution 1 for FredholmBanach.index_comp
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T18:47:24.014467+00:00
-- url     : https://prove2.me/submissions/ea54319d-918b-49f4-9225-8e2bfdc5ff68

import Definitions.Def_FredholmBanach_Setting
import Mathlib.Algebra.Module.LinearMap.Index

open Topology

theorem solution {𝕜 E F G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
    {u : E →L[𝕜] F} {v : F →L[𝕜] G} (hu : u.IsFredholm) (hv : v.IsFredholm) :
    FredholmBanach.index (v.comp u) = FredholmBanach.index v + FredholmBanach.index u := by
  haveI : FiniteDimensional 𝕜 (LinearMap.ker (u : E →ₗ[𝕜] F)) := hu.finite_ker
  haveI : FiniteDimensional 𝕜 (LinearMap.ker (v : F →ₗ[𝕜] G)) := hv.finite_ker
  haveI : FiniteDimensional 𝕜 (F ⧸ LinearMap.range (u : E →ₗ[𝕜] F)) := hu.finite_coker
  haveI : FiniteDimensional 𝕜 (G ⧸ LinearMap.range (v : F →ₗ[𝕜] G)) := hv.finite_coker
  -- the Banach-space index is, by definition, the algebraic index of the underlying linear map
  exact LinearMap.index_comp (f := (u : E →ₗ[𝕜] F)) (v : F →ₗ[𝕜] G)
