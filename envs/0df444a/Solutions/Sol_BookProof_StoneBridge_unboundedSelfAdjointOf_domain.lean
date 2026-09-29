-- Prove2me | solution 1 for BookProof.StoneBridge.unboundedSelfAdjointOf_domain
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:11:09.780029+00:00
-- url     : https://prove2.me/submissions/3b278fc2-db29-4f47-945c-85b4e5af1b69

-- Generated from ChapterStoneBridge.lean — solution of BookProof.StoneBridge.unboundedSelfAdjointOf_domain
import Mathlib
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.StoneBridge







open Filter Topology
open scoped InnerProductSpace


open BookProof.FarisLavine BookProof.EsaClosure BookProof.YangMillsFriedrichs
open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (hdense : Dense ((D : Submodule ℂ F) : Set F))
    (h : IsSelfAdjointExtension Hc A) :
    (unboundedSelfAdjointOf hdense h).domain = Dom := rfl
