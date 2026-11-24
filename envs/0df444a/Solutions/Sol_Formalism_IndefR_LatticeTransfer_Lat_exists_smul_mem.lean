-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.Lat.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:59.263539+00:00
-- url     : https://prove2.me/submissions/a56f64f0-d9be-4383-895d-39424fa7e01b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_MemSpanOfSmulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer Formalism.IndefR.LatticeTransfer.Lat
open Formalism.IndefR.TransferLatticeStatement Formalism.HN Formalism.IndefR.LatticeTransfer
variable {K : Type} [Field K] [NumberField K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.IndefR.LatticeTransfer.Lat
theorem _root_.solution {A : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Submodule.span K (A : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ A := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K
    (A : Set V) x hx
  refine ⟨t, nonZeroDivisors.coe_ne_zero t, ?_⟩
  rw [Submodule.span_eq] at ht
  exact ht
end Formalism.IndefR.LatticeTransfer.Lat
