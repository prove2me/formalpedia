-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.Lat.rkK_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:49.086499+00:00
-- url     : https://prove2.me/submissions/1e7b95bc-8f15-4ea1-ade5-e929991697b2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_MemSpanOfSmulMem
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_span_cut

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
theorem _root_.solution {A : Submodule (𝓞 K) V} (hA : Submodule.span K (A : Set V) = ⊤)
    (p : V →ₗ[K] V) : rkK (cut A p) = finrank K (LinearMap.range p) := by
  unfold rkK
  rw [span_cut hA]
end Formalism.IndefR.LatticeTransfer.Lat
