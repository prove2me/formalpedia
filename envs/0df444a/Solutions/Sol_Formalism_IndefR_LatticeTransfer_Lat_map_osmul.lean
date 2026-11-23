-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.Lat.map_osmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:58.834822+00:00
-- url     : https://prove2.me/submissions/c501b9ca-66d0-4e82-8ed5-357377b99101

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
omit [NumberField K]
namespace Formalism.IndefR.LatticeTransfer.Lat
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (p : V →ₗ[K] W) (d : 𝓞 K) (a : V) : p (d • a) = d • p a := by
  rw [← IsScalarTower.algebraMap_smul K d a, map_smul, IsScalarTower.algebraMap_smul]
end Formalism.IndefR.LatticeTransfer.Lat
