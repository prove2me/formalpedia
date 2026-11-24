-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.Lat.mem_span_of_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:59.206009+00:00
-- url     : https://prove2.me/submissions/161ba5fe-577a-4638-afb0-483a4281fbff

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
theorem _root_.solution {A : Submodule (𝓞 K) V} {x : V} {d : 𝓞 K} (hd : d ≠ 0)
    (hx : d • x ∈ A) : x ∈ Submodule.span K (A : Set V) := by
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd
  have h1 : x = (d : K)⁻¹ • (d • x) := by
    rw [← IsScalarTower.algebraMap_smul K d x, smul_smul]
    simp [hdK]
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hx)
end Formalism.IndefR.LatticeTransfer.Lat
