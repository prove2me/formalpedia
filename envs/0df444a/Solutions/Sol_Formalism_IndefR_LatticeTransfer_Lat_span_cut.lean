-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.Lat.span_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:47.717602+00:00
-- url     : https://prove2.me/submissions/dd8230ac-5803-484d-af08-b0efeb7c101a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_MemSpanOfSmulMem
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_exists_smul_mem
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_mem_span_of_smul_mem

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
    (p : V →ₗ[K] V) : Submodule.span K (cut A p : Set V) = LinearMap.range p := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro a ha
    exact ha.2
  · intro u hu
    obtain ⟨d, hd, hdu⟩ := exists_smul_mem (A := A) (x := u) (by rw [hA]; trivial)
    refine mem_span_of_smul_mem hd ⟨hdu, ?_⟩
    have : d • u = (d : K) • u := (IsScalarTower.algebraMap_smul K d u).symm
    change d • u ∈ LinearMap.range p
    rw [this]
    exact Submodule.smul_mem _ _ hu
end Formalism.IndefR.LatticeTransfer.Lat
