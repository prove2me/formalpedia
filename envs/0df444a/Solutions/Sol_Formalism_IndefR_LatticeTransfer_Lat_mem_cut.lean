-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.Lat.mem_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:33:27.975962+00:00
-- url     : https://prove2.me/submissions/fde191e3-c95d-455e-b496-6b9369f3f346

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
theorem _root_.solution {A : Submodule (𝓞 K) V} {p : V →ₗ[K] V} (hp : ∀ a, p (p a) = p a) {a : V} :
    a ∈ cut A p ↔ a ∈ A ∧ p a = a := by
  unfold cut
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, LinearMap.mem_range]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨a, h⟩⟩
  rintro ⟨z, rfl⟩
  exact hp z
end Formalism.IndefR.LatticeTransfer.Lat
