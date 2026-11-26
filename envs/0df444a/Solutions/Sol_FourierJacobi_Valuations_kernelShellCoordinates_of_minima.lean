-- Prove2me | solution 1 for FourierJacobi.Valuations.kernelShellCoordinates_of_minima
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:12.87637+00:00
-- url     : https://prove2.me/submissions/93579104-a531-46f7-8852-7a5a796d2646

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Valuations_KernelShells
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_kernel_half_ell
import Theorems.Thm_FourierJacobi_Valuations_kernel_height_eq
import Theorems.Thm_FourierJacobi_Valuations_kernel_indices_of_minima
attribute [local simp] FourierJacobi.Valuations.actualEntryInteger_coe
attribute [local simp] FourierJacobi.Valuations.actualMinorInteger_coe



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Valuations
open FourierJacobi.LocalMatrix
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Valuations
theorem _root_.solution (p : KernelPoint K) (r k j h c : ℤ)
    (he : matrixMinimum (localFieldValuation K) (g p.1 p.2.1 p.2.2.1 p.2.2.2) =
      (entryMinimum r k j h : WithTop ℤ))
    (hm : matrixMinimum (localFieldValuation K)
      (secondCompound (g p.1 p.2.1 p.2.2.1 p.2.2.2)) =
        (minorMinimum r k j h c : WithTop ℤ)) :
    KernelShellCoordinates K p r k j h c := by
  have he' : kernelEntryIndex K p = entryMinimum r k j h := by
    apply WithTop.coe_injective
    exact (actualEntryInteger_coe _ _ _ _ _).trans he
  have hm' : kernelMinorIndex K p = minorMinimum r k j h c := by
    apply WithTop.coe_injective
    exact (actualMinorInteger_coe _ _ _ _ _).trans hm
  have hcartan := kernel_indices_of_minima K p r k j h c he hm
  have hell : kernelEll K p = (cartanIndices r k j h c).1 := congrArg Prod.fst hcartan
  have hb : kernelB K p = (cartanIndices r k j h c).2 := congrArg Prod.snd hcartan
  have hn : kernelN K p = (cartanIndices r k j h c).1 / 2 := by
    rw [← hell, kernel_half_ell]
  refine ⟨he', hm', hell, hn, hb, ?_, ?_⟩
  · unfold kernelHeight
    rw [hn, hb]
  · rw [kernel_height_eq, he']
end FourierJacobi.Valuations
