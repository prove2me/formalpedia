-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.overlattice_count_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:23.161118+00:00
-- url     : https://prove2.me/submissions/fca18283-f4e3-4796-8c35-d743074a213f

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : OverlatticeCount := by
  intro O A _ _ _ _ m h
  have hs : Function.Surjective (fun s : Fin m → A => Submodule.span O (Set.range s)) := fun N => h N
  calc Nat.card (Submodule O A) ≤ Nat.card (Fin m → A) := Nat.card_le_card_of_surjective _ hs
    _ = _ := by rw [Nat.card_fun]; simp
end Formalism.HermitianLatticeCounting.P.S4aux
