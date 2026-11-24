-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.herm_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:31.198356+00:00
-- url     : https://prove2.me/submissions/99df3d88-ef18-40ee-87df-317842a2a960

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
theorem _root_.solution {E : Type} [CommRing E] [StarRing E] (O : Subring E)
    (htr : ∀ c ∈ O, star c = c → ∃ s ∈ O, s + star s = c) (r : ℕ) (γ : Fin r → Fin r → E)
    (hO : ∀ j k, γ j k ∈ O) (hγ : ∀ j k, star (γ j k) = γ k j) :
    ∃ c : Fin r → Fin r → E, (∀ j k, c j k ∈ O) ∧ ∀ j k, c j k + star (c k j) = γ j k := by
  have hdiag : ∀ j, ∃ s ∈ O, s + star s = γ j j := fun j => htr _ (hO j j) (hγ j j)
  choose s hs hss using hdiag
  refine ⟨fun j l => if j < l then γ j l else if j = l then s j else 0, fun j l => ?_, fun j k => ?_⟩
  · dsimp only
    split_ifs
    exacts [hO j l, hs j, O.zero_mem]
  · rcases lt_trichotomy j k with hjk | hjk | hjk
    · simp [hjk, hjk.not_gt, hjk.ne']
    · subst hjk; simp [hss]
    · simp [hjk, hjk.not_gt, hjk.ne', hγ]
end Formalism.HermitianLatticeCounting.P.S4aux
