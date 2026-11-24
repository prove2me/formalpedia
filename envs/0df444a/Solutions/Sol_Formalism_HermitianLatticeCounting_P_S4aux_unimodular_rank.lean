-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.unimodular_rank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:14.493055+00:00
-- url     : https://prove2.me/submissions/f865e2c5-cc3e-4ea9-ba3d-a48cc2609428

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_not_unit_of_mem_mO
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_polar_mO
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_span
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_exists_orth_family_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : UnimodRank := by
  intro o O abelian₂ _ _ _ _ _ _ _ _ _ _ h hU hSD ρ hρ
  have : Nontrivial O := Module.nontrivial_of_finrank_pos (R := o) (by rw [hU.rank2]; norm_num)
  obtain ⟨v, horth, hunit⟩ := exists_orth_family_gen h (mO o O) (not_unit_of_mem_mO hU)
    (polar_mO hU h hSD.1) hSD ρ hρ
  obtain ⟨h1, h3, h4, h5⟩ := orth_span h v horth hunit
  exact ⟨Submodule.span O (Set.range v), h1, by rw [h3, Fintype.card_fin], h4, h5⟩
end Formalism.HermitianLatticeCounting.P.S4aux
