-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.NormTraceLemmas.asAlg_epA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:52.496629+00:00
-- url     : https://prove2.me/submissions/94660a10-fd42-4e0a-888b-b2360f14e722

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Lemmata_RankOneOrbitForms_RankOneForm
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_ExistsStrictHenselianAbsolutelyClosedLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open Formalism.IndefR.LatticeTransfer.NormTraceLemmas
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace Formalism.IndefR.LatticeTransfer.NormTraceLemmas
theorem _root_.solution (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) {V : Type} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) : ρ.asAlgebraHom (epA H χ) = epP H χ ρ := by
  simp only [epA, epP, map_smul, map_sum, Representation.asAlgebraHom_single]
end Formalism.IndefR.LatticeTransfer.NormTraceLemmas
