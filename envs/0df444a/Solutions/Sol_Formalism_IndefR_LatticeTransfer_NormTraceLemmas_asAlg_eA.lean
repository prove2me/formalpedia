-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.NormTraceLemmas.asAlg_eA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:52.024672+00:00
-- url     : https://prove2.me/submissions/6b84c7b2-835b-4f2d-8e7a-9252c2454fcd

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
theorem _root_.solution {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T)
    {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V) :
    ρ.asAlgebraHom (eA τ) = eS τ ρ := by
  simp only [eA, eS, map_smul, map_sum, Representation.asAlgebraHom_single]
end Formalism.IndefR.LatticeTransfer.NormTraceLemmas
