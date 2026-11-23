-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusBasic_lg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:23.252326+00:00
-- url     : https://prove2.me/submissions/b3716969-af70-4c85-a9fb-4551b9d32198

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hS
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_lg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module R W] (L : Submodule R W) (x : W)
    (hx : ∀ p : Ideal R, p.IsMaximal → x ∈ loc (K := K) p L) : x ∈ L := locBasic_lg (fun p => hcompl (K := K) p) (fun p hp s hs => genusBasic_hS p hp s hs) L x hx
end Formalism.HermitianLatticesTheory
