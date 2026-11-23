-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusBasic_hS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:14.406593+00:00
-- url     : https://prove2.me/submissions/c4edb076-1a2e-4681-a551-5620a4e82986

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_hcompl_not_mem


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
theorem _root_.solution (p : Ideal R) (hp : p.IsMaximal) (s : R) (hs : s ∈ hcompl (K := K) p) :
    s ∉ p := by
  haveI := hp.isPrime
  exact locBasic_hcompl_not_mem p s hs
end Formalism.HermitianLatticesTheory
