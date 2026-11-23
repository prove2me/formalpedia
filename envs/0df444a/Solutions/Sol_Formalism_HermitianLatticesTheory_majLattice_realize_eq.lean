-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majLattice_realize_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:14.781776+00:00
-- url     : https://prove2.me/submissions/bf991856-1e96-465d-a6d8-de5949be40d8

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CommonMajorizingLattice
import Definitions.Def_Lemmata_GeneralBFactSecondRest_Imports
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module
open scoped Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type*} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K] [AddCommGroup V]
  [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V) :
    realize b X x = majLattice_alt X (fun i => mixedEmbedding K (b.repr x i)) := by
  rfl
end Formalism.HermitianLatticesTheory
