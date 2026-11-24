-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majLattice_mem_zmap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:56.884008+00:00
-- url     : https://prove2.me/submissions/b4bd00f1-85ad-4c77-9007-3d1747b7ecb2

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
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :
    w ∈ zmap (realize b X) L ↔ ∃ x ∈ L, realize b X x = w := Iff.rfl
end Formalism.HermitianLatticesTheory
