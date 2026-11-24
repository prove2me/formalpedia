-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majLattice_B_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:56.308069+00:00
-- url     : https://prove2.me/submissions/18385cb7-a512-42af-bf57-1739a4091bcc

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CommonMajorizingLattice
import Definitions.Def_Lemmata_GeneralBFactSecondRest_Imports
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Theorems.Thm_Formalism_HermitianLatticesTheory_majLattice_realize_eq

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
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (k : Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 K)) :
    majLattice_B X hX k = realize b X (integralBasis K k.2 • b k.1) := by
  rw [majLattice_realize_eq]
  have : (fun i => mixedEmbedding K (b.repr (integralBasis K k.2 • b k.1) i)) =
      Pi.single k.1 (latticeBasis K k.2) := by
    funext i
    rcases eq_or_ne i k.1 with rfl | h
    · simp [Algebra.smul_def]
    · simp [h]
  rw [this]
  simp [majLattice_B]
end Formalism.HermitianLatticesTheory
