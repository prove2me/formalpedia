-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.PrismTransfer.degD_le_muMax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:37:54.022317+00:00
-- url     : https://prove2.me/submissions/f035b0ee-9bb0-4fd9-b75f-9560fe334548

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_rkK_bot
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_saturation_basic_properties
import Theorems.Thm_Formalism_HN_slope_characterization


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
open Formalism.BranchingDeterminantCap.PrismTransfer
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.BranchingDeterminantCap.PrismTransfer
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (N M : Submodule (𝓞 K) V) (hM : M.FG) (hNM : N ≤ M) :
    degD b X N ≤ (rkK N : ℝ) * muMaxDef b X M := by
  unfold degD
  by_cases hb : N = ⊥
  · rw [hb, Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_bot]; simp
  · have hM0 : M ≠ ⊥ := fun h => hb (le_bot_iff.1 (h ▸ hNM))
    have hlat := (place_lattice_structure K V ι b X hX M hM).1
    have hmax := ((slope_characterization (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) M hlat hM0).1
      (muMax (Formalism.HermitianLatticesTheory.realize b X) M)).1 le_rfl N hNM
    have hr0 : rk (Formalism.HermitianLatticesTheory.realize b X) N ≠ 0 := fun h =>
      hb (((saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) M hlat).2.2.2.1 N hNM).1 h)
    have hrpos : (0 : ℝ) < (rk (Formalism.HermitianLatticesTheory.realize b X) N : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hr0
    have hs : slope (Formalism.HermitianLatticesTheory.realize b X) N ≤ muMax (Formalism.HermitianLatticesTheory.realize b X) M := by
      change deg (Formalism.HermitianLatticesTheory.realize b X) N / (rk (Formalism.HermitianLatticesTheory.realize b X) N : ℝ) ≤ _
      rw [div_le_iff₀ hrpos]
      exact hmax
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    unfold muDef muMaxDef
    linarith
end Formalism.BranchingDeterminantCap.PrismTransfer
