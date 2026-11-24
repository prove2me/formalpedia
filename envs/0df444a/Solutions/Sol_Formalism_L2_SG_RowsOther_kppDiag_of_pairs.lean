-- Prove2me | solution 1 for Formalism.L2.SG.RowsOther.kppDiag_of_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:19:30.147368+00:00
-- url     : https://prove2.me/submissions/8845880c-2644-4ac3-a501-19a68fa82c33

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RowsOther

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RowsOther
open Formalism.FourierDecayAlt
variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)
namespace Formalism.L2.SG.RowsOther
theorem _root_.solution [CompleteSpace H₁] (hP : PB.NormSqBoundOfEqualIota) (hE : PB.GramSumLeOfPosSemidef) (hS : PB.PairSplit)
    (hSub : PB.SubFamily) (Pg du : ℝ) (k f : ℕ) (hPg : 0 ≤ Pg) (hAbs : X.AbsConv) (hO : X.RowOrth)
    (hC : X.CorankPos) (hN : X.NormExpansionOn X.degSet) (hG : X.GGBound Pg)
    (hB : PairsDeg X Pg du k f) : KppDiag X du k f := by
  unfold KppDiag
  have h1 := hP hE τ Rw I H H₁ X Pg X.degSet hN hG
  rw [((hS τ Rw I H H₁ X hAbs hO hC).1 X.degSet)] at h1
  have h3 := (hSub τ Rw I H H₁ X hAbs _ _ (subset_refl (X.allPairs X.degSet))).2
  calc ‖X.part X.degSet‖ ^ 2 ≤ Pg * X.pairSum (X.allPairs X.degSet) := h1
    _ ≤ Pg * X.pairAbs (X.allPairs X.degSet) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans h3) hPg
    _ ≤ _ := hB
end Formalism.L2.SG.RowsOther
