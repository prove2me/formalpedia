-- Prove2me | solution 1 for CompanionTheory.Zuck.iso_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:15:15.526485+00:00
-- url     : https://prove2.me/submissions/ef11c292-3657-43eb-b7b4-1344ad671ac8

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_ShiftApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped Kronecker
noncomputable section
open CompanionTheory CompanionTheory.Zuck
open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (IsHCParam)
open PI.ZuckTensor (GapAtLeast)
variable {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
namespace CompanionTheory.Zuck
theorem _root_.solution (S : Steps) (Lb : Lib t) {μ : Fin (2 * r + k + 1) → ℝ} {U U' : URep k r} {h : ℝ}
    (hU : U.R.IsDS ε μ) (hU' : U'.R.IsDS ε μ) (hg : GapAtLeast ε μ h) (ht : t _ ε < h) :
    IsIso (N := M) IsHom (one U) (one U') :=
  S.uIso k r _ U U' (Lb.uniq k r ε μ U.R U'.R h hU hU' hg ht)
end CompanionTheory.Zuck
