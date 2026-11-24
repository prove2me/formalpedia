-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_j_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:23.482667+00:00
-- url     : https://prove2.me/submissions/d8157dad-5e1e-4d0c-8208-67a164dd4ec9

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_TCols_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_subsing
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_ext_card
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_ext_surj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hn : Dominant nu) (hi : Interl lam nu) (K : TIdx lam)
    (hK : ∀ c : ↥(TCols lam), (Fin.last m ∈ (K c).1 ↔ colH lam c = colH nu c + 1)) :
    ∃ K' : TIdx nu, qr_j hi K' = K := by
  have hc : ∀ c : ↥(TCols lam), (univ.filter fun a : Fin m => a.castSucc ∈ (K c).1).card = colH nu c := by
    intro c
    have h1 := congrArg Finset.card (qr_ext_surj _ (K c).1 (hK c))
    rw [qr_ext_card, (K c).2] at h1
    have h2 := qr_colH_eq hi c
    omega
  refine ⟨fun c => ⟨_, hc ⟨c.1, qr_TCols_sub hi c.2⟩⟩, ?_⟩
  funext c
  apply Subtype.ext
  show qr_ext _ _ = _
  rw [qr_ext_surj _ (K c).1 (hK c)]
  congr 1
  by_cases h : c.1 ∈ TCols nu
  · rw [qr_base, dif_pos h]
  · have := qr_subsing hn h
    exact congrArg Subtype.val (Subsingleton.elim (qr_base _ c.1) ⟨_, hc c⟩)
end Formalism.InvariantFactorPaths.ColumnFamilies
