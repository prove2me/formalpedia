-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.ycondC_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:33:46.921293+00:00
-- url     : https://prove2.me/submissions/8041ac13-4018-4bae-8587-8a9f99fc4486

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typeProj_glActC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typeProj_polC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_proj_fixC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycondC_glStable
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycondC_le_supp
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycondC_keep
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_first_weight_le_of_support
import Theorems.Thm_Formalism_CountingSumsFrames_comm_preserves_weight_le
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_pol


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (h0 : (0 : Fin r) ∈ Cs)
    (Mt : WithTop ℤ) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j Cs T P) (hT : ∀ la : Fin r → ℤ, ((la 0 : ℤ) : WithTop ℤ) ≤ Mt → la ∈ T) :
    ∀ x ∈ YCondC p LL j Cs Mt ⊓ Pol p r LL, P x = x := by
  intro x hx
  refine proj_fixC LL j Cs T P hP (YCondC p LL j Cs Mt ⊓ Pol p r LL) inf_le_right ?_ ?_ ?_ x hx
  · intro c hc d hd y hy
    rw [Submodule.mem_inf] at hy ⊢
    exact ⟨ycondC_glStable LL j Cs Mt c hc d hd y hy.1, glAct_pol LL j c d y hy.2⟩
  · intro y hy
    rw [Submodule.mem_inf] at hy ⊢
    exact ⟨ycondC_keep LL j Cs Mt P (fun c hc d hd z => typeProj_glActC LL j Cs T P hP c hc d hd z)
      (comm_preserves_weight_le LL j Mt P (fun z => typeProj_glActC LL j Cs T P hP 0 h0 0 h0 z)) y hy.1,
      typeProj_polC LL j Cs T P hP y hy.2⟩
  · intro h hh hh0 μ hμ
    rw [Submodule.mem_inf] at hh
    apply hT
    exact first_weight_le_of_support LL j Cs h0 Mt μ h hh0 (ycondC_le_supp LL j Cs Mt hh.1)
      (Submodule.mem_inf.mp hμ).1
end Formalism.InvariantFactorPaths.L4
