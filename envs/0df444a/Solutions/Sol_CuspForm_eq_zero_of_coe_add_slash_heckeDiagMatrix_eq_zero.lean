-- Prove2me | solution 1 for CuspForm.eq_zero_of_coe_add_slash_heckeDiagMatrix_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e5dc1108-e55e-5c67-b9a6-27324d77eab1

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_CuspForm_vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant
import Theorems.Thm_CuspForm_eq_zero_of_forall_vadd_inv_pow_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_eq_zero_of_coe_add_slash_heckeDiagMatrix_eq_zero
p2m_attr_erase "instance" "Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"

open CongruenceSubgroup ModularForm UpperHalfPlane
open scoped ModularForm UpperHalfPlane MatrixGroups

theorem solution
    {R q' : ℕ} [NeZero R] (hq' : q'.Prime) (hq'R : ¬ q' ∣ R) (k : ℤ)
    (x y : CuspForm ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (h : (⇑x : ℍ → ℂ) + ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix q') = 0) :
    x = 0 ∧ y = 0 := by
  have hyδ : ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix q') = -(⇑x : ℍ → ℂ) := eq_neg_of_add_eq_zero_right h
  have hy : ∀ γ ∈ ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix q') ∣[k] γ = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix q' := by
    intro γ hγ
    rw [hyδ, SlashAction.neg_slash, SlashInvariantFormClass.slash_action_eq x γ hγ]
  have hper : ∀ (j : ℕ) (τ : ℍ), y ((((q' : ℝ) ^ j)⁻¹) +ᵥ τ) = y τ :=
    fun j τ => CuspForm.vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant hq' hq'R k y hy j τ
  have hy0 : y = 0 := CuspForm.eq_zero_of_forall_vadd_inv_pow_eq hq'.one_lt k y hper
  refine ⟨?_, hy0⟩
  have hx : (⇑x : ℍ → ℂ) = 0 := by
    rw [← neg_eq_zero, ← hyδ, hy0]
    show ((⇑(0 : CuspForm ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) : ℍ → ℂ) ∣[k] heckeDiagMatrix q') = 0
    rw [CuspForm.coe_zero, SlashAction.zero_slash]
  exact DFunLike.ext x 0 (fun τ => by simpa using congrFun hx τ)

end S_CuspForm_eq_zero_of_coe_add_slash_heckeDiagMatrix_eq_zero
end P2MW
export P2MW.S_CuspForm_eq_zero_of_coe_add_slash_heckeDiagMatrix_eq_zero (solution)
