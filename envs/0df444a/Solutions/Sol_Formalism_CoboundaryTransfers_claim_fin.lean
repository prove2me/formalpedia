-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.claim_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:10.209798+00:00
-- url     : https://prove2.me/submissions/8599312c-4605-414c-b04f-aab14a918828

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_TorsionKilledCriterionHolds
import Theorems.Thm_Formalism_CoboundaryTransfers_aeval_stable
import Theorems.Thm_Formalism_CoboundaryTransfers_N_QInv
import Theorems.Thm_P2M_Formalism_CoboundaryTransfers___QInv_fa44b24c21bd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
namespace Formalism.CoboundaryTransfers
theorem _root_.solution (W : WachMod B M D) (δ : D →ₗ[O] D) (R : Polynomial O) (a : ℕ) (cΓ : O)
    (h2 : ∀ y, B.X • δ y = W.γ y - y)
    (h6 : ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      cΓ • (B.X • n) = (W.γ (B.X • x) - B.X • x) + B.X ^ (a + 1) • z')
    (h7 : ∀ n ∈ W.N, ∃ z ∈ W.N, B.X ^ (a + 1) • n = B.X ^ (a + 1) • z - W.φ (B.X ^ (a + 1) • z))
    (w : D) (hw : W.QInv w) (hm : Polynomial.aeval δ R w ∈ W.N) :
    W.IsCob2 ((R.eval 0 * cΓ) • (B.X • w)) := by
  have RQ : ∀ f : Polynomial O, ∀ y, W.QInv y → W.QInv (Polynomial.aeval δ f y) :=
    fun f => aeval_stable δ (QS W) (δ_QInv W δ h2) f
  obtain ⟨R1, hR1⟩ := Polynomial.X_dvd_sub_C (p := R)
  have eD : (R.eval 0) • w = Polynomial.aeval δ R w - δ (Polynomial.aeval δ R1 w) := by
    have : R = Polynomial.C (R.coeff 0) + Polynomial.X * R1 := by rw [← hR1]; ring
    conv_rhs => rw [this]
    rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, LinearMap.add_apply,
      Module.End.mul_apply, Polynomial.coeff_zero_eq_eval_zero, Algebra.algebraMap_eq_smul_one,
      LinearMap.smul_apply, Module.End.one_apply]
    abel
  obtain ⟨x2, hx2, z2, hz2, hc2⟩ := h6 _ hm
  obtain ⟨z3, hz3, h73⟩ := h7 z2 hz2
  refine ⟨B.X • x2 - cΓ • Polynomial.aeval δ R1 w, B.X • (B.X ^ a • z3),
    ⟨?_, _, W.N.smul_mem _ hz3, rfl⟩, ?_⟩
  · exact (QS W).sub_mem (N_QInv W (W.N.smul_mem _ hx2)) ((QS W).smul_mem _ (RQ R1 w hw))
  · have e3 : B.X • (B.X ^ a • z3) = B.X ^ (a + 1) • z3 := by rw [smul_smul, ← pow_succ']
    simp only [WachMod.d1, e3]
    have e4 : (R.eval 0 * cΓ) • (B.X • w) = cΓ • (B.X • ((R.eval 0) • w)) := by
      rw [mul_comm, mul_smul, smul_comm (R.eval 0) B.X]
    rw [e4, eD, smul_sub, smul_sub, hc2, h73]
    simp only [h2, map_sub, LinearMap.map_smul, smul_sub]
    abel
end Formalism.CoboundaryTransfers
