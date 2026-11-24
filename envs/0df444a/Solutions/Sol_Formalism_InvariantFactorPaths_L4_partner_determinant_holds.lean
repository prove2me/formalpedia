-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.partner_determinant_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:49:17.317718+00:00
-- url     : https://prove2.me/submissions/d4c3660b-3f56-4958-afe7-690093bbe25a

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementA
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithZp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_PartnerDeterminantHolds
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_GM_TM_smith_qp
import Theorems.Thm_Formalism_GM_smith_form_p_adic_integers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : PartnerDet := by
  intro p _ Vs _ _ _ _ be k g D hli hpart
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  set G : Matrix (Fin k) (Fin k) ℚ_[p] := Matrix.of fun a b => be (g a) (g b) with hG
  obtain ⟨U, V, dg, hU, hV, hUd, hVd, hGUV⟩ := Formalism.GM.TM.smith_qp smith_form_p_adic_integers G
  let φ : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom
  let U' : Matrix (Fin k) (Fin k) ℤ_[p] := fun x y => ⟨U x y, hU x y⟩
  let V' : Matrix (Fin k) (Fin k) ℤ_[p] := fun x y => ⟨V x y, hV x y⟩
  have hU'map : U'.map φ = U := by ext x y; rfl
  have hU'det : IsUnit U'.det := by
    rw [PadicInt.isUnit_iff]
    have : ((U'.det : ℤ_[p]) : ℚ_[p]) = U.det := by
      rw [← hU'map, show U'.map φ = φ.mapMatrix U' from rfl, ← RingHom.map_det]; rfl
    rw [PadicInt.norm_def, this, hUd]
  set W : Matrix (Fin k) (Fin k) ℤ_[p] := U'⁻¹ with hW
  have hWU : W * U' = 1 := Matrix.nonsing_inv_mul _ hU'det
  have hsm : ∀ (a : ℤ_[p]) (x : Vs), a • x = (a : ℚ_[p]) • x := fun a x => by
    rw [← PadicInt.algebraMap_apply, algebraMap_smul]

  have hd : ∀ i, (p : ℝ) ^ (-D) ≤ ‖dg i‖ := by
    intro i
    set u : Vs := ∑ a, W i a • g a with hu
    have huL : u ∈ Submodule.span ℤ_[p] (Set.range g) :=
      Submodule.mem_span_range_iff_exists_fun ℤ_[p] |>.mpr ⟨W i, rfl⟩
    have hprim : ∀ (a : ℤ_[p]) (x : Vs), x ∈ Submodule.span ℤ_[p] (Set.range g) → u = a • x → IsUnit a := by
      intro a x hx hux
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).mp hx
      have h0 : ∑ b, (W i b - a * c b) • g b = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum]
        rw [← hu, hux, sub_self]
      have h1 := Fintype.linearIndependent_iff.mp hli _ h0
      have h2 : (W * U') i i = a * ∑ b, c b * U' b i := by
        rw [Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [sub_eq_zero.mp (h1 b)]; ring
      rw [hWU, Matrix.one_apply_eq] at h2
      exact IsUnit.of_mul_eq_one _ h2.symm
    obtain ⟨u', hu'L, hu'⟩ := hpart u huL hprim
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).mp hu'L
    have hWG : ∀ b, be u (g b) = dg i * V i b := by
      intro b
      have e1 : be u (g b) = ((W.map φ) * G) i b := by
        rw [Matrix.mul_apply, hu, map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hsm, map_smul, LinearMap.smul_apply, smul_eq_mul]; rfl
      have e2 : (W.map φ) * U = 1 := by
        rw [← hU'map, ← Matrix.map_mul, hWU]
        exact Matrix.map_one φ (map_zero φ) (map_one φ)
      rw [e1, hGUV, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul, Matrix.diagonal_mul]
    have hval : be u (∑ b, c b • g b) = dg i * ((∑ b, c b * V' i b : ℤ_[p]) : ℚ_[p]) := by
      rw [map_sum, PadicInt.coe_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hsm, map_smul, smul_eq_mul, hWG b, PadicInt.coe_mul]
      show _ = dg i * ((c b : ℚ_[p]) * V i b)
      ring
    rw [hval, norm_mul] at hu'
    refine hu'.trans ?_
    calc ‖dg i‖ * ‖((∑ b, c b * V' i b : ℤ_[p]) : ℚ_[p])‖ ≤ ‖dg i‖ * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
      _ = ‖dg i‖ := mul_one _
  rw [hGUV, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, norm_mul, norm_mul, hUd, hVd, one_mul, mul_one,
    norm_prod]
  calc (p : ℝ) ^ (-(D * k)) = ∏ _i : Fin k, (p : ℝ) ^ (-D) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_mul_natCast hp0.le]
        congr 1; ring
    _ ≤ ∏ i, ‖dg i‖ := Finset.prod_le_prod (fun _ _ => (Real.rpow_pos_of_pos hp0 _).le) fun i _ => hd i
end Formalism.InvariantFactorPaths.L4
