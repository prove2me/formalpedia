-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.jf_psiOnto_of_cellDecomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:15:20.661409+00:00
-- url     : https://prove2.me/submissions/b8a61089-aabb-4564-8029-2f284555fd34

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDecomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellDecomposition_bigCell_one_fixes_vector
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellDecomposition_n_inv_S
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellDecomposition_n_S
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellHermitian_herm_bigCell
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellInversePair_uw_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mem_UWb
import Theorems.Thm_Formalism_FourierDecayAlt_P_b2_rank_one_coord
import Theorems.Thm_Formalism_FourierDecayAlt_P_bruhat_big_cell_factorization
import Theorems.Thm_Formalism_FourierDecayAlt_P_unipotent_weyl_properties
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_inv
import Theorems.Thm_Formalism_QuantumDeterminants_bigCellMinors
import Theorems.Thm_Formalism_QuantumDeterminants_gInv
import Theorems.Thm_Formalism_QuantumDeterminants_uWNormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.JF
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution (hCD : BigCellDecomposition.CellDecomp) : Formalism.FourierDecayAlt.JF.PsiOnto := by
  intro k r Wp Wq _ _ _ _ D g hg
  obtain ⟨n, hn, n', hn', c, hc, μ, hμ, rfl⟩ := hCD k r D.z D.z' g hg.1 hg.2.1
  set ζ := herm (Hb k) (μ *ᵥ wbPart k r D.z') (wbPart k r D.z) with hζdef
  have hmin := bigCellMinors k r D.z D.z' c μ D.z_mem D.z'_mem

  have hG : 0 < Gf k r D.z D.z' (bigCell k r c μ) := by
    have := hg.2.2
    rwa [gInv k r D.z D.z' D.z_mem D.z'_mem _ (BigCellDecomposition.n_inv_S hn) _ (BigCellDecomposition.n_S hn')] at this
  have hζ : Tz k r D.z * Tz k r D.z' < Complex.normSq ζ := by
    have hz := hmin.2.2 hc
    rw [BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem] at hz
    have hr := hmin.1 (Fin.last r)
    set P := Dmin k r D.z D.z' (bigCell k r c μ) ⟨r, by omega⟩ with hP
    have hP0 : P ≠ 0 := by
      have : P = ∏ a : Fin r with a.val < (Fin.last r).val, c a := hr
      rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
    have hlast : Dmin k r D.z D.z' (bigCell k r c μ) (Fin.last (r + 1)) = ζ * P := by
      unfold zeta at hz
      rw [← hP] at hz
      have h2 := div_mul_cancel₀ (Dmin k r D.z D.z' (bigCell k r c μ) (Fin.last (r + 1))) hP0
      rw [hz] at h2
      exact h2.symm
    unfold Gf at hG
    rw [hlast, ← hP, Complex.normSq_mul] at hG
    have h1 : 0 < Complex.normSq P := Complex.normSq_pos.2 hP0
    nlinarith

  have hfac := bruhat_big_cell_factorization k r c μ
  have huw := unipotent_weyl_properties k r
  have hm : embWb k r μ ∈ UWb k r := TwoByOneBlock.emb_mem_UWb hμ
  have hmz : herm (Hpk k r) (embWb k r μ *ᵥ D.z') D.z = ζ := by
    have e1 : embWb k r μ *ᵥ D.z' = bigCell k r c μ *ᵥ D.z' := by
      rw [hfac.2, ← Matrix.mulVec_mulVec, BigCellDecomposition.bigCell_one_fixes_vector D.z'_mem]
    rw [e1, BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem]
  obtain ⟨h, hh, h', hh', hmeq⟩ := b2_rank_one_coord k r D.z D.z' D.μsec D.k_pos D.z_mem D.z'_mem D.T_pos
    D.T'_pos D.sec (embWb k r μ) hm (by rw [hmz]; exact hζ)
  rw [hmz] at hmeq
  have hu1 := WeylGroupFacts.isUnit_of_uh hh.1
  have hu2 := WeylGroupFacts.isUnit_of_uh hh'.1
  have hun := WeylGroupFacts.isUnit_of_uh hn.1
  have hcomm : bigCell k r c 1 * h⁻¹ = h⁻¹ * bigCell k r c 1 :=
    (huw.2.2 c h⁻¹ (huw.2.1 D.z (BigCellInversePair.uw_inv hh))).symm

  refine ⟨((h, h * n * h⁻¹), (h', h' * n' * h'⁻¹)), ⟨hh,
      (uWNormal k r D.z D.z_mem h hh n hn).1, hh', (uWNormal k r D.z' D.z'_mem h' hh' n' hn').1⟩,
    (c, ζ), ⟨hc, hζ⟩, ?_⟩
  show n⁻¹ * bigCell k r c μ * n' = h⁻¹ * (h * n * h⁻¹)⁻¹ * bigCell k r c (D.μsec ζ) * (h' * n' * h'⁻¹) * h'
  rw [hfac.1, hmeq, (bruhat_big_cell_factorization k r c (D.μsec ζ)).1]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu1]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hu2, Matrix.mul_one]
  rw [← Matrix.mul_assoc (bigCell k r c 1) h⁻¹, hcomm]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hu1]
end Formalism.FourierDecayAlt.P
