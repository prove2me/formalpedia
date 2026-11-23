-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.cnta_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:00.544604+00:00
-- url     : https://prove2.me/submissions/a2532f79-7349-4001-9092-7695eb4ab4f3

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnta_coef_fin
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnta_Lam_coord
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_up_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_smul_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution {D : Matrix (Fin n) (Fin n) K} (hD : IsD R k D) (Z : Matrix (Fin n) (Fin n) K)
    (j : Fin n) (hj : k < j.val) (v : Fin n → R) :
    (Submodule.Quotient.mk ((D *ᵥ abelian₂ R k Z v) j) : KR R) =
      lamN R Z j.val v + ∑ l ∈ Finset.Ioo j.val n, cntaCoef R k hD j l • lamN R Z l v := by
  have h1 : (Submodule.Quotient.mk ((D *ᵥ abelian₂ R k Z v) j) : KR R) =
      ∑ b : Fin n, cntaCoef R k hD j b.val • lamN R Z b.val v := by
    simp only [Matrix.mulVec, dotProduct]
    rw [← Submodule.mkQ_apply, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Submodule.mkQ_apply, cnta_coef_fin, cnta_Lam_coord]
    by_cases hb : k < b.val
    · rw [if_pos hb]
      show _ = _ • (Submodule.Quotient.mk (lamTil R Z b.val v) : KR R)
      rw [A5x3.smul_mk]
    · have hbj : b < j := by rw [Fin.lt_def]; omega
      have h0 : D j b = 0 := Formalism.DoubleCosetMeasures.P.Phase.up_zero hD.1 hbj
      have h0' : (⟨D j b, hD.2.1 _ _⟩ : R) = 0 := Subtype.ext h0
      rw [if_neg hb, h0', mul_zero, zero_smul]
      rfl
  rw [h1, Fin.sum_univ_eq_sum_range (fun l => cntaCoef R k hD j l • lamN R Z l v) n]
  have h2 : ∑ l ∈ Finset.range n, cntaCoef R k hD j l • lamN R Z l v =
      ∑ l ∈ Finset.Ico j.val n, cntaCoef R k hD j l • lamN R Z l v := by
    symm
    apply Finset.sum_subset
    · intro l hl
      rw [Finset.mem_Ico] at hl
      exact Finset.mem_range.2 hl.2
    · intro l hl hl'
      rw [Finset.mem_range] at hl
      rw [Finset.mem_Ico] at hl'
      have hlj : (⟨l, hl⟩ : Fin n) < j := by rw [Fin.lt_def]; simp only; omega
      have h0 : D j ⟨l, hl⟩ = 0 := Formalism.DoubleCosetMeasures.P.Phase.up_zero hD.1 hlj
      have := cnta_coef_fin R k hD j ⟨l, hl⟩
      simp only at this
      rw [this]
      have h0' : (⟨D j ⟨l, hl⟩, hD.2.1 _ _⟩ : R) = 0 := Subtype.ext h0
      rw [h0', zero_smul]
  rw [h2, ← Finset.Ioo_insert_left j.2, Finset.sum_insert (by simp)]
  congr 1
  rw [cnta_coef_fin]
  have h1' : (⟨D j j, hD.2.1 _ _⟩ : R) = 1 := Subtype.ext (hD.1.2 j)
  rw [h1', one_smul]
end Formalism.FourierDecayAlt.P.A5x9
