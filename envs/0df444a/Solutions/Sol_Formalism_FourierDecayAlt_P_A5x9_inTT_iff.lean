-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.inTT_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:36.949415+00:00
-- url     : https://prove2.me/submissions/4bb67418-e8e9-4184-82e9-62fa18eb3631

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_Lam_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_isD_mulVec_msk
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnta_coef_fin
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnta_Lam_coord
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnta_row
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
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
theorem _root_.solution (Z Z' : Matrix (Fin n) (Fin n) K) (φ : coker R Z ≃ₗ[R] coker R Z') :
    InTT R (k + 1) Z Z' φ ↔ ∃ D, IsD R k D ∧ ∀ v v' : Fin n → R,
      φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' →
        ∀ j, (abelian₂ R k Z' v' - D *ᵥ abelian₂ R k Z v) j ∈ R := by
  constructor
  · intro hT
    have hex : ∀ j : Fin n, ∃ a : ℕ → R, k < j.val → ∀ (v v' : Fin n → R),
        φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' →
          lamN R Z' j.val v' = lamN R Z j.val v +
            ∑ l ∈ Finset.Ioo j.val n, a l • lamN R Z l v := by
      intro j
      by_cases hj : k < j.val
      · obtain ⟨a, ha⟩ := hT j.val hj j.2
        exact ⟨a, fun _ => ha⟩
      · exact ⟨0, fun h => absurd h hj⟩
    choose α hα using hex
    let D : Matrix (Fin n) (Fin n) K := fun a b =>
      if k < a.val then (if a = b then 1 else if a < b then ((α a b.val : R) : K) else 0)
      else (1 : Matrix (Fin n) (Fin n) K) a b
    have hD : IsD R k D := by
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · intro i j hji
        have hji' : j < i := hji
        simp only [D]
        by_cases hi : k < i.val
        · rw [if_pos hi, if_neg hji'.ne', if_neg (not_lt.2 hji'.le)]
        · rw [if_neg hi, Matrix.one_apply_ne hji'.ne']
      · intro a
        simp only [D]
        by_cases ha : k < a.val
        · rw [if_pos ha, if_pos trivial]
        · rw [if_neg ha, Matrix.one_apply_eq]
      · intro a b
        simp only [D]
        split_ifs with h1 h2 h3
        · exact R.one_mem
        · exact (α a b.val).2
        · exact R.zero_mem
        · rw [Matrix.one_apply]
          split_ifs
          · exact R.one_mem
          · exact R.zero_mem
      · intro a b ha
        simp only [D]
        rw [if_neg (by omega)]
    refine ⟨D, hD, fun v v' hv j => ?_⟩
    by_cases hj : k < j.val
    · rw [Pi.sub_apply, ← A5x3.mk_eq_mk, cnta_row R k hD Z j hj v, cnta_Lam_coord, if_pos hj]
      show lamN R Z' j.val v' = _
      rw [hα j hj v v' hv]
      congr 1
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [Finset.mem_Ioo] at hl
      congr 1
      have := cnta_coef_fin R k hD j ⟨l, hl.2⟩
      simp only at this
      rw [this]
      apply Subtype.ext
      have hjl : j < (⟨l, hl.2⟩ : Fin n) := by rw [Fin.lt_def]; exact hl.1
      simp only [D]
      rw [if_pos hj, if_neg hjl.ne, if_pos hjl]
    · rw [Lam_apply, Lam_apply, isD_mulVec_msk R k hD]
      simp [msk, hj, R.zero_mem]
  · rintro ⟨D, hD, h⟩ j hkj hjn
    refine ⟨cntaCoef R k hD ⟨j, hjn⟩, fun v v' hv => ?_⟩
    have hj : k < (⟨j, hjn⟩ : Fin n).val := hkj
    have h1 := h v v' hv ⟨j, hjn⟩
    rw [Pi.sub_apply, ← A5x3.mk_eq_mk, cnta_row R k hD Z ⟨j, hjn⟩ hj v, cnta_Lam_coord,
      if_pos hj] at h1
    exact h1
end Formalism.FourierDecayAlt.P.A5x9
