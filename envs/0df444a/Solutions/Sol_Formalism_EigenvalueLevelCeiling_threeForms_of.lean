-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.threeForms_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:29.031423+00:00
-- url     : https://prove2.me/submissions/d2e46505-3bfa-40be-8da4-e7a83b142fdb

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_qlen_congr
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_qlen_inf_self
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_qlen_mono_left
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_qlen_le_of_sup
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_qlen_anti_right
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_qlen_add
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_lidx_of_le
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_localization_sc
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_localization_inf
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_cut_mono
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_localization_cut
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_mem_OO_of_vw_nonneg
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_exists_split
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_le_sc_inv
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_sc_inv_cut
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_isLatIn_cut
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_qlen_ne_top
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_qlen_scale
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
open ThreeFormsAlt
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (hS : IdxScaleIn) : ThreeForms := by
  intro K _ _ _ Z _ _ _ _ _ w A B hA hB hBA a E r ha hE
  have hav : a ∈ OO w := mem_OO_of_vw_nonneg w ha (by rw [hE]; exact Int.natCast_nonneg E)
  have hR : lix w A (A ⊓ sc a⁻¹ B) =
      ((qlen (localization₂ w.asIdeal A) (sc a⁻¹ (localization₂ w.asIdeal B))).toNat : ℤ) := by
    unfold lix
    rw [lidx_of_le _ (inf_le_left : A ⊓ sc a⁻¹ B ≤ A), localization_inf, localization_sc _ (inv_ne_zero ha),
      qlen_inf_self]
  have hL : ∀ W : Submodule K Z, lix w (cut W A) (cut W B) =
      ((qlen (cut W (localization₂ w.asIdeal A)) (cut W (localization₂ w.asIdeal B))).toNat : ℤ) := by
    intro W
    unfold lix
    rw [lidx_of_le _ (cut_mono W hBA), localization_cut, localization_cut]
  have hSc : ∀ W : Submodule K Z,
      qlen (cut W (sc a⁻¹ (localization₂ w.asIdeal B))) (cut W (localization₂ w.asIdeal B)) =
        ((E * finrank K W : ℕ) : ℕ∞) := by
    intro W
    rw [← sc_inv_cut W _ ha, ← localization_cut]
    exact qlen_scale hS w W (cut W B) (isLatIn_cut W B hB) ha E hE
  have hfin : qlen (localization₂ w.asIdeal A) (localization₂ w.asIdeal B) ≠ ⊤ :=
    qlen_ne_top w.asIdeal A B hA.1 hB.2
  have hBA' : localization₂ w.asIdeal B ≤ localization₂ w.asIdeal A := locBasic_locS_mono _ hBA
  have hBC' : localization₂ w.asIdeal B ≤ sc a⁻¹ (localization₂ w.asIdeal B) := le_sc_inv w B ha hav
  have hsplit := exists_split w A B hA.1 hBA ha hav
  rw [hR]
  simp only [hL]
  generalize localization₂ w.asIdeal A = A' at *
  generalize localization₂ w.asIdeal B = B' at *
  generalize hC : sc a⁻¹ B' = C' at *
  have hfinC : qlen A' C' ≠ ⊤ := ne_top_of_le_ne_top hfin (qlen_anti_right A' hBC')
  have hcongr : ∀ (W : Submodule K Z) (Y : Submodule (𝓞 K) Z),
      qlen (cut W A') (cut W Y) = qlen (cut W A') Y := fun W Y =>
    qlen_congr _ (fun x hx => ⟨fun h => h.1, fun h => ⟨h, hx.2⟩⟩)
  have hfinW : ∀ W : Submodule K Z, qlen (cut W A') (cut W B') ≠ ⊤ := fun W =>
    ne_top_of_le_ne_top hfin (by rw [hcongr]; exact qlen_mono_left inf_le_left _)
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hfinC
  constructor
  · intro h
    obtain ⟨W, h1, h2⟩ := hsplit
    obtain ⟨x, hx⟩ := ENat.ne_top_iff_exists.mp (hfinW W)
    have hadd : qlen (cut W A') (cut W B') =
        qlen (cut W C') (cut W B') + qlen (cut W A') (cut W C') :=
      qlen_add (cut_mono W hBC') (le_inf h2 inf_le_right)
    have hge : qlen A' C' ≤ qlen (cut W A') (cut W C') := by
      rw [hcongr]
      exact qlen_le_of_sup inf_le_left h1
    have hW := h W
    rw [hSc W] at hadd
    rw [← hx] at hadd hW
    rw [← hc] at hge ⊢
    have h3 : ((E * finrank K W : ℕ) : ℕ∞) + (c : ℕ∞) ≤ (x : ℕ∞) := by
      rw [hadd]
      exact add_le_add_right hge _
    have h4 : E * finrank K W + c ≤ x := by exact_mod_cast h3
    have h5 : ((E * finrank K W + c : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast h4
    push_cast at h5
    simp only [ENat.toNat_natCast, Int.cast_natCast] at hW ⊢
    linarith
  · intro h W
    obtain ⟨x, hx⟩ := ENat.ne_top_iff_exists.mp (hfinW W)
    have hadd : qlen (cut W A') (cut W B') =
        qlen (cut W (A' ⊓ C')) (cut W B') + qlen (cut W A') (cut W (A' ⊓ C')) :=
      qlen_add (cut_mono W (le_inf hBA' hBC')) (cut_mono W inf_le_left)
    have hle1 : qlen (cut W (A' ⊓ C')) (cut W B') ≤ qlen (cut W C') (cut W B') :=
      qlen_mono_left (cut_mono W inf_le_right) _
    have hle2 : qlen (cut W A') (cut W (A' ⊓ C')) ≤ qlen A' C' := by
      have h6 : qlen (cut W A') (A' ⊓ C') = qlen (cut W A') C' :=
        qlen_congr (cut W A') (fun x hx => ⟨fun h => h.2, fun h => ⟨hx.1, h⟩⟩)
      rw [hcongr, h6]
      exact qlen_mono_left inf_le_left _
    rw [hSc W] at hle1
    rw [← hx] at hadd ⊢
    rw [← hc] at hle2 h
    have h3 : (x : ℕ∞) ≤ ((E * finrank K W : ℕ) : ℕ∞) + (c : ℕ∞) := by
      rw [hadd]
      exact add_le_add hle1 hle2
    have h4 : x ≤ E * finrank K W + c := by exact_mod_cast h3
    have h5 : (x : ℝ) ≤ ((E * finrank K W + c : ℕ) : ℝ) := by exact_mod_cast h4
    push_cast at h5
    simp only [ENat.toNat_natCast, Int.cast_natCast] at h ⊢
    linarith
end Formalism.EigenvalueLevelCeiling
