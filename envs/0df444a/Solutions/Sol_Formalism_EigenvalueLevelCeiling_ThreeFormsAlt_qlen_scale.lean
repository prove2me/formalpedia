-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.qlen_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:31.758626+00:00
-- url     : https://prove2.me/submissions/38c5bc68-4b6e-47b8-bfa3-fefa2ef4cab1

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_qlen_eq_zero
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_lidx_of_le
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_mem_sc_inv
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_localization_sc
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_localization_inf
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_mem_OO_of_vw_nonneg
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_le_sc_inv
import Theorems.Thm_Formalism_DivisionValues_valuation_basic_properties
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_finLen


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
open Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
namespace Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
theorem _root_.solution [FiniteDimensional K Z] (hS : IdxScaleIn) (w : HeightOneSpectrum (𝓞 K))
    (W : Submodule K Z) (L : Submodule (𝓞 K) Z) (hL : IsLatIn W L) {a : K} (ha : a ≠ 0) (E : ℕ)
    (hE : vw w a = (E : ℤ)) :
    qlen (sc a⁻¹ (localization₂ w.asIdeal L)) (localization₂ w.asIdeal L) = ((E * finrank K W : ℕ) : ℕ∞) := by
  have hav : a ∈ OO w := mem_OO_of_vw_nonneg w ha (by rw [hE]; exact Int.natCast_nonneg E)
  have hloc := le_sc_inv w L ha hav
  have hfin : qlen (sc a⁻¹ (localization₂ w.asIdeal L)) (localization₂ w.asIdeal L) ≠ ⊤ := by
    obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have hr0 : algebraMap (𝓞 K) K r ≠ 0 := by
      intro h0
      rw [h0, zero_div] at hrs
      exact ha hrs.symm
    have hr : r ∈ nonZeroDivisors (𝓞 K) :=
      mem_nonZeroDivisors_of_ne_zero (fun h0 => hr0 (by rw [h0, map_zero]))
    rw [← localization_sc _ (inv_ne_zero ha)]
    refine Module.length_ne_top_iff.mpr
      (indexBasic_finLen w.asIdeal (sc a⁻¹ L) L (hL.1.map _) hr ?_)
    intro x hx
    have hx' := (mem_sc_inv ha L x).mp hx
    have : r • x = s • (a • x) := by
      rw [← algebraMap_smul K r, ← algebraMap_smul K s, smul_smul, ← hrs]
      congr 1
      field_simp
    rw [this]
    exact L.smul_mem s hx'
  have h := (hS K Z w W L L hL hL a⁻¹ (inv_ne_zero ha)).2
  have hinv : vw w a⁻¹ = - vw w a := (valuation_basic_properties K w).2.2.2.2.2.1 a
  have h0 : lix w L L = 0 := by
    unfold lix
    rw [lidx_of_le _ le_rfl, qlen_eq_zero le_rfl]
    rfl
  have h1 : lix w L (sc a⁻¹ L) =
      - ((qlen (sc a⁻¹ (localization₂ w.asIdeal L)) (localization₂ w.asIdeal L)).toNat : ℤ) := by
    unfold lix lidx locLen
    rw [localization_inf, localization_sc _ (inv_ne_zero ha), inf_eq_left.mpr hloc]
    change ((qlen (localization₂ w.asIdeal L) (localization₂ w.asIdeal L)).toNat : ℤ) -
      ((qlen (sc a⁻¹ (localization₂ w.asIdeal L)) (localization₂ w.asIdeal L)).toNat : ℤ) = _
    rw [qlen_eq_zero le_rfl]
    simp
  rw [h1, h0, hinv, hE] at h
  have h2 : (qlen (sc a⁻¹ (localization₂ w.asIdeal L)) (localization₂ w.asIdeal L)).toNat = E * finrank K W := by
    have : ((qlen (sc a⁻¹ (localization₂ w.asIdeal L)) (localization₂ w.asIdeal L)).toNat : ℤ) =
        (E : ℤ) * (finrank K W : ℤ) := by linarith
    exact_mod_cast this
  rw [← h2, ENat.natCast_toNat hfin]
end Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
