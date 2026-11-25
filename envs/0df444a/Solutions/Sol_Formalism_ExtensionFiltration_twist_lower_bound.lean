-- Prove2me | solution 1 for Formalism.ExtensionFiltration.twist_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:49:05.117214+00:00
-- url     : https://prove2.me/submissions/ed4f1d08-546c-4c38-a58d-608759ed8414

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_DescentSlope
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_TwistLower
import Theorems.Thm_Formalism_ExtensionFiltration_covol_of_le
import Theorems.Thm_P2M_Formalism_ExtensionFiltration_rkK_pos__577b2a56145a
import Theorems.Thm_Formalism_ExtensionFiltration_muDef_eq_covol
import Theorems.Thm_Formalism_ExtensionFiltration_idealScale_mu
import Theorems.Thm_Formalism_ExtensionFiltration_slope_image_injective
import Theorems.Thm_Formalism_F_covolPos
import Theorems.Thm_Formalism_HN_place_lattice_structure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open scoped Pointwise
namespace Formalism.ExtensionFiltration
theorem _root_.solution : TwistLower := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A B I hI hAfg hBfg hA0 hinj
    hle hrkBA
  have : FiniteDimensional K W := Module.Finite.of_basis b'
  obtain ⟨hrkeq, hsl⟩ := slope_image_injective b X b' X' hX hX' φ A hAfg hA0 hinj
  set A' := A.map (φ.restrictScalars (𝓞 K)) with hA'def
  have hA'fg : A'.FG := hAfg.map _
  have hA'0 : A' ≠ ⊥ := by
    intro h
    apply hA0
    rw [eq_bot_iff]
    intro x hx
    have hm : φ x ∈ A' := ⟨x, hx, rfl⟩
    rw [h] at hm
    have h0 : φ x = 0 := (Submodule.mem_bot _).1 hm
    exact (Submodule.mem_bot _).2 (hinj (by rw [h0, map_zero]))
  obtain ⟨hNfg, hrkN, hmuN⟩ := idealScale_mu b' X' hX' I hI A' hA'fg hA'0
  set N := Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) A' with hNdef
  have hrkNB : rkK N = rkK B := by rw [hrkN, hrkeq, hrkBA]
  have hcov := covol_of_le b' X' hX' N B hNfg hBfg hle hrkNB
  obtain ⟨hBlat, -, -⟩ := place_lattice_structure K W κ b' X' hX' B hBfg
  obtain ⟨hNlat, -, -⟩ := place_lattice_structure K W κ b' X' hX' N hNfg
  have hcB := Formalism.F.covolPos _ _ hBlat.2
  have hcN := Formalism.F.covolPos _ _ hNlat.2
  have hidx : (1 : ℝ) ≤ (N.toAddSubgroup.relIndex B.toAddSubgroup : ℝ) := by
    rcases Nat.eq_zero_or_pos (N.toAddSubgroup.relIndex B.toAddSubgroup) with h | h
    · rw [h, Nat.cast_zero, zero_mul] at hcov
      exact absurd hcov hcN.ne'
    · exact_mod_cast h
  have hcle : Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b' X') B) ≤
      Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b' X') N) := by
    rw [hcov]
    nlinarith
  have hlogle := Real.log_le_log hcB hcle
  have hr : (0 : ℝ) < rkK B := by
    rw [← hrkNB, hrkN]
    exact_mod_cast rkK_pos' A' hA'0
  have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  have hmuNB : muDef b' X' N ≤ muDef b' X' B := by
    rw [muDef_eq_covol b' X' hX' N hNfg, muDef_eq_covol b' X' hX' B hBfg, hrkNB]
    have : -Real.log (Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b' X') N)) /
        ((Module.finrank ℚ K : ℝ) * (rkK B : ℝ)) ≤
        -Real.log (Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b' X') B)) /
        ((Module.finrank ℚ K : ℝ) * (rkK B : ℝ)) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hmuA : muDef b X A - htMap b X b' X' φ ≤ muDef b' X' A' := by
    unfold muDef
    linarith
  linarith
end Formalism.ExtensionFiltration
