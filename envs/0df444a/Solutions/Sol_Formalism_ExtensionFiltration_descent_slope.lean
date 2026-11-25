-- Prove2me | solution 1 for Formalism.ExtensionFiltration.descent_slope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:49:03.702901+00:00
-- url     : https://prove2.me/submissions/25941519-9077-40b1-b1b4-68d460f049ec

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeIneq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_DescentSlope
import Theorems.Thm_Formalism_ExtensionFiltration_slope_image_injective
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_saturation_basic_properties
import Theorems.Thm_Formalism_HN_slope_characterization


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
namespace Formalism.ExtensionFiltration
theorem _root_.solution : DescentSlope := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A B hAfg hBfg hA0 hinj hIB
  obtain ⟨hrkeq, hsl⟩ := slope_image_injective b X b' X' hX hX' φ A hAfg hA0 hinj
  set I := A.map (φ.restrictScalars (𝓞 K)) with hIdef
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b' X' with hρ'
  have hIfg : I.FG := hAfg.map _
  have hI0 : I ≠ ⊥ := by
    intro h
    apply hA0
    rw [eq_bot_iff]
    intro x hx
    have hm : φ x ∈ I := ⟨x, hx, rfl⟩
    rw [h] at hm
    have h0 : φ x = 0 := (Submodule.mem_bot _).1 hm
    exact (Submodule.mem_bot _).2 (hinj (by rw [h0, map_zero]))
  have hB0 : B ≠ ⊥ := fun h => hI0 (le_bot_iff.mp (h ▸ hIB))
  obtain ⟨hBlat, hrkB, -⟩ := place_lattice_structure K W κ b' X' hX' B hBfg
  obtain ⟨-, hrkI, -⟩ := place_lattice_structure K W κ b' X' hX' I hIfg
  have hSBB := saturation_basic_properties (𝓞 K) W _ ρ' B hBlat
  have hMB := slope_characterization (𝓞 K) W _ ρ' B hBlat hB0
  have hmin := (hMB.2.1 (muMin ρ' B)).1 le_rfl I hIB
  have hrkIpos : 0 < rk ρ' I := by
    rcases Nat.eq_zero_or_pos (rk ρ' I) with h | h
    · exact absurd ((hSBB.2.2.2.1 I hIB).1 h) hI0
    · exact h
  have hrkBpos : 0 < rk ρ' B := by
    rcases Nat.eq_zero_or_pos (rk ρ' B) with h | h
    · exact absurd ((hSBB.2.2.2.1 B le_rfl).1 h) hB0
    · exact h
  have hdI : deg ρ' I = slope ρ' I * (rk ρ' I : ℝ) := by
    have : (rk ρ' I : ℝ) ≠ 0 := by exact_mod_cast hrkIpos.ne'
    show deg ρ' I = deg ρ' I / (rk ρ' I : ℝ) * (rk ρ' I : ℝ)
    field_simp
  have hdB : deg ρ' B = slope ρ' B * (rk ρ' B : ℝ) := by
    have : (rk ρ' B : ℝ) ≠ 0 := by exact_mod_cast hrkBpos.ne'
    show deg ρ' B = deg ρ' B / (rk ρ' B : ℝ) * (rk ρ' B : ℝ)
    field_simp
  have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  rw [hdI, hdB, hrkB, hrkI, hrkeq] at hmin
  push_cast at hmin
  have hmin' : muMin ρ' B * ((rkK B : ℝ) - rkK A) ≤
      slope ρ' B * (rkK B : ℝ) - slope ρ' I * (rkK A : ℝ) := by
    refine le_of_mul_le_mul_left ?_ hn
    linarith
  have hra : (0 : ℝ) ≤ (rkK A : ℝ) := Nat.cast_nonneg _
  have h2 := mul_le_mul_of_nonneg_left hsl hra
  unfold muDef muMinDef
  simp only [← hρ, ← hρ']
  nlinarith [h2, hmin']
end Formalism.ExtensionFiltration
