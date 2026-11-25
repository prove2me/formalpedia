-- Prove2me | solution 1 for Formalism.ExtensionFiltration.muMin_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:20:47.426105+00:00
-- url     : https://prove2.me/submissions/9858270a-0529-48a1-9eec-4717a356919b

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SpanMuMin
import Theorems.Thm_Formalism_ExtensionFiltration_rkK_span_singleton
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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
  [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.ExtensionFiltration
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : x ≠ 0) (θ : ℝ)
    (hθ : θ ≤ slope (Formalism.HermitianLatticesTheory.realize b X) (Submodule.span (𝓞 K) ({x} : Set V))) :
    θ ≤ muMin (Formalism.HermitianLatticesTheory.realize b X) (Submodule.span (𝓞 K) ({x} : Set V)) := by
  classical
  have hFG : (Submodule.span (𝓞 K) ({x} : Set V)).FG := Submodule.fg_span_singleton x
  obtain ⟨hLat, hrkL, -⟩ := Formalism.HN.place_lattice_structure K V ι b X hX _ hFG
  have hne : Submodule.span (𝓞 K) ({x} : Set V) ≠ ⊥ := by
    rw [Ne, Submodule.span_singleton_eq_bot]
    exact hx
  obtain ⟨-, hmin, -, -, -⟩ := Formalism.HN.slope_characterization (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) _ hLat hne
  rw [hmin]
  intro N hN
  obtain ⟨-, hmono, -, hzero, hdeg0, -⟩ := Formalism.HN.saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) _ hLat
  have hK : 0 < Module.finrank ℚ K := Module.finrank_pos
  rw [rkK_span_singleton x hx, mul_one] at hrkL
  by_cases hN0 : N = ⊥
  · subst hN0
    rw [hdeg0, (hzero ⊥ bot_le).mpr rfl]
    have hpos : (0 : ℝ) < (rk (Formalism.HermitianLatticesTheory.realize b X) (Submodule.span (𝓞 K) ({x} : Set V)) : ℝ) := by
      rw [hrkL]; exact_mod_cast hK
    have hθ' : θ ≤ deg (Formalism.HermitianLatticesTheory.realize b X) (Submodule.span (𝓞 K) ({x} : Set V)) /
        (rk (Formalism.HermitianLatticesTheory.realize b X) (Submodule.span (𝓞 K) ({x} : Set V)) : ℝ) := hθ
    rw [le_div_iff₀ hpos] at hθ'
    simpa using hθ'
  · have hNoeth : IsNoetherian (𝓞 K) (Submodule.span (𝓞 K) ({x} : Set V)) :=
      isNoetherian_of_fg_of_noetherian _ hFG
    have hNFG : N.FG := by
      have h1 := (IsNoetherian.noetherian (N.comap (Submodule.span (𝓞 K) ({x} : Set V)).subtype)).map
        (Submodule.span (𝓞 K) ({x} : Set V)).subtype
      rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hN] at h1
    obtain ⟨-, hrkN, -⟩ := Formalism.HN.place_lattice_structure K V ι b X hX N hNFG
    haveI : FiniteDimensional K V := Module.Finite.of_basis b
    have hkN : rkK (K := K) N = 1 := by
      have hle : Submodule.span K (N : Set V) ≤ Submodule.span K ({x} : Set V) := by
        rw [Submodule.span_le]
        intro y hy
        have hy' := hN hy
        rw [Submodule.mem_span_singleton] at hy'
        obtain ⟨a, rfl⟩ := hy'
        rw [SetLike.mem_coe, ← algebraMap_smul K a x]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
      have h1 : rkK (K := K) N ≤ 1 := by
        unfold rkK
        calc Module.finrank K (Submodule.span K (N : Set V))
            ≤ Module.finrank K (Submodule.span K ({x} : Set V)) := Submodule.finrank_mono hle
          _ = 1 := finrank_span_singleton hx
      have h2 : 0 < rkK (K := K) N := by
        unfold rkK
        apply Module.finrank_pos_iff_exists_ne_zero.mpr
        obtain ⟨y, hyN, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
        exact ⟨⟨y, Submodule.subset_span hyN⟩, fun h => hy0 (congrArg Subtype.val h)⟩
      omega
    rw [hkN, mul_one] at hrkN
    have hrkNL : rk (Formalism.HermitianLatticesTheory.realize b X) N = rk (Formalism.HermitianLatticesTheory.realize b X) (Submodule.span (𝓞 K) ({x} : Set V)) := by
      rw [hrkN, hrkL]
    rw [hrkNL, sub_self, mul_zero, sub_nonneg]
    exact (hmono N _ hN le_rfl).2 hrkNL
end Formalism.ExtensionFiltration
