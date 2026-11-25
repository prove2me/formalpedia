-- Prove2me | solution 1 for Formalism.ExtensionFiltration.log_covolume_slope_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:40:32.369633+00:00
-- url     : https://prove2.me/submissions/e8afb711-3880-4668-a00c-261fcc905de8

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_Assembly
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeAssemblyHolds
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_sizeMu_finrank_eq
import Theorems.Thm_Formalism_HN_size_maximal_slope


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
namespace Formalism.ExtensionFiltration
theorem _root_.solution : LcvMu := by
  intro K _ _ _ _ d hd X hX M hM
  have hfg : M.FG := Submodule.IsLattice.fg (self := hM)
  have hspan : Submodule.span K (M : Set (Fin d → K)) = ⊤ :=
    Submodule.IsLattice.span_eq_top (self := hM)
  have hrk : Formalism.HN.rkK M = d := by
    unfold Formalism.HN.rkK
    rw [hspan]
    simp
  have hne : M ≠ ⊥ := by
    intro h
    have h2 : Formalism.HN.rkK (⊥ : Submodule (𝓞 K) (Fin d → K)) = 0 := by
      unfold Formalism.HN.rkK
      simp
    rw [h, h2] at hrk
    omega
  obtain ⟨-, hmu, -⟩ := Formalism.HN.size_maximal_slope K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX M hfg hne
  have hht : 0 < Formalism.HN.ht (Pi.basisFun K (Fin d)) X M :=
    (Formalism.HN.place_lattice_structure K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX M hfg).2.2
  have hn : (finrank ℚ K : ℝ) = 2 * (Formalism.HN.nPl K : ℝ) := by
    exact_mod_cast Formalism.HN.sizeMu_finrank_eq K
  have hf : (0 : ℝ) < Formalism.HN.nPl K := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace K))
  have hDr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [hmu, Formalism.HN.size, Real.log_rpow hht, hrk, Formalism.DivisionValues.lcv, hn]
  field_simp
end Formalism.ExtensionFiltration
