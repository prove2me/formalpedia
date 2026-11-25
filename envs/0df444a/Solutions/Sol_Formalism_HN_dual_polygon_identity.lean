-- Prove2me | solution 1 for Formalism.HN.dual_polygon_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:40:36.55283+00:00
-- url     : https://prove2.me/submissions/23035c10-1fbc-47da-8286-bd025125e1b1

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Theorems.Thm_Formalism_HN_DualPolygon_dualFrame_unit
import Theorems.Thm_Formalism_HN_DualPolygon_dualLat_fg
import Theorems.Thm_Formalism_HN_DualPolygon_dualLat_span
import Theorems.Thm_Formalism_HN_DualPolygon_ht_dual
import Theorems.Thm_Formalism_HN_DualPolygon_rkK_dualLat
import Theorems.Thm_Formalism_HN_DualPolygon_dual_dual
import Theorems.Thm_Formalism_HN_DualPolygon_dual_ne_bot
import Theorems.Thm_Formalism_HN_DualPolygon_mu_dual
import Theorems.Thm_Formalism_HN_place_lattice_structure
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
open Formalism Formalism.HN
open DualPolygon
namespace Formalism.HN
theorem _root_.solution : DualPl := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX A hA hsp
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hX' := dualFrame_unit X hX
  have hht := ht_dual b X hX A hA hsp
  have hpos := (place_lattice_structure K V ι b X hX A hA).2.2
  have hhtinv : ht b.dualBasis (dualFrame X) (dualLat A) = (ht b X A)⁻¹ :=
    eq_inv_of_mul_eq_one_left hht
  have hrkA : rkK A = finrank K V := by unfold rkK; rw [hsp, finrank_top]
  have hrkD := rkK_dualLat b A hA hsp
  have hdfg := dualLat_fg A hsp
  have hc2 : ∀ m : ℝ, (Real.log 2 / 2 - logDisc K / (2 * (finrank ℚ K : ℝ))) -
      ((Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) - m) =
      -((Real.log 2 / 2 - logDisc K / (2 * (finrank ℚ K : ℝ))) - m) := by
    intro m
    unfold logDisc
    ring
  refine ⟨hdfg, dualLat_span A hA hsp, hhtinv, ?_, ?_, ?_, dual_dual b X hX A hA hsp⟩
  · unfold size
    rw [hhtinv, hrkD, hrkA]
    exact Real.inv_rpow hpos.le _
  · by_cases hA0 : A = ⊥
    · have hsub : ∀ x : V, x = 0 := by
        intro x
        have : x ∈ Submodule.span K (A : Set V) := hsp ▸ Submodule.mem_top
        rw [hA0] at this
        simpa using this
      have hdual : ∀ f : Module.Dual K V, f = 0 := fun f =>
        LinearMap.ext fun x => by rw [hsub x]; simp
      have h1 : leastSize b.dualBasis (dualFrame X) (dualLat A) = 0 := by
        unfold leastSize
        convert Real.sInf_empty
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨R, -, hR0, -⟩
        exact hR0 (eq_bot_iff.2 fun f _ => (Submodule.mem_bot _).2 (hdual f))
      have h2 : largestSize b X A = 0 := by
        unfold largestSize
        convert Real.sSup_empty
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨S, hS, hSA, -⟩
        exact hSA (le_antisymm hS.1 (by rw [hA0]; exact bot_le))
      rw [h1, h2, inv_zero]
    · obtain ⟨-, -, -, -, hg, -⟩ := size_maximal_slope K V ι b X hX A hA hA0
      obtain ⟨-, -, -, hl', -, -⟩ := size_maximal_slope K _ ι b.dualBasis (dualFrame X) hX'
        (dualLat A) hdfg (dual_ne_bot b A hA hsp hA0)
      rw [hl', hg, (mu_dual b X hX A hA hsp hA0).1, ← Real.exp_neg, hc2]
  · by_cases hA0 : A = ⊥
    · have hsub : ∀ x : V, x = 0 := by
        intro x
        have : x ∈ Submodule.span K (A : Set V) := hsp ▸ Submodule.mem_top
        rw [hA0] at this
        simpa using this
      have hdual : ∀ f : Module.Dual K V, f = 0 := fun f =>
        LinearMap.ext fun x => by rw [hsub x]; simp
      have hbot : ∀ R : Submodule (𝓞 K) (Module.Dual K V), R = ⊥ := fun R =>
        eq_bot_iff.2 fun f _ => (Submodule.mem_bot _).2 (hdual f)
      have h1 : largestSize b.dualBasis (dualFrame X) (dualLat A) = 0 := by
        unfold largestSize
        convert Real.sSup_empty
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨S, -, hSA, -⟩
        exact hSA (by rw [hbot S, hbot (dualLat A)])
      have h2 : leastSize b X A = 0 := by
        unfold leastSize
        convert Real.sInf_empty
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨R, hR, hR0, -⟩
        exact hR0 (le_antisymm (by rw [← hA0]; exact hR) bot_le)
      rw [h1, h2, inv_zero]
    · obtain ⟨-, -, -, hl, -, -⟩ := size_maximal_slope K V ι b X hX A hA hA0
      obtain ⟨-, -, -, -, hg', -⟩ := size_maximal_slope K _ ι b.dualBasis (dualFrame X) hX'
        (dualLat A) hdfg (dual_ne_bot b A hA hsp hA0)
      rw [hg', hl, (mu_dual b X hX A hA hsp hA0).2, ← Real.exp_neg, hc2]
end Formalism.HN
