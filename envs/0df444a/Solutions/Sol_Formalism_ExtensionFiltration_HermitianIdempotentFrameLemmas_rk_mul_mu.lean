-- Prove2me | solution 1 for Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rk_mul_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:41:27.145493+00:00
-- url     : https://prove2.me/submissions/02866a67-3025-429c-8b72-e44d52763a2f

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_rkK_ne_zero
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_rkK_bot
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_nPl_ne_zero
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_log_ht
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_saturation_basic_properties
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
open Formalism.HN
open Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
theorem _root_.solution [IsTotallyComplex K] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    (rkK L : ℝ) * muDef b X L = -Real.log (ht b X L) / (nPl K : ℝ) := by
  by_cases h0 : L = ⊥
  · have hlat := (place_lattice_structure K V ι b X hX L hL).1
    have hd := (saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) L hlat).2.2.2.2.1
    rw [log_ht b X hX L hL, h0, rkK_bot, hd]
    simp
  · have hpos := (place_lattice_structure K V ι b X hX L hL).2.2
    have hj : (rkK L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (rkK_ne_zero b L h0)
    have hf : (nPl K : ℝ) ≠ 0 := nPl_ne_zero
    rw [(size_maximal_slope K V ι b X hX L hL h0).2.1, size, Real.log_rpow hpos]
    field_simp
end Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
