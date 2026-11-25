-- Prove2me | solution 1 for Formalism.ExtensionFiltration.muDef_line_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:41:30.69939+00:00
-- url     : https://prove2.me/submissions/96193d71-8fa5-47cc-9a7c-29d9a1bac4c1

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeEstimateAnchoredWeights
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeFullAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeIntoDivisionHolds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SpanMuMin
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_TwistLower
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GlobalBoundRefinements
import Theorems.Thm_Formalism_ExtensionFiltration_majAt_self_re
import Theorems.Thm_Formalism_ExtensionFiltration_mink_normAt_pos
import Theorems.Thm_Formalism_ExtensionFiltration_rkK_span_singleton
import Theorems.Thm_Formalism_HN_height_gram_determinant
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
open Formalism Formalism.ExtensionFiltration
noncomputable section
open Module NumberField
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
  [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.ExtensionFiltration
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : x ≠ 0) :
    muDef b X (Submodule.span (𝓞 K) ({x} : Set V)) =
      -((1 / (nPl K : ℝ)) * ∑ v, 2 * Real.log (Formalism.HermitianLatticesTheory.normAt b X v x)) := by
  set L : Submodule (𝓞 K) V := Submodule.span (𝓞 K) ({x} : Set V) with hL
  have hLfg : L.FG := Submodule.fg_span (Set.finite_singleton x)
  have hL0 : L ≠ ⊥ := by
    intro h
    exact hx ((Submodule.span_singleton_eq_bot).1 h)
  have hrk : rkK (K := K) L = 1 := rkK_span_singleton x hx
  have hf : 0 < nPl K := Fintype.card_pos
  have hfR : (0 : ℝ) < (nPl K : ℝ) := by exact_mod_cast hf
  obtain ⟨-, hmu, -⟩ := size_maximal_slope K V ι b X hX L hLfg hL0
  have hpos : 0 < ht b X L := (place_lattice_structure K V ι b X hX L hLfg).2.2
  have hli : LinearIndependent K (fun _ : Fin 1 => x) :=
    LinearIndependent.of_subsingleton (0 : Fin 1) hx
  have hrange : Set.range (fun _ : Fin 1 => x) = {x} := Set.range_const
  have hg := (height_gram_determinant K V ι b X hX 1 (fun _ : Fin 1 => x) hli).1
  rw [hrange] at hg
  have hht : ht b X L = ∏ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := by
    rw [hL, hg]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Matrix.det_fin_one]
    simp only [gramPl, Matrix.of_apply]
    rw [majAt_self_re]
  have hlog : Real.log (ht b X L) = ∑ v, 2 * Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) := by
    rw [hht, Real.log_prod (s := Finset.univ) (f := fun v => Formalism.HermitianLatticesTheory.normAt b X v x ^ 2)
      (fun v _ => pow_ne_zero 2 (mink_normAt_pos b X hX v x hx).ne')]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Real.log_pow]; norm_num
  rw [hmu]
  unfold size
  rw [Real.log_rpow hpos, hrk, hlog, Nat.cast_one]
  field_simp
end Formalism.ExtensionFiltration
