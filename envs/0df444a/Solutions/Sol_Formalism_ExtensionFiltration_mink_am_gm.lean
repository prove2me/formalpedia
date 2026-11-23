-- Prove2me | solution 1 for Formalism.ExtensionFiltration.mink_am_gm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:39:47.320799+00:00
-- url     : https://prove2.me/submissions/b9acc686-e248-4297-997d-55eb63001035

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_MuMaxMinkowski

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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
  [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.ExtensionFiltration
theorem _root_.solution {σ : Type} [Fintype σ] [Nonempty σ] (a : σ → ℝ) (ha : ∀ v, 0 < a v) :
    (Fintype.card σ : ℝ) * Real.exp (2 * ((1 / (Fintype.card σ : ℝ)) * ∑ v, Real.log (a v))) ≤
      ∑ v, a v ^ 2 := by
  set n : ℝ := (Fintype.card σ : ℝ) with hn_def
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hw : ∑ _v : σ, (1 / n) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def, mul_one_div_cancel hn.ne']
  have hJ := convexOn_exp.map_sum_le (t := Finset.univ) (w := fun _ => 1 / n)
    (p := fun v => 2 * Real.log (a v)) (fun _ _ => by positivity) hw (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hJ
  have hexp : ∀ v, Real.exp (2 * Real.log (a v)) = a v ^ 2 := fun v => by
    rw [two_mul, Real.exp_add, Real.exp_log (ha v)]
    ring
  have hL : ∑ v, 1 / n * (2 * Real.log (a v)) = 2 * (1 / n * ∑ v, Real.log (a v)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hR : ∑ v, 1 / n * Real.exp (2 * Real.log (a v)) = 1 / n * ∑ v, a v ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [hexp v]
  rw [hL, hR] at hJ
  have h3 : n * (1 / n * ∑ v, a v ^ 2) = ∑ v, a v ^ 2 := by
    rw [← mul_assoc, mul_one_div_cancel hn.ne', one_mul]
  exact (mul_le_mul_of_nonneg_left hJ hn.le).trans_eq h3
end Formalism.ExtensionFiltration
