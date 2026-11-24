-- Prove2me | solution 1 for Formalism.L2.SG.Pf.WuDec.continuous_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:26:06.831658+00:00
-- url     : https://prove2.me/submissions/e639201d-5a91-4a82-ba6d-9eaab7ac4f0f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_TensInt
import Theorems.Thm_Formalism_L2_SG_Pf_WuDec_norm_sub_tens_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.WuDec
variable {ι : Type} [Fintype ι] {V : ι → Type} [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
  {Vπ : Type} [NormedAddCommGroup Vπ] [InnerProductSpace ℂ Vπ] {tens : (∀ v, V v) → Vπ}
namespace Formalism.L2.SG.Pf.WuDec
theorem _root_.solution [∀ v, FiniteDimensional ℂ (V v)] (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) :
    Continuous tens := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have p : ∀ v, Continuous fun y : (∀ v, V v) => y v := fun v => _root_.continuous_apply v
  have hF : Continuous fun y : (∀ v, V v) => RCLike.re ((∏ v, ⟪y v, y v⟫_ℂ) - (∏ v, ⟪y v, x v⟫_ℂ) -
      (∏ v, ⟪x v, y v⟫_ℂ) + (∏ v, ⟪x v, x v⟫_ℂ)) := by
    refine RCLike.continuous_re.comp
      (Continuous.add (Continuous.sub (Continuous.sub ?_ ?_) ?_) continuous_const)
    · exact continuous_finset_prod _ fun v _ => (p v).inner (p v)
    · exact continuous_finset_prod _ fun v _ => (p v).inner continuous_const
    · exact continuous_finset_prod _ fun v _ => continuous_const.inner (p v)
  have h2 : Filter.Tendsto (fun y => ‖tens y - tens x‖ ^ 2) (nhds x) (nhds 0) := by
    have e : (fun y => ‖tens y - tens x‖ ^ 2) = fun y : (∀ v, V v) =>
        RCLike.re ((∏ v, ⟪y v, y v⟫_ℂ) - (∏ v, ⟪y v, x v⟫_ℂ) - (∏ v, ⟪x v, y v⟫_ℂ) +
          (∏ v, ⟪x v, x v⟫_ℂ)) :=
      funext fun y => norm_sub_tens_sq hi y x
    rw [e]
    convert hF.tendsto x using 2
    simp
  have h3 := h2.sqrt
  simp only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at h3
  exact h3
end Formalism.L2.SG.Pf.WuDec
