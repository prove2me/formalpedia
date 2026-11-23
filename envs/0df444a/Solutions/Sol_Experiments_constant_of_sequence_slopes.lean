-- Prove2me | solution 1 for Experiments.constant_of_sequence_slopes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:01:35.813006+00:00
-- url     : https://prove2.me/submissions/d3d5420c-1d22-49ec-86fe-14694726c6ca

import Definitions.Def_Experiments_GeneratorBound
import Definitions.Def_Experiments_FiniteDifferenceSemigroup

set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
noncomputable section
open Experiments
namespace Experiments
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {h : ℕ → ℝ} (hpos : ∀ n, 0 < h n)
    (hz : Tendsto h atTop (𝓝 0)) {t : ℝ} (ht : 0 ≤ t)
    (hcont : ContinuousOn f (Icc 0 t))
    (hquot : ∀ x ∈ Ico 0 t,
      Tendsto (fun n => (h n)⁻¹ • (f (x + h n) - f x)) atTop (𝓝 0)) :
    f t = f 0 := by
  let g := fun x => ‖f x - f 0‖
  have hg : ContinuousOn g (Icc 0 t) := (hcont.sub continuousOn_const).norm
  have hsmall : ∀ x ∈ Ico 0 t, ∀ r : ℝ, 0 < r →
      ∃ᶠ z in 𝓝[>] x, slope g x z < r := by
    intro x hx r hr
    have hright : Tendsto (fun n => x + h n) atTop (𝓝[>] x) :=
      tendsto_nhdsWithin_iff.mpr ⟨by simpa using tendsto_const_nhds.add hz,
        Eventually.of_forall fun n => by simpa using hpos n⟩
    have hevent : ∀ᶠ n in atTop, ‖(h n)⁻¹ • (f (x + h n) - f x)‖ < r :=
      (hquot x hx).norm.eventually (gt_mem_nhds (by simpa using hr))
    apply hright.frequently
    apply hevent.frequently.mono
    intro n hn
    calc
      slope g x (x + h n) =
          (h n)⁻¹ * (‖f (x + h n) - f 0‖ - ‖f x - f 0‖) := by
        simp [slope_def_module, g]
      _ ≤ (h n)⁻¹ * ‖f (x + h n) - f x‖ := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hpos n).le)
        simpa using norm_sub_norm_le (f (x + h n) - f 0) (f x - f 0)
      _ = ‖(h n)⁻¹ • (f (x + h n) - f x)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hpos n)]
      _ < r := hn
  have hbound := image_le_of_liminf_slope_right_le_deriv_boundary
    (B := fun _ => 0) (B' := fun _ => 0) hg
    (show g 0 ≤ 0 by simp [g]) continuousOn_const
    (fun x _ => (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt)
    (fun x hx r hr => hsmall x hx r hr)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (hbound ⟨ht, le_rfl⟩))
end Experiments
