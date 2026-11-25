-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.abel_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:04:42.128362+00:00
-- url     : https://prove2.me/submissions/a787eca5-94ea-4f3e-8cfa-0f5bb1f1c659

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperB
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_abel_identity
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_tele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
theorem _root_.solution (c : ℕ → ℂ) (w : ℕ → ℝ) (B : ℝ) (hA : ∀ m, ‖∑ n ∈ Ioc 0 m, c n‖ ≤ B)
    (U V : ℕ) (hUV : U ≤ V) (hw0 : 0 ≤ w (U + 1))
    (hw : ∀ n, U < n → 0 ≤ w (n + 1) ∧ w (n + 1) ≤ w n) :
    ‖∑ n ∈ Ioc U V, c n * (w n : ℂ)‖ ≤ 2 * B * w (U + 1) := by
  rw [abel_identity c w U V hUV]
  have hV : 0 ≤ w (V + 1) := by
    rcases hUV.lt_or_eq with h | h
    · exact (hw V h).1
    · rw [← h]; exact hw0
  have h1 : ‖(∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ)‖ ≤ B * w (V + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hV]
    exact mul_le_mul_of_nonneg_right (hA V) hV
  have h2 : ‖(∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ)‖ ≤ B * w (U + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_right (hA U) hw0
  have h3 : ‖∑ n ∈ Ioc U V, (∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ)‖ ≤
      B * (w (U + 1) - w (V + 1)) := by
    calc _ ≤ ∑ n ∈ Ioc U V, ‖(∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Ioc U V, B * (w n - w (n + 1)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn' : U < n := (Finset.mem_Ioc.mp hn).1
        have hd : 0 ≤ w n - w (n + 1) := by linarith [(hw n hn').2]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hd]
        exact mul_le_mul_of_nonneg_right (hA n) hd
      _ = B * (w (U + 1) - w (V + 1)) := by rw [← Finset.mul_sum, tele w U V hUV]
  have h4 := norm_add_le ((∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ) - (∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ))
    (∑ n ∈ Ioc U V, (∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ))
  have h5 := norm_sub_le ((∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ)) ((∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ))
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
