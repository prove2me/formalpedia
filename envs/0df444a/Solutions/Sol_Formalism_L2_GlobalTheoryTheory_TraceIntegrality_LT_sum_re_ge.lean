-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT.sum_re_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:16:37.007512+00:00
-- url     : https://prove2.me/submissions/b109837e-c260-4a76-b776-49a71a64325e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL4_PLemTAmgm
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_LT_abs_norm_eq_prod_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.TraceIntegrality Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
theorem _root_.solution (a : E) (hpos : ∀ φ : E →+* ℂ, ∃ c : ℝ, 0 < c ∧ φ a = c) (X : ℝ) (hX : 0 < X)
    (h1 : 1 ≤ |((Algebra.norm ℚ a : ℚ) : ℝ)| * X) :
    (Module.finrank ℚ E : ℝ) * X ^ (-(1 / (Module.finrank ℚ E : ℝ))) ≤ ∑ φ : E →+* ℂ, (φ a).re := by
  set d : ℝ := ((Module.finrank ℚ E : ℕ) : ℝ) with hd
  have hcard : (Fintype.card (E →+* ℂ) : ℝ) = d := by rw [hd, Embeddings.card]
  have hd0 : 0 < d := by rw [hd]; exact_mod_cast Module.finrank_pos
  have hc : ∀ φ : E →+* ℂ, 0 < (φ a).re := by
    intro φ
    obtain ⟨c, hc, he⟩ := hpos φ
    rw [he, Complex.ofReal_re]; exact hc
  have hP : ∏ φ : E →+* ℂ, (φ a).re = |((Algebra.norm ℚ a : ℚ) : ℝ)| := (abs_norm_eq_prod_re a hpos).symm
  have hPX : X⁻¹ ≤ ∏ φ : E →+* ℂ, (φ a).re := by
    rw [hP, inv_le_iff_one_le_mul₀ hX, mul_comm]; linarith
  have hgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (E →+* ℂ)) (fun _ ↦ 1 / d)
    (fun φ ↦ (φ a).re) (fun _ _ ↦ by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; field_simp)
    (fun φ _ ↦ (hc φ).le)
  rw [Real.finsetProd_rpow _ _ (fun φ _ ↦ (hc φ).le), ← Finset.mul_sum] at hgm
  have hmono : X⁻¹ ^ (1 / d) ≤ (∏ φ : E →+* ℂ, (φ a).re) ^ (1 / d) :=
    Real.rpow_le_rpow (by positivity) hPX (by positivity)
  rw [Real.inv_rpow hX.le, ← Real.rpow_neg hX.le] at hmono
  calc d * X ^ (-(1 / d)) ≤ d * (1 / d * ∑ φ : E →+* ℂ, (φ a).re) := by gcongr; exact hmono.trans hgm
    _ = _ := by field_simp
end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
