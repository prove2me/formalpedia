-- Prove2me | solution 1 for Formalism.Gz_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:39.022451+00:00
-- url     : https://prove2.me/submissions/f685851f-7f32-44dd-82c7-025bc2709fc5

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt
import Definitions.Def_Formalism_ZetaNonvanishing_LandauEq
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZetaNonvanishing_MellinElem
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LogDerivZeroFree
import Definitions.Def_Formalism_ZetaNonvanishing_MellinDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Theorems.Thm_Formalism_Sz_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open ArithmeticFunction
namespace Formalism
theorem _root_.solution {X : ℝ} (hX : 1 ≤ X) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x → x ≤ X → |Gz x| ≤ B := by
  have hγ : 0 ≤ Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hS0 : 0 ≤ X * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Λ n :=
    mul_nonneg (by linarith) (Finset.sum_nonneg fun n _ => vonMangoldt_nonneg)
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
  refine ⟨X * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Λ n + X * Real.log X
      + (1 + Real.eulerMascheroniConstant) * X, by positivity, ?_⟩
  intro x hx1 hxX
  obtain ⟨hS1, hS2⟩ := Sz_bound hx1 hxX
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hl1 : Real.log x ≤ Real.log X := Real.log_le_log (by linarith) hxX
  have hxl : x * Real.log x ≤ X * Real.log X := mul_le_mul hxX hl1 hl0 (by linarith)
  have hxl0 : 0 ≤ x * Real.log x := mul_nonneg (by linarith) hl0
  have hg : (1 + Real.eulerMascheroniConstant) * x ≤ (1 + Real.eulerMascheroniConstant) * X :=
    mul_le_mul_of_nonneg_left hxX (by linarith)
  have hg0 : 0 ≤ (1 + Real.eulerMascheroniConstant) * x := mul_nonneg (by linarith) (by linarith)
  unfold Gz
  rw [abs_le]
  constructor <;> nlinarith
end Formalism
