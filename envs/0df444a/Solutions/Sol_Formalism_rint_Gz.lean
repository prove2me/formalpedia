-- Prove2me | solution 1 for Formalism.rint_Gz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:28.836836+00:00
-- url     : https://prove2.me/submissions/77005871-8792-4d16-8c33-ae72017d2d52

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly
import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi
import Theorems.Thm_Formalism_Sz_eq_Sa
import Theorems.Thm_Formalism_vM_bound
import Theorems.Thm_Formalism_rint_of_abs


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
theorem _root_.solution (h3 : MellinSgen) (h5 : MellinElem) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun x : ℝ => Gz x * x ^ (-σ - 1)) (Ioi 1) := by
  have hS := h3 _ 1 vM_bound
  have a1 := rint_of_abs _ hS.1 σ (hS.2.1 σ hσ)
  have a2 := rint_of_abs (fun x => x * Real.log x) (by fun_prop) σ (h5.2.1 σ hσ)
  have a3 := h5.1 1 σ hσ
  have hfun : (fun x : ℝ => Gz x * x ^ (-σ - 1)) = fun x =>
      (Sa (fun n => Λ n) x * x ^ (-σ - 1) - (x * Real.log x) * x ^ (-σ - 1))
        + (1 + Real.eulerMascheroniConstant) * (x ^ (1:ℝ) * x ^ (-σ - 1)) := by
    funext x
    simp only [Gz, Sz_eq_Sa, Real.rpow_one]
    ring
  rw [hfun]
  exact Integrable.add (Integrable.sub a1 a2) (Integrable.const_mul a3 _)
end Formalism
