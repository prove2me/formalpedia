-- Prove2me | solution 1 for Formalism.mellin_Gz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:05.892476+00:00
-- url     : https://prove2.me/submissions/42129019-9887-490d-a453-04b882319b8e

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly
import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi
import Theorems.Thm_Formalism_Sz_eq_Sa
import Theorems.Thm_Formalism_vM_bound
import Theorems.Thm_Formalism_cint_of_abs
import Theorems.Thm_Formalism_int_abs_rpow


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
theorem _root_.solution (h3 : MellinSgen) (h5 : MellinElem) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (Gz x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1:ℝ), (Gz x : ℂ) * (x : ℂ) ^ (-s - 1) =
      (-deriv riemannZeta s / riemannZeta s) / (s * (s - 1)) - 1 / (s - 1) ^ 2
        + (1 + (Real.eulerMascheroniConstant : ℂ)) * (1 / (s - 1)) := by
  have hS := h3 _ 1 vM_bound
  have i1 : IntegrableOn (fun x : ℝ => (Sa (fun n => Λ n) x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ hS.1 s (hS.2.1 _ hs)
  have i2 := cint_of_abs (fun x => x * Real.log x) (by fun_prop) s (h5.2.1 _ hs)
  have i3 : IntegrableOn (fun x : ℝ => ((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
  have hfun : (fun x : ℝ => (Gz x : ℂ) * (x : ℂ) ^ (-s - 1)) = fun x =>
      ((Sa (fun n => Λ n) x : ℂ) * (x : ℂ) ^ (-s - 1)
        - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
        + ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) *
          (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    simp only [Gz, Sz_eq_Sa, Real.rpow_one]
    push_cast
    ring
  have j12 : IntegrableOn (fun x : ℝ => (Sa (fun n => Λ n) x : ℂ) * (x : ℂ) ^ (-s - 1)
        - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := Integrable.sub i1 i2
  have j3 := Integrable.const_mul i3 ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ)
  refine ⟨by rw [hfun]; exact j12.add j3, ?_⟩
  rw [hfun, integral_add j12 j3, integral_sub i1 i2, integral_const_mul, hS.2.2 s hs,
    h5.2.2.2 s hs, h5.2.2.1 1 s (by simpa using hs)]
  have hL : LSeries (fun n => ((Λ n : ℝ) : ℂ)) s = -deriv riemannZeta s / riemannZeta s :=
    LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [hL]
  push_cast
  ring
end Formalism
