-- Prove2me | solution 1 for Formalism.mellin_H
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:46:33.154738+00:00
-- url     : https://prove2.me/submissions/29d60845-e8de-4737-abce-ffe79d468b84

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly
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
variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
namespace Formalism
theorem _root_.solution (h3 : MellinS) (h5 : MellinElem) (σ₀ C : ℝ) {s : ℂ} (hs : 1 < s.re)
    (hσ₀ : σ₀ < 1) :
    ∫ x in Ioi (1:ℝ), ((G χ x + C * x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) =
      LSeries (fun n => (LamF χ n : ℂ)) s / (s * (s - 1)) - 1 / (s - 1) ^ 2
        + (1 + gammaF χ) * (1 / (s - 1)) + C * (1 / (s - σ₀)) := by
  have hS := h3 N χ
  have i1 : IntegrableOn (fun x : ℝ => (S χ x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ hS.1 s (hS.2.1 _ hs)
  have i2 : IntegrableOn (fun x : ℝ => ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (h5.2.1 _ hs)
  have i3 : IntegrableOn (fun x : ℝ => ((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
  have i4 : IntegrableOn (fun x : ℝ => ((x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
  have hfun : (fun x : ℝ => ((G χ x + C * x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) =
      fun x => ((S χ x : ℂ) * (x : ℂ) ^ (-s - 1) - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
        + ((1 + gammaF χ : ℝ) : ℂ) * (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)))
        + (C : ℂ) * (((x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    simp only [G, Real.rpow_one]
    push_cast
    ring
  have j12 : IntegrableOn (fun x : ℝ => (S χ x : ℂ) * (x : ℂ) ^ (-s - 1)
      - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := Integrable.sub i1 i2
  have j3 : IntegrableOn (fun x : ℝ => ((1 + gammaF χ : ℝ) : ℂ) *
      (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) (Ioi 1) := Integrable.const_mul i3 _
  have j4 : IntegrableOn (fun x : ℝ => (C : ℂ) *
      (((x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) (Ioi 1) := Integrable.const_mul i4 _
  have j123 : IntegrableOn (fun x : ℝ => (S χ x : ℂ) * (x : ℂ) ^ (-s - 1)
      - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
      + ((1 + gammaF χ : ℝ) : ℂ) * (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) (Ioi 1) :=
    Integrable.add j12 j3
  rw [hfun, integral_add j123 j4, integral_add j12 j3, integral_sub i1 i2, integral_const_mul, integral_const_mul,
    hS.2.2 s hs, h5.2.2.2 s hs, h5.2.2.1 1 s (by simpa using hs), h5.2.2.1 σ₀ s (by linarith)]
  push_cast
  ring
end Formalism
