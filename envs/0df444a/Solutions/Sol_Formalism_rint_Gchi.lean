-- Prove2me | solution 1 for Formalism.rint_Gchi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:46:01.449659+00:00
-- url     : https://prove2.me/submissions/7ea1334f-b51e-4458-89d7-25e373221834

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly
import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi
import Theorems.Thm_Formalism_Schi_eq_Sa
import Theorems.Thm_Formalism_twist_bound
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
theorem _root_.solution (h3 : MellinSgen) (h5 : MellinElem) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun x : ℝ => Gchi χ x * x ^ (-σ - 1)) (Ioi 1) := by
  have hS := h3 _ 1 (twist_bound χ)
  have a1 := rint_of_abs _ hS.1 σ (hS.2.1 σ hσ)
  have a3 := h5.1 1 σ hσ
  have hfun : (fun x : ℝ => Gchi χ x * x ^ (-σ - 1)) = fun x =>
      Sa (fun n => Λ n * (χ n).re) x * x ^ (-σ - 1)
        + (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re
          * (x ^ (1:ℝ) * x ^ (-σ - 1)) := by
    funext x
    simp only [Gchi, Schi_eq_Sa, Real.rpow_one]
    ring
  rw [hfun]
  exact Integrable.add a1 (Integrable.const_mul a3 _)
end Formalism
