-- Prove2me | solution 1 for Formalism.deriv_Pfun_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:45:20.585157+00:00
-- url     : https://prove2.me/submissions/8338636c-b250-4993-9698-6103d5941716

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly
import Theorems.Thm_Formalism_Pfun_eq_of_ne

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
theorem _root_.solution {s : ℂ} (hs : s ≠ 1) :
    deriv (Pfun χ) s = riemannZeta s * DirichletCharacter.LFunction χ s
      + (s - 1) * deriv riemannZeta s * DirichletCharacter.LFunction χ s
      + (s - 1) * riemannZeta s * deriv (DirichletCharacter.LFunction χ) s := by
  have heq : Pfun χ =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z * DirichletCharacter.LFunction χ z := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact Pfun_eq_of_ne χ hz
  rw [heq.deriv_eq]
  have h : HasDerivAt (fun z => (z - 1) * riemannZeta z * DirichletCharacter.LFunction χ z)
      ((1 * riemannZeta s + (s - 1) * deriv riemannZeta s) * DirichletCharacter.LFunction χ s +
        (s - 1) * riemannZeta s * deriv (DirichletCharacter.LFunction χ) s) s :=
    (((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt).mul
      (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).hasDerivAt
  rw [h.deriv]
  ring
end Formalism
