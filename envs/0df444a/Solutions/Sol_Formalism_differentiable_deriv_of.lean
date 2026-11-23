-- Prove2me | solution 1 for Formalism.differentiable_deriv_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:04.934977+00:00
-- url     : https://prove2.me/submissions/8b62a07f-0ca7-4b93-bd77-c2799d553b28

import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi
import Definitions.Def_Formalism_ZetaNonvanishing_RiemannZetaOneNeZeroOfRealMemIoo

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
  (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ)
namespace Formalism
theorem _root_.solution {f : ℂ → ℂ} (hf : Differentiable ℂ f) : Differentiable ℂ (deriv f) :=
  fun z => ((analyticOnNhd_univ_iff_differentiable.mpr hf).deriv z trivial).differentiableAt
end Formalism
