-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg.hom_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:18.239247+00:00
-- url     : https://prove2.me/submissions/a0f6a136-7c33-4547-9342-ab991605c58d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanDirAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
open NumberField Matrix
variable {E : Type} [Field E] [NumberField E] {κ : Type} [Fintype κ]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
theorem _root_.solution {R' : Type} [Ring R'] (f : 𝓞 E →+* R') (b : Module.Basis κ ℤ (𝓞 E)) (x : 𝓞 E) :
    f x = ∑ k, ((b.repr x k : ℤ) : R') * f (b k) := by
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, zsmul_eq_mul]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
