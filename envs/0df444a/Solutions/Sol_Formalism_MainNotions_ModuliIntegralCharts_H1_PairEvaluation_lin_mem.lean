-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.lin_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:57.344597+00:00
-- url     : https://prove2.me/submissions/5ae4cc80-9567-4515-8d40-da2fbc106d24

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
open MvPolynomial
variable {S : Type} [CommRing S] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
theorem _root_.solution {n : ℕ} (A : Fin d → Fin d → S) (k : Fin n) (i : Fin d) : lin A k i ∈ Io S (Fin n × Fin d) :=
  Ideal.sum_mem _ fun _ _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)
end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
