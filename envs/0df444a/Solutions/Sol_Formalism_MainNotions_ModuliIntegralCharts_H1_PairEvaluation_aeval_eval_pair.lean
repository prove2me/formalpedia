-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.aeval_eval_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:37.026269+00:00
-- url     : https://prove2.me/submissions/62213869-f816-4384-8e09-228dcb779510

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
theorem _root_.solution {τ τ' : Type} (g : τ → MvPolynomial τ' S) (h : MvPolynomial (Fin 2 × Fin d) S)
    (u v : Fin d → MvPolynomial τ S) :
    aeval g (ev2 h u v) = ev2 h (fun i => aeval g (u i)) (fun i => aeval g (v i)) := by
  have hf : (fun p : Fin 2 × Fin d => aeval g (![u, v] p.1 p.2)) =
      (fun p : Fin 2 × Fin d => ![fun i => aeval g (u i), fun i => aeval g (v i)] p.1 p.2) := by
    funext p
    rcases p with ⟨k, i⟩
    fin_cases k <;> simp
  unfold ev2
  rw [← AlgHom.comp_apply, comp_aeval, hf]
end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
