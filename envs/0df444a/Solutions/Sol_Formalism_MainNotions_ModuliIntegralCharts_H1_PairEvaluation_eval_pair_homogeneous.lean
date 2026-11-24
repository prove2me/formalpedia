-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.eval_pair_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:15.195862+00:00
-- url     : https://prove2.me/submissions/76440523-8b72-42ad-9ada-b11cf95e8ad4

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
theorem _root_.solution {τ : Type} {h : MvPolynomial (Fin 2 × Fin d) S} {j : ℕ} (hh : h.IsHomogeneous j)
    (u v : Fin d → MvPolynomial τ S) (hu : ∀ i, (u i).IsHomogeneous 1) (hv : ∀ i, (v i).IsHomogeneous 1) :
    (ev2 h u v).IsHomogeneous j := by
  have := hh.aeval (fun p : Fin 2 × Fin d => ![u, v] p.1 p.2) (n := 1)
    (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv])
  rw [one_mul] at this
  exact this
end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
