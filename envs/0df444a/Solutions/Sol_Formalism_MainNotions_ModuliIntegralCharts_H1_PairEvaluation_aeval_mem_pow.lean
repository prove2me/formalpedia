-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.aeval_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:37.007808+00:00
-- url     : https://prove2.me/submissions/ec944ef1-8f1e-4a48-8dad-b43b809252fe

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
variable {σ τ : Type}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
theorem _root_.solution (g : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (k : ℕ) {p : MvPolynomial σ S}
    (hp : p ∈ Io S σ ^ k) : aeval g p ∈ Io S τ ^ k := by
  have h1 : Io S σ ≤ (Io S τ).comap (aeval g) := by
    show Ideal.span (Set.range X) ≤ _
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simpa using hg i
  exact (Ideal.le_comap_pow (f := aeval g) k) (Ideal.pow_right_mono h1 k hp)
end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
