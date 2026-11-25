-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.subst_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:05:21.789996+00:00
-- url     : https://prove2.me/submissions/557b3a4f-1c50-4fbf-a59d-27100d9862e8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_mem_subV

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
open MvPowerSeries
variable {σ : Type}
variable {k : Type} [CommRing k]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
theorem _root_.solution {τ : Type} {V : Set σ} (a : τ → MvPowerSeries σ k) (ha : HasSubst a)
    (haV : ∀ t, a t ∈ subV k V) (f : MvPowerSeries τ k) : subst a f ∈ subV k V := by
  rw [mem_subV]
  intro e he j hj
  rw [coeff_subst ha] at he
  obtain ⟨d, hd⟩ : ∃ d : τ →₀ ℕ, coeff d f • coeff e (d.prod fun s n => a s ^ n) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact he (by simp only [hcon, finsum_zero])
  have hP : (d.prod fun s n => a s ^ n) ∈ subV k V := by
    unfold Finsupp.prod
    exact Subalgebra.prod_mem _ (fun s _ => Subalgebra.pow_mem _ (haV s) _)
  rw [smul_eq_mul] at hd
  exact (mem_subV V _).1 hP e (right_ne_zero_of_mul hd) j hj
end Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
