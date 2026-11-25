-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.Sym.GoodPair.iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:10:19.295877+00:00
-- url     : https://prove2.me/submissions/9213cf58-19e9-4783-8730-940500f751d7

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LegendreSumSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CPfSym
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_Sym_ordGE_zero
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_Sym_ordGE_add

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.Sym
variable {k : Type} [CommRing k] {σ : Type}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.Sym
namespace GoodPair
theorem _root_.solution {D D₀ : MvPowerSeries σ k → MvPowerSeries σ k} (hP : GoodPair D D₀) (c : ℕ) :
    ∀ r g, OrdGE (c + r) g →
      OrdGE (r + 1) (D^[c] g - D₀^[c] g) ∧ OrdGE r (D^[c] g) ∧ OrdGE r (D₀^[c] g) := by
  induction c with
  | zero =>
    intro r g hg
    rw [zero_add] at hg
    refine ⟨?_, hg, hg⟩
    have e : D^[0] g - D₀^[0] g = 0 := sub_self g
    rw [e]
    exact ordGE_zero _
  | succ n ih =>
    intro r g hg
    obtain ⟨h1, h2, h3⟩ := ih (r + 1) g (by rwa [show n + (r + 1) = n + 1 + r by omega])
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine ⟨?_, hP.ord r _ h2, hP.ord₀ r _ h3⟩
    have e : D (D^[n] g) - D₀ (D₀^[n] g) = D (D^[n] g - D₀^[n] g) + (D (D₀^[n] g) - D₀ (D₀^[n] g)) := by
      rw [hP.sub]
      abel
    rw [e]
    exact ordGE_add (hP.ord (r + 1) _ h1) (hP.diff r _ h3)
end GoodPair
end Formalism.MainNotions.ModuliIntegralCharts.H1.Sym
