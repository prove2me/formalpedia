-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf.eq_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:42:51.810809+00:00
-- url     : https://prove2.me/submissions/d9ff440e-2f82-4f75-8601-f38b19e5c3bb

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpAct
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpActPf
import Theorems.Thm_Formalism_FG_SolveVAux_degree_eq_one


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ExpTieAlg
variable {S : Type} [CommRing S]
open Formalism.FG.SolveVAux
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf
theorem _root_.solution {N : ℕ} (g : MvPowerSeries (Fin 1 × Fin N) S)
    (h : ∀ n : Fin 1 × Fin N →₀ ℕ, n.degree ≠ 1 → coeff n g = 0) :
    g = ∑ q, C (coeff (Finsupp.single ((0 : Fin 1), q) 1) g) * X ((0 : Fin 1), q) := by
  classical
  ext n
  rw [map_sum]
  by_cases hn : n.degree = 1
  · obtain ⟨⟨i, q⟩, rfl⟩ := degree_eq_one n hn
    fin_cases i
    rw [Finset.sum_eq_single q]
    · simp [coeff_X]
    · intro b _ hb
      rw [coeff_C_mul, coeff_X, if_neg, mul_zero]
      intro e
      apply hb
      have := Finsupp.single_left_injective one_ne_zero e
      simp only [Prod.mk.injEq] at this
      exact this.2.symm
    · simp
  · rw [h n hn]
    symm
    apply Finset.sum_eq_zero
    intro q _
    rw [coeff_C_mul, coeff_X, if_neg, mul_zero]
    rintro rfl
    exact hn (by simp [Finsupp.degree_single])
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf
