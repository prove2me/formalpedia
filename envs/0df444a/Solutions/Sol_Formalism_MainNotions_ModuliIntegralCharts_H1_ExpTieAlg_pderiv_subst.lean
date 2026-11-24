-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.pderiv_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:05:29.246195+00:00
-- url     : https://prove2.me/submissions/e178572d-dfd7-4d28-afd4-57aa878c3d46

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_continuous_pderiv_disc

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S : Type} [CommRing S]
open scoped MvPowerSeries.WithPiTopology
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
theorem _root_.solution {σ τ : Type} [Fintype σ] [DecidableEq σ] {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (t : τ) (g : MvPowerSeries σ S) :
    pderiv S t (subst a g) = ∑ s, subst a (pderiv S s g) * pderiv S t (a s) := by
  classical
  have hsa : ∀ x y : MvPowerSeries σ S, subst a (x + y) = subst a x + subst a y := fun x y => by
    rw [← coe_substAlgHom ha, map_add]
  have hm : ∀ x y : MvPowerSeries σ S, subst a (x * y) = subst a x * subst a y := fun x y => by
    rw [← coe_substAlgHom ha, map_mul]
  have hz : subst a (0 : MvPowerSeries σ S) = 0 := by
    rw [← coe_substAlgHom ha, map_zero]
  have h1 : subst a (1 : MvPowerSeries σ S) = 1 := by
    rw [← coe_substAlgHom ha, map_one]
  have hcC : ∀ c : S, subst a (C c : MvPowerSeries σ S) = C c := by
    intro c
    have hc : (C c : MvPowerSeries σ S) = c • (1 : MvPowerSeries σ S) := by
      rw [smul_eq_C_mul, mul_one]
    rw [hc, ← coe_substAlgHom ha, map_smul, map_one, smul_eq_C_mul, mul_one]
  have hpoly : ∀ p : MvPolynomial σ S, pderiv S t (subst a (p : MvPowerSeries σ S)) =
      ∑ s, subst a (pderiv S s (p : MvPowerSeries σ S)) * pderiv S t (a s) := by
    intro p
    induction p using MvPolynomial.induction_on
    next c =>
      simp [MvPolynomial.coe_C, hcC, pderiv_C, hz]
    next p q hp hq =>
      simp only [MvPolynomial.coe_add, map_add, hsa, add_mul, Finset.sum_add_distrib, hp, hq]
    next p n hp =>
      simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, hm, subst_X ha, Derivation.leibniz, smul_eq_mul,
        map_add, hsa, pderiv_X, add_mul, Finset.sum_add_distrib, hp, Pi.single_apply, apply_ite (subst a), h1, hz,
        mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Finset.mul_sum, mul_assoc, mul_ite, one_mul]
  letI : UniformSpace S := ⊥
  haveI : DiscreteUniformity S := by first | exact ⟨rfl⟩ | exact inferInstance
  haveI : DiscreteTopology S := by first | exact inferInstance | exact ⟨rfl⟩
  haveI : IsTopologicalRing S := by
    first
    | exact inferInstance
    | exact { continuous_add := continuous_of_discreteTopology, continuous_mul := continuous_of_discreteTopology, continuous_neg := continuous_of_discreteTopology }
  have hc1 : Continuous fun f : MvPowerSeries σ S => pderiv S t (subst a f) :=
    (continuous_pderiv_disc t).comp (MvPowerSeries.continuous_subst ha)
  have hc2 : Continuous fun f : MvPowerSeries σ S => ∑ s, subst a (pderiv S s f) * pderiv S t (a s) :=
    continuous_finset_sum _ fun s _ =>
      ((MvPowerSeries.continuous_subst ha).comp (continuous_pderiv_disc s)).mul continuous_const
  have heq := MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries.equalizer hc1 hc2 (funext hpoly)
  exact congrFun heq g
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
