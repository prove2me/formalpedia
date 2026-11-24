-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.monomial_mem_orig_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:47:57.735491+00:00
-- url     : https://prove2.me/submissions/ee925992-45f4-44ce-8e4f-f9f750c968e2

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open AlgebraicGeometry CategoryTheory MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun ReciprocityTheory.ChartRestriction.G.Geo.Tor
section Alg
variable {R : Type} [CommRing R] {ι : Type} {m : ℕ}
private theorem deg_sum_lemma {κ : Type} (e : κ →₀ ℕ) : e.degree = ∑ i ∈ e.support, e i := by
  first
  | rfl
  | simp [Finsupp.degree]
  | exact Finsupp.degree_apply e
end Alg
section Subst
variable {R : Type} [CommRing R] {d : ℕ}
end Subst
section Over
variable {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
end Over
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open AlgebraicGeometry CategoryTheory MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] {ι : Type} {m : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
theorem _root_.solution (e : ι →₀ ℕ) (c : R) : monomial e c ∈ orig R ι ^ e.degree := by
  classical
  rw [MvPolynomial.monomial_eq, Finsupp.prod]
  refine Ideal.mul_mem_left _ _ ?_
  rw [deg_sum_lemma e, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (X_mem_orig i) _
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
