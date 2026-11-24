-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy.mk_psTrunc_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:40.722278+00:00
-- url     : https://prove2.me/submissions/7d4215d1-76e1-4875-b74c-2824a358f8e3

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)
section Alg
variable {S : Type} [CommRing S] (d : ℕ)
private theorem degree_eq_sum_lemma_2 {τ : Type} (e : τ →₀ ℕ) : e.degree = ∑ i ∈ e.support, e i := by
  first
  | rfl
  | simp [Finsupp.degree, Finsupp.sum]
private theorem le_degree_lemma_4 {τ : Type} (e : τ →₀ ℕ) (i : τ) : e i ≤ e.degree := by
  by_cases h : e i = 0
  · rw [h]; exact Nat.zero_le _
  · rw [degree_eq_sum_lemma_2]
    exact Finset.single_le_sum (f := fun j => e j) (fun _ _ => Nat.zero_le _)
      (Finsupp.mem_support_iff.2 h)
private theorem mem_degLE_lemma_6 {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) (e : τ →₀ ℕ) :
    e ∈ degLE m ↔ e.degree ≤ m := by
  unfold degLE
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨_, h⟩
    rw [degree_eq_sum_lemma_2]
    exact h
  · intro h
    refine ⟨⟨fun i => ⟨e i, by have := le_degree_lemma_4 e i; omega⟩, Finset.mem_univ _, ?_⟩, ?_⟩
    · ext i
      simp
    · rw [degree_eq_sum_lemma_2] at h
      exact h
private theorem coeff_psTrunc_lemma_7 {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ)
    (f : MvPowerSeries τ S) (e : τ →₀ ℕ) :
    coeff e (psTrunc m f) = if e.degree ≤ m then MvPowerSeries.coeff e f else 0 := by
  rw [psTrunc, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq', mem_degLE_lemma_6]
end Alg
section Axes
variable {S : Type} [CommRing S] (d : ℕ)
end Axes
section Frame
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
end Frame
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)
variable {S : Type} [CommRing S] (d : ℕ)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
theorem _root_.solution {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) (q : τ) :
    (Ideal.Quotient.mk (orig S τ ^ (m + 1)) (psTrunc m (MvPowerSeries.X q))) = Ideal.Quotient.mk _ (X q) := by
  have hdeg : (Finsupp.single q 1).degree = 1 := by
    rw [degree_eq_sum_lemma_2, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same]
  have hs : psTrunc m (MvPowerSeries.X q : MvPowerSeries τ S) = if 1 ≤ m then X q else 0 := by
    ext e
    rw [coeff_psTrunc_lemma_7, MvPowerSeries.coeff_X]
    by_cases h2 : e = Finsupp.single q 1
    · subst h2
      rw [hdeg]
      by_cases h3 : 1 ≤ m
      · simp [h3, MvPolynomial.coeff_X]
      · simp [h3]
    · have h4 : coeff e (X q : MvPolynomial τ S) = 0 := by
        rw [MvPolynomial.coeff_X']
        exact if_neg (Ne.symm h2)
      split_ifs <;> simp [h4, h2]
  rw [Ideal.Quotient.eq, hs]
  split_ifs with h
  · rw [sub_self]
    exact Ideal.zero_mem _
  · have hm : m = 0 := by omega
    subst hm
    rw [zero_sub, zero_add, pow_one]
    exact Ideal.neg_mem_iff _ |>.2 (Ideal.subset_span ⟨q, rfl⟩)
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
