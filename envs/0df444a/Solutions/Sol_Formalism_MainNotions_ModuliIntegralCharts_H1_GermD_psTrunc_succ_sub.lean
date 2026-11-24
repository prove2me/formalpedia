-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.psTrunc_succ_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:21.158557+00:00
-- url     : https://prove2.me/submissions/f973b583-9494-44f3-8499-4fc0421addfe

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_mem_orig_pow_of
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
private theorem mem_degLE_lemma [Fintype ι] [DecidableEq ι] (k : ℕ) (e : ι →₀ ℕ) :
    e ∈ degLE k ↔ e.degree ≤ k := by
  unfold degLE
  rw [Finset.mem_filter, deg_sum_lemma]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨Finset.mem_image.2 ⟨fun i => ⟨e i, ?_⟩, Finset.mem_univ _, ?_⟩, h⟩
    · have hle : e i ≤ ∑ j ∈ e.support, e j := by
        by_cases hi : i ∈ e.support
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        · have h0 : e i = 0 := by simpa [Finsupp.mem_support_iff] using hi
          rw [h0]
          exact Nat.zero_le _
      omega
    · ext i
      simp
private theorem coeff_psTrunc_lemma_2 [Fintype ι] [DecidableEq ι] (k : ℕ) (g : MvPowerSeries ι R)
    (e : ι →₀ ℕ) :
    MvPolynomial.coeff e (psTrunc k g) = if e.degree ≤ k then MvPowerSeries.coeff e g else 0 := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : e.degree ≤ k
  · rw [if_pos ((mem_degLE_lemma k e).2 h), if_pos h]
  · rw [if_neg (mt (mem_degLE_lemma k e).1 h), if_neg h]
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
theorem _root_.solution [Fintype ι] [DecidableEq ι] (g : MvPowerSeries ι R) :
    psTrunc (m + 1) g - psTrunc m g ∈ orig R ι ^ (m + 1) := by
  apply mem_orig_pow_of
  intro e he
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, coeff_psTrunc_lemma_2, coeff_psTrunc_lemma_2] at he
  by_contra hlt
  have h1 : e.degree ≤ m := by omega
  rw [if_pos h1, if_pos (by omega : e.degree ≤ m + 1), sub_self] at he
  exact he rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
