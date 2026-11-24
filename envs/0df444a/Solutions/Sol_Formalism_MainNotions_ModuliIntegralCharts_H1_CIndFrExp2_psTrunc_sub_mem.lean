-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2.psTrunc_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:42:44.034357+00:00
-- url     : https://prove2.me/submissions/f38c57aa-0eca-493e-8bb4-0524e0cecb2d

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_AevalDiagMonomial
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupLinearSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
variable {S : Type} [CommRing S] {d : ℕ}
private theorem mem_degLE_lemma {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ} {x : κ →₀ ℕ}
    (hx : x.degree ≤ n) : x ∈ degLE n := by
  have hle : ∀ i, x i ≤ n := by
    intro i
    by_cases hi : x i = 0
    · rw [hi]
      exact Nat.zero_le n
    · exact le_trans (Finset.single_le_sum (f := fun j => x j) (fun j _ => Nat.zero_le (x j))
        (Finsupp.mem_support_iff.2 hi)) hx
  unfold degLE
  rw [Finset.mem_filter, Finset.mem_image]
  refine ⟨⟨fun i => ⟨x i, Nat.lt_succ_of_le (hle i)⟩, Finset.mem_univ _, ?_⟩, hx⟩
  ext i
  simp
private theorem coeff_psTrunc_lemma_2 {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ S) (n : ℕ)
    (x : κ →₀ ℕ) : coeff x (psTrunc n f) = if x.degree ≤ n then MvPowerSeries.coeff x f else 0 := by
  unfold psTrunc
  rw [coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq', Finset.sum_ite_eq]
  by_cases h : x.degree ≤ n
  · rw [if_pos (mem_degLE_lemma h), if_pos h]
  · have h' : x ∉ degLE n := by
      intro h'
      unfold degLE at h'
      exact h (Finset.mem_filter.1 h').2
    rw [if_neg h', if_neg h]
private theorem mem_pow_Io_lemma_3 {κ : Type} (k : ℕ) (p : MvPolynomial κ S)
    (hp : ∀ x ∈ p.support, k ≤ x.degree) : p ∈ Io S κ ^ k := by
  have hX : ∀ i, (X i : MvPolynomial κ S) ∈ Io S κ := fun i => Ideal.subset_span ⟨i, rfl⟩
  rw [p.as_sum]
  refine Ideal.sum_mem _ fun x hx => ?_
  rw [monomial_eq]
  refine Ideal.mul_mem_left _ _ ?_
  have h2 : x.degree = ∑ a ∈ x.support, x a := by
    first
      | rfl
      | simp [Finsupp.degree]
  have h1 : (x.prod fun n e => (X n : MvPolynomial κ S) ^ e) ∈ Io S κ ^ x.degree := by
    unfold Finsupp.prod
    rw [h2, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun a _ => Ideal.pow_mem_pow (hX a) _
  exact Ideal.pow_le_pow_right (hp x hx) h1
section Poly
variable [Algebra ℚ S]
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
end Poly
section Act
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
end Act
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
variable {S : Type} [CommRing S] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ S) {k m : ℕ} (hkm : k ≤ m) :
    psTrunc m f - psTrunc k f ∈ Io S κ ^ (k + 1) := by
  apply mem_pow_Io_lemma_3
  intro x hx
  rw [mem_support_iff, coeff_sub, coeff_psTrunc_lemma_2, coeff_psTrunc_lemma_2] at hx
  by_contra hlt
  have h1 : x.degree ≤ k := by omega
  rw [if_pos (h1.trans hkm), if_pos h1, sub_self] at hx
  exact hx rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
