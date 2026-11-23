-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.mk_trunc_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:59:14.055434+00:00
-- url     : https://prove2.me/submissions/4dc8b6a1-b19b-4dac-a3ae-30775f689832

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]
private lemma mem_orig_pow_lemma_6 {ι : Type} (m : ℕ) (Q : MvPolynomial ι R)
    (hQ : ∀ e : ι →₀ ℕ, e.degree < m + 1 → MvPolynomial.coeff e Q = 0) :
    Q ∈ orig R ι ^ (m + 1) := by
  rw [Q.as_sum]
  refine Ideal.sum_mem _ fun e he => ?_
  have hd : m + 1 ≤ e.degree := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.1 he) (hQ e (by omega))
  rw [MvPolynomial.monomial_eq]
  refine Ideal.mul_mem_left _ _ ?_
  refine Ideal.pow_le_pow_right hd ?_
  have hX : ∀ i, (MvPolynomial.X i : MvPolynomial ι R) ∈ orig R ι := fun i => by
    first
    | exact Ideal.subset_span ⟨i, rfl⟩
    | (unfold orig; exact Ideal.subset_span ⟨i, rfl⟩)
  have h1 : (∏ i ∈ e.support, (MvPolynomial.X i : MvPolynomial ι R) ^ e i) ∈
      ∏ i ∈ e.support, orig R ι ^ e i :=
    Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hX i) _
  rw [Finset.prod_pow_eq_pow_sum] at h1
  first
  | exact h1
  | (unfold Finsupp.prod; simpa [Finsupp.degree] using h1)
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (P : MvPolynomial ι R) :
    (Ideal.Quotient.mk (orig R ι ^ (m + 1))
      (MvPowerSeries.truncTotal (m + 1) (P : MvPowerSeries ι R))) = Ideal.Quotient.mk _ P := by
  rw [Ideal.Quotient.eq]
  apply mem_orig_pow_lemma_6
  intro e he
  first
  | (rw [MvPolynomial.coeff_sub, MvPowerSeries.coeff_truncTotal, MvPolynomial.coeff_coe,
      sub_self] <;> exact he)
  | simp [MvPowerSeries.coeff_truncTotal, he]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
