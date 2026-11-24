-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.exists_ps_of_jets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:28:02.859016+00:00
-- url     : https://prove2.me/submissions/63438f10-c41a-4d9e-b500-d8a9f44ce0c4

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetTrunc_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_mem_orig_pow_of
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_coeff_eq_zero_of_mem

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
theorem _root_.solution [Fintype ι] [DecidableEq ι] (a : ∀ m, Jet R ι m)
    (ha : ∀ m, (jetTrunc : Jet R ι (m + 1) →ₐ[R] Jet R ι m) (a (m + 1)) = a m) :
    ∃ f : MvPowerSeries ι R, ∀ m, psJet m f = a m := by
  choose p hp using fun k => Ideal.Quotient.mk_surjective (a k)
  have hc : ∀ k l, k ≤ l → p l - p k ∈ orig R ι ^ (k + 1) := by
    intro k l hkl
    induction l, hkl using Nat.le_induction with
    | base => simp
    | succ l hkl ih =>
      have h1 : p (l + 1) - p l ∈ orig R ι ^ (l + 1) := by
        rw [← Ideal.Quotient.eq]
        have h := ha l
        rw [← hp (l + 1), ← hp l, jetTrunc_mk] at h
        exact h
      have h2 : orig R ι ^ (l + 1) ≤ orig R ι ^ (k + 1) := Ideal.pow_le_pow_right (by omega)
      have h3 := Ideal.add_mem _ (h2 h1) ih
      rwa [sub_add_sub_cancel] at h3
  obtain ⟨f, hf⟩ : ∃ f : MvPowerSeries ι R, ∀ e, MvPowerSeries.coeff e f = MvPolynomial.coeff e (p e.degree) :=
    ⟨fun e => MvPolynomial.coeff e (p e.degree), fun e => rfl⟩
  refine ⟨f, fun k => ?_⟩
  rw [← hp k]
  unfold psJet
  rw [Ideal.Quotient.eq]
  apply mem_orig_pow_of
  intro e he
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, coeff_psTrunc_lemma_2] at he
  by_contra hlt
  have h1 : e.degree ≤ k := by omega
  rw [if_pos h1] at he
  apply he
  have h3 := coeff_eq_zero_of_mem (hc e.degree k h1) (by omega : e.degree < e.degree + 1)
  rw [MvPolynomial.coeff_sub, sub_eq_zero] at h3
  rw [hf, sub_eq_zero]
  exact h3.symm
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
