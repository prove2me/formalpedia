-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.sL_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:33:26.436798+00:00
-- url     : https://prove2.me/submissions/4fc0b015-e03c-4991-8fca-2c14ea0b0bf0

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetMap_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetTrunc_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jet_hom_ext
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_psTrunc_succ_sub
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_power_series_in_fin_one
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
private theorem const_psTrunc_lemma_3 {κ : Type} [Fintype κ] [DecidableEq κ] (k : ℕ) (g : MvPowerSeries κ R) :
    MvPolynomial.constantCoeff (psTrunc k g) = MvPowerSeries.coeff 0 g := by
  rw [show MvPolynomial.constantCoeff (psTrunc k g) = MvPolynomial.coeff 0 (psTrunc k g) from rfl,
    coeff_psTrunc_lemma_2, if_pos (by simp)]
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
variable {R : Type} [CommRing R] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
theorem _root_.solution (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) R) :
    (jetTrunc : Jet R (Fin 1 × Fin d) (m + 1) →ₐ[R] _).comp (sL (m + 1) g) =
      (sL m g).comp (jetTrunc : Jet R (Fin 2 × Fin d) (m + 1) →ₐ[R] _) := by
  apply jet_hom_ext
  rintro ⟨k, j⟩
  simp only [AlgHom.comp_apply, jetTrunc_mk, sL, jetSubstP, jetMap_mk, MvPolynomial.aeval_X]
  rw [Ideal.Quotient.eq]
  fin_cases k
  · simp
  · simp only [power_series_in_fin_one, Matrix.cons_val_one, Matrix.head_cons]
    change psTrunc (m + 1) (g j) - C (MvPolynomial.constantCoeff (psTrunc (m + 1) (g j))) -
      (psTrunc m (g j) - C (MvPolynomial.constantCoeff (psTrunc m (g j)))) ∈ _
    rw [const_psTrunc_lemma_3, const_psTrunc_lemma_3, sub_sub_sub_cancel_right]
    exact psTrunc_succ_sub (g j)
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
