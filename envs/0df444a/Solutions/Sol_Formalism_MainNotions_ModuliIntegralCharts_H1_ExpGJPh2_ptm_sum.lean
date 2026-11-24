-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2.ptm_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:06:57.587357+00:00
-- url     : https://prove2.me/submissions/7ad06d60-62d7-4e76-bf45-e07a3f6932d9

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhOneValSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhTwoValHolds
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGJPh2_subst_psIn
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_const_substPS
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_ptm_congr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_ptm_subst
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_cc_psTrunc__670d9e4bd30f
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_const__a_6a1787d574a4
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_law__a_b638aaa98346


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
set_option maxHeartbeats 1000000
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2
theorem _root_.solution (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hexp : IsExpOf C.B.G.F C.uvec φ) (m : ℕ) (u0 u1 u2 : 𝓞 E) :
    ptm C (P3 C φ u0 u1 u2) m ≫ homAt y.x (jetSubstP m (σS C m)) =
      ptm C ![φa c φ u0, φa c φ (u1 + u2)] m := by
  have hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0 := hexp.const
  have hP : ∀ i j, MvPowerSeries.constantCoeff (P3 C φ u0 u1 u2 i j) = 0 := fun i j => const_φa c φ hφ _ j
  have hσ : ∀ p : Fin 2 × Fin C.d, MvPolynomial.constantCoeff (σS C m p) = 0 := by
    rintro ⟨i, j⟩
    rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with h | h <;> subst h
    · simp
    · show MvPolynomial.constantCoeff (psIn C.d m ![1, 2] (C.B.G.F j)) = 0
      rw [psIn, MvPolynomial.constantCoeff_rename, ExpGB.cc_psTrunc', C.B.G.const]
  rw [ptm_subst C (P3 C φ u0 u1 u2) hP m (σS C m) hσ]
  refine ptm_congr C (P := fun i j => MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2)
      ((σS C m (i, j) : MvPolynomial _ S) : MvPowerSeries (Fin 3 × Fin C.d) S))
    (P' := ![φa c φ u0, φa c φ (u1 + u2)])
    (fun i j => const_substPS (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2)
      (fun p : Fin 3 × Fin C.d => hP p.1 p.2) _ ?_)
    ?_ m ?_
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
    exact hσ (i, j)
  · rw [Fin.forall_fin_two]
    exact ⟨fun j => const_φa c φ hφ _ j, fun j => const_φa c φ hφ _ j⟩
  · rw [Fin.forall_fin_two]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · show psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2)
          ((MvPolynomial.X ((0 : Fin 3), j) : MvPolynomial _ S) : MvPowerSeries _ S)) = _
      rw [MvPolynomial.coe_X, MvPowerSeries.subst_X (a := fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2)
        (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p : Fin 3 × Fin C.d => hP p.1 p.2))]
      rfl
    · show psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2)
          ((psIn C.d m (![1, 2] : Fin 2 → Fin 3) (C.B.G.F j) : MvPolynomial (Fin 3 × Fin C.d) S) :
            MvPowerSeries (Fin 3 × Fin C.d) S)) = _
      rw [subst_psIn m ![1, 2] (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2)
        (fun p : Fin 3 × Fin C.d => hP p.1 p.2) (C.B.G.F j)]
      have hfun : (fun p : Fin 2 × Fin C.d => (fun q : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 q.1 q.2)
          ((![1, 2] : Fin 2 → Fin 3) p.1, p.2)) = fun p : Fin 2 × Fin C.d => φa c φ (![u1, u2] p.1) p.2 := by
        funext p
        obtain ⟨i, k⟩ := p
        rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with h | h <;> subst h <;> rfl
      refine (congrArg (fun Q => psJet m (MvPowerSeries.subst Q (C.B.G.F j))) hfun).trans ?_
      rw [law_φa c hexp u1 u2 j]
      rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2
