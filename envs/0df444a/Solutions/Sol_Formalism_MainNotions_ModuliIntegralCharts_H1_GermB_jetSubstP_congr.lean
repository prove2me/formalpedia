-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.jetSubstP_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:48.078162+00:00
-- url     : https://prove2.me/submissions/471ea190-f1ea-4d13-95cd-d2b944dda2e6

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {κ κ' : Type}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
theorem _root_.solution (m : ℕ) (φ ψ : κ → MvPolynomial κ' S) (h : ∀ i, φ i - ψ i ∈ orig S κ' ^ (m + 1)) :
    (jetSubstP m φ : Jet S κ m →ₐ[S] Jet S κ' m) = jetSubstP m ψ := by
  unfold jetSubstP jetMap
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  rw [Ideal.Quotient.eq]
  have hc : MvPolynomial.constantCoeff (φ i) = MvPolynomial.constantCoeff (ψ i) := by
    have h1 : φ i - ψ i ∈ orig S κ' := Ideal.pow_le_self (Nat.succ_ne_zero m) (h i)
    have h2 : orig S κ' ≤ RingHom.ker (MvPolynomial.constantCoeff (R := S) (σ := κ')) := by
      unfold orig
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      simp
    have h3 := h2 h1
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h3
    exact h3
  rw [hc]
  convert h i using 1
  ring
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
