-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.jetTan_eq_tp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:45:27.721951+00:00
-- url     : https://prove2.me/submissions/03dda283-f193-40c8-ab1c-1a89603ffcd7

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
theorem _root_.solution {κ : Type} [DecidableEq κ] (ℓ : κ) :
    (jetTan ℓ : Jet R κ (0 + 1) →ₐ[R] DualNumber R) = tp (fun q => if q = ℓ then 1 else 0) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  show MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber R) else 0)
      (MvPolynomial.X i) =
    MvPolynomial.aeval (fun q => (TrivSqZeroExt.inr (if q = ℓ then 1 else 0) : DualNumber R))
      (MvPolynomial.X i)
  rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  by_cases h : i = ℓ
  · (simp only [if_pos h]) <;> rfl
  · simp only [if_neg h, TrivSqZeroExt.inr_zero]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
