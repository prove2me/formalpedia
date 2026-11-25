-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.jetCoef_substP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:33:14.206127+00:00
-- url     : https://prove2.me/submissions/7f89ee02-902c-4935-adb4-20058372b810

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
theorem _root_.solution {V K : Type} [CommRing V] [CommRing K] (f : V →+* K) {κ κ' : Type} (m : ℕ)
    (φ : κ → MvPolynomial κ' V) :
    (jetCoef f κ' m).comp ((jetSubstP m φ : Jet V κ m →ₐ[V] Jet V κ' m) : Jet V κ m →+* Jet V κ' m) =
      ((jetSubstP m (fun i => MvPolynomial.map f (φ i)) : Jet K κ m →ₐ[K] Jet K κ' m) : Jet K κ m →+* Jet K κ' m).comp
        (jetCoef f κ m) := by
  have keyV : ∀ (ψ : κ → MvPolynomial κ' V) (j : κ),
      (jetSubstP m ψ : Jet V κ m →ₐ[V] Jet V κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X j)) =
        Ideal.Quotient.mk _ (ψ j - MvPolynomial.C (MvPolynomial.constantCoeff (ψ j))) := fun ψ j =>
    congrArg (Ideal.Quotient.mk _) (MvPolynomial.bind₁_X_right _ j)
  have keyK : ∀ (ψ : κ → MvPolynomial κ' K) (j : κ),
      (jetSubstP m ψ : Jet K κ m →ₐ[K] Jet K κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X j)) =
        Ideal.Quotient.mk _ (ψ j - MvPolynomial.C (MvPolynomial.constantCoeff (ψ j))) := fun ψ j =>
    congrArg (Ideal.Quotient.mk _) (MvPolynomial.bind₁_X_right _ j)
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro v
    have e2 : ∀ (κ'' : Type), jetCoef f κ'' m (algebraMap V (Jet V κ'' m) v) =
        algebraMap K (Jet K κ'' m) (f v) := by
      intro κ''
      show jetCoef f κ'' m (Ideal.Quotient.mk _ (MvPolynomial.C v)) = Ideal.Quotient.mk _ (MvPolynomial.C (f v))
      simp [jetCoef]
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
    rw [show (Ideal.Quotient.mk (orig V κ ^ (m + 1))) (MvPolynomial.C v) = algebraMap V (Jet V κ m) v from rfl]
    rw [AlgHom.commutes, e2, e2, AlgHom.commutes]
  · intro i
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
    rw [keyV φ i]
    have eX : jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.X i)) = Ideal.Quotient.mk _ (MvPolynomial.X i) := by
      simp [jetCoef]
    rw [eX, keyK]
    simp [jetCoef, MvPolynomial.constantCoeff_map]
end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
