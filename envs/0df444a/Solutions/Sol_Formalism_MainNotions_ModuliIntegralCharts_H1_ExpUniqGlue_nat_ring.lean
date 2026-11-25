-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue.nat_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:38.693285+00:00
-- url     : https://prove2.me/submissions/d011bff6-bdf0-4faa-9911-a9388591207e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_JetGlue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqGlue
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqGlue_base_change_jet_variable

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
attribute [local instance] Over.cartesianMonoidalCategory
variable {S T : Type} [CommRing S] [CommRing T] (f : S →+* T)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
theorem _root_.solution {κ : Type} {m : ℕ} {B B' : Type} [CommRing B] [Algebra S B] [CommRing B'] [Algebra T B']
    (ψ : Jet S κ m →ₐ[S] B) (ψ' : Jet T κ m →ₐ[T] B') (bB : B →+* B')
    (hB : ∀ s, bB (algebraMap S B s) = algebraMap T B' (f s)) (h : ∀ j, ψ' (zz m j) = bB (ψ (zz m j))) :
    (ψ' : Jet T κ m →+* B').comp (bcJ f κ m) = bB.comp (ψ : Jet S κ m →+* B) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro s
    have e1 : (Ideal.Quotient.mk (orig S κ ^ (m + 1)) (C s)) = algebraMap S (Jet S κ m) s := rfl
    simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, e1, bcJ_C, AlgHom.commutes, hB]
  · intro j
    have e2 : (Ideal.Quotient.mk (orig S κ ^ (m + 1)) (X j)) = zz m j := rfl
    simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, e2, base_change_jet_variable, h]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
