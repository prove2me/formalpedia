-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.sub_aug_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:30.028308+00:00
-- url     : https://prove2.me/submissions/c5a7d812-13f2-4b6c-92d8-cb2606451d27

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_augmentation_jet_variable

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
open MvPolynomial Formalism.L2.Pj
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
theorem _root_.solution {κ : Type} {m : ℕ} (p : Jet R κ m) :
    p - algebraMap R _ ((jetAug : Jet R κ m →ₐ[R] R) p) ∈ Ij R κ m := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective p
  induction P using MvPolynomial.induction_on
  next a =>
    have e : (Ideal.Quotient.mk (orig R κ ^ (m + 1)) (C a) : Jet R κ m) = algebraMap R _ a := rfl
    rw [e, AlgHom.commutes]
    simp
  next q r hq hr =>
    have h := Ideal.add_mem _ hq hr
    convert h using 1
    simp only [map_add]
    abel
  next q j _ =>
    have hz : (Ideal.Quotient.mk (orig R κ ^ (m + 1)) (X j) : Jet R κ m) ∈ Ij R κ m :=
      Ideal.subset_span ⟨j, rfl⟩
    have h0 : (jetAug : Jet R κ m →ₐ[R] R) (Ideal.Quotient.mk (orig R κ ^ (m + 1)) (X j)) = 0 :=
      augmentation_jet_variable m j
    rw [map_mul, map_mul, h0, mul_zero, map_zero, sub_zero]
    exact Ideal.mul_mem_left _ _ hz
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
