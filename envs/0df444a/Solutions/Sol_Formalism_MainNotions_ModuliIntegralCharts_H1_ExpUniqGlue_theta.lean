-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue.theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:41:05.603802+00:00
-- url     : https://prove2.me/submissions/c0ca3824-083e-44a8-aa95-ae0432f4ac01

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_JetGlue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqGlue

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
theorem _root_.solution {S : Type} [CommRing S] (p : Ideal S) [p.IsPrime] (κ : Type) (m : ℕ) :
    ∃ θ : Jet (Localization.AtPrime p) κ m →+* ReciprocityTheory.ChartRestriction.G.TB.JetLoc S κ m p,
      θ.comp (bcJ (algebraMap S (Localization.AtPrime p)) κ m) =
        algebraMap (ReciprocityTheory.ChartRestriction.G.TB.JetRing S κ m) (ReciprocityTheory.ChartRestriction.G.TB.JetLoc S κ m p) := by
  classical
  have hu : ∀ y : p.primeCompl, IsUnit (((algebraMap (ReciprocityTheory.ChartRestriction.G.TB.JetRing S κ m)
      (ReciprocityTheory.ChartRestriction.G.TB.JetLoc S κ m p)).comp (algebraMap S (ReciprocityTheory.ChartRestriction.G.TB.JetRing S κ m))) y) :=
    fun y => IsLocalization.map_units (ReciprocityTheory.ChartRestriction.G.TB.JetLoc S κ m p)
      (⟨algebraMap S (ReciprocityTheory.ChartRestriction.G.TB.JetRing S κ m) y, by
        first
        | exact Algebra.mem_algebraMapSubmonoid_of_mem y
        | exact Submonoid.mem_map_of_mem _ y.2⟩ :
        Algebra.algebraMapSubmonoid (ReciprocityTheory.ChartRestriction.G.TB.JetRing S κ m) p.primeCompl)
  let g : Localization.AtPrime p →+* ReciprocityTheory.ChartRestriction.G.TB.JetLoc S κ m p :=
    IsLocalization.lift (M := p.primeCompl) hu
  let F : MvPolynomial κ (Localization.AtPrime p) →+* ReciprocityTheory.ChartRestriction.G.TB.JetLoc S κ m p :=
    MvPolynomial.eval₂Hom g fun j => algebraMap (ReciprocityTheory.ChartRestriction.G.TB.JetRing S κ m)
      (ReciprocityTheory.ChartRestriction.G.TB.JetLoc S κ m p)
      (Ideal.Quotient.mk (Ideal.span (Set.range (X : κ → MvPolynomial κ S)) ^ (m + 1)) (X j))
  have hF : ∀ a ∈ orig (Localization.AtPrime p) κ ^ (m + 1), F a = 0 := by
    intro a ha
    have h1 : F a ∈ Ideal.map F (orig (Localization.AtPrime p) κ ^ (m + 1)) := Ideal.mem_map_of_mem _ ha
    rw [map_orig_pow] at h1
    have h3 : Ideal.span (Set.range fun i => F (X i)) =
        Ideal.map (algebraMap (ReciprocityTheory.ChartRestriction.G.TB.JetRing S κ m) (ReciprocityTheory.ChartRestriction.G.TB.JetLoc S κ m p))
          (Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range (X : κ → MvPolynomial κ S)) ^ (m + 1)))
            (Ideal.span (Set.range (X : κ → MvPolynomial κ S)))) := by
      rw [Ideal.map_map, Ideal.map_span, ← Set.range_comp]
      congr 1
      congr 1
      funext i
      simp [F]
    rw [h3, ← Ideal.map_pow, ← Ideal.map_pow, Ideal.map_quotient_self, Ideal.map_bot] at h1
    exact (Submodule.mem_bot _).1 h1
  refine ⟨Ideal.Quotient.lift _ F hF, ?_⟩
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro s
    show F (MvPolynomial.map (algebraMap S (Localization.AtPrime p)) (C s)) = _
    rw [MvPolynomial.map_C]
    simp only [F, MvPolynomial.eval₂Hom_C]
    exact IsLocalization.lift_eq hu s
  · intro j
    show F (MvPolynomial.map (algebraMap S (Localization.AtPrime p)) (X j)) = _
    rw [MvPolynomial.map_X]
    simp only [F, MvPolynomial.eval₂Hom_X']
    rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
