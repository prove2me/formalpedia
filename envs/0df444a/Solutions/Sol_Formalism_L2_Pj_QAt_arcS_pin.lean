-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.arcS_pin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:11:34.35555+00:00
-- url     : https://prove2.me/submissions/3f00534f-1979-4df3-8a34-3e44a8913a61

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_ArcLineFunctions_ArcSPin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace Formalism.L2.Pj.QAt
theorem _root_.solution (Dw : Datum H) (K₁ : Type) [Field K₁] {F₀ : Type} [Field F₀] [Algebra F₀ K₁] (r : F₀) :
    algebraMap F₀ (ArcS Dw K₁) r = arcι Dw K₁ (PowerSeries.C (R := K₁) (algebraMap F₀ K₁ r)) := by
  rw [IsScalarTower.algebraMap_apply F₀ (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁)]
  have h1 : algebraMap F₀ (LaurentSeries K₁) r =
      HahnSeries.ofPowerSeries ℤ K₁ (algebraMap F₀ (PowerSeries K₁) r) := rfl
  have h2 : algebraMap F₀ (PowerSeries K₁) r = PowerSeries.C (R := K₁) (algebraMap F₀ K₁ r) := by
    first
      | (rw [IsScalarTower.algebraMap_apply F₀ K₁ (PowerSeries K₁)]; rfl)
      | exact MvPowerSeries.algebraMap_apply
      | exact PowerSeries.algebraMap_apply' r
      | simp [Algebra.algebraMap_eq_smul_one]
  simp only [arcι, RingHom.comp_apply, MvPolynomial.algebraMap_apply, h1, h2]
end Formalism.L2.Pj.QAt
