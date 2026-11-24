-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.sum_encP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:48:00.32195+00:00
-- url     : https://prove2.me/submissions/88910bc3-e41e-4c40-a565-e4ea02f95189

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
open MvPowerSeries
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {n : ℕ}
    {K S : Type} [CommRing K] [CommRing S] (φ : K →+* S) (P : MvPolynomial (LtN Dw n) K)
    (V : ((Σ τ : E →+* ℂ, Fin (Dw.mult τ)) × Fin n →₀ ℕ) → S) :
    ∑ m' ∈ (MvPolynomial.map φ (encP P)).support, (MvPolynomial.map φ (encP P)).coeff m' * V m' =
      ∑ m ∈ P.support, φ (P.coeff m) * V (Finsupp.equivMapDomain (ltEquiv Dw n) m) := by
  classical
  have hinj : Function.Injective (ltEquiv Dw n) := (ltEquiv Dw n).injective
  unfold encP
  rw [MvPolynomial.map_rename, MvPolynomial.support_rename_of_injective hinj,
    Finset.sum_image (fun x _ y _ h => Finsupp.mapDomain_injective hinj h)]
  simp only [MvPolynomial.coeff_rename_mapDomain _ hinj, MvPolynomial.coeff_map,
    Finsupp.equivMapDomain_eq_mapDomain]
  refine Finset.sum_subset (MvPolynomial.support_map_subset _ _) ?_
  intro m _ hm
  rw [MvPolynomial.notMem_support_iff, MvPolynomial.coeff_map] at hm
  rw [hm, zero_mul]
end Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
