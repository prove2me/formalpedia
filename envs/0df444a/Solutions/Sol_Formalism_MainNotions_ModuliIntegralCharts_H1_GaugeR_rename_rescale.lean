-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.rename_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:46:56.590812+00:00
-- url     : https://prove2.me/submissions/0cbfbbcb-93f8-4685-854d-0d99523dd24a

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqC
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_exists_embDomain
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB
namespace GaugeR
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {H : Host E} {Dw : Datum H} {l : Level H}
private theorem coeff_rename_emb_lemma {S : Type} [CommRing S] (p : MvPowerSeries (Lt1 Dw) S)
    (y : Lt1 Dw →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y) (MvPowerSeries.rename (nu Dw).toEmbedding p) =
      MvPowerSeries.coeff y p :=
  MvPowerSeries.coeff_embDomain_rename _ _ _
end GaugeR
end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB
open Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {H : Host E} {Dw : Datum H} {l : Level H}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
theorem _root_.solution {S : Type} [CommRing S] (s : Fin 1 × Fin (dL Dw) → S) (p : MvPowerSeries (Lt1 Dw) S) :
    MvPowerSeries.rename (nu Dw).toEmbedding (MvPowerSeries.rescale (fun ℓ => s (nu Dw ℓ)) p) =
      MvPowerSeries.rescale s (MvPowerSeries.rename (nu Dw).toEmbedding p) := by
  ext x
  obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) x
  simp only [coeff_rename_emb_lemma, MvPowerSeries.coeff_rescale, Finsupp.prod_embDomain] <;> rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
