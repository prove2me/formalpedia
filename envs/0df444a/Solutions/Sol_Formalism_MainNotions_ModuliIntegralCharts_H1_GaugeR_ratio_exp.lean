-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.ratio_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:50.696179+00:00
-- url     : https://prove2.me/submissions/12c21462-edf2-4d49-854a-c4d42ba26ad3

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqC
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_embK_conj
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_hunit_chi
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_exists_embDomain
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_degree_embDomain
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_rename_rescale
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
theorem _root_.solution (hR : GaugeRatioSt) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (r : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (h1 : MvPowerSeries.constantCoeff r = 1)
    (hr : ∀ a : 𝓞 E, MvPowerSeries.rescale (sc (Dw := Dw) c S (1 + a * H.bar a)) r =
      MvPowerSeries.rescale (sc (Dw := Dw) c S a) r ^ 2 * r * MvPowerSeries.rescale (sc (Dw := Dw) c S (a * H.bar a)) r) :
    ∃ q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S, MvPowerSeries.constantCoeff q = 0 ∧
      (∀ m, MvPowerSeries.coeff m q ≠ 0 → m.degree = 2) ∧
      (∀ ℓ ℓ' : Lt1 Dw, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1 +
          Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ') 1) q ≠ 0 → ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) ∧
      r = PowerSeries.subst q (PowerSeries.exp S) := by
  letI : StarRing (𝓞 E) := barStar H
  let r' : MvPowerSeries (Lt1 Dw) S := fun y => MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y) r
  have hcr' : ∀ y, MvPowerSeries.coeff y r' = MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y) r :=
    fun y => rfl
  have hrr : MvPowerSeries.rename (nu Dw).toEmbedding r' = r := by
    ext x
    obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) x
    rw [coeff_rename_emb_lemma, hcr']
  have hinj : ∀ p p' : MvPowerSeries (Lt1 Dw) S,
      MvPowerSeries.rename (nu Dw).toEmbedding p = MvPowerSeries.rename (nu Dw).toEmbedding p' → p = p' := by
    intro p p' hpp
    ext y
    have hc := congrArg (MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y)) hpp
    simpa only [coeff_rename_emb_lemma] using hc
  have hsc : ∀ b : 𝓞 E, (fun ℓ : Lt1 Dw => sc (Dw := Dw) c S b (nu Dw ℓ)) = fun ℓ => chi c S ℓ.1 b := by
    intro b
    funext ℓ
    simp [sc, chi, nu]
  have hscale : ∀ (b : 𝓞 E) (p : MvPowerSeries (Lt1 Dw) S),
      MvPowerSeries.rename (nu Dw).toEmbedding (scaleBy (rk := Dw.mult) (chi c S) b p) =
        MvPowerSeries.rescale (sc (Dw := Dw) c S b) (MvPowerSeries.rename (nu Dw).toEmbedding p) := by
    intro b p
    (rw [← rename_rescale, hsc b]) <;> rfl
  have hr0' : MvPowerSeries.constantCoeff r' = 1 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hcr', Finsupp.embDomain_zero,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h1]
  have hr' : ∀ a : 𝓞 E, scaleBy (rk := Dw.mult) (chi c S) (1 + a * star a) r' =
      scaleBy (rk := Dw.mult) (chi c S) a r' ^ 2 * r' * scaleBy (rk := Dw.mult) (chi c S) (a * star a) r' := by
    intro a
    apply hinj
    rw [map_mul, map_mul, map_pow, hscale, hscale, hscale, hrr]
    exact hr a
  have hcc : ∀ (σ : E →+* ℂ) (a : 𝓞 E), chi c S (ComplexEmbedding.conjugate σ) a = chi c S σ (star a) := by
    intro σ a
    simp only [chi, RingHom.comp_apply]
    (rw [embK_conj]) <;> rfl
  obtain ⟨q', hq0, hqdeg, hqpair, hqexp⟩ :=
    hR (𝓞 E) S (E →+* ℂ) Dw.mult (chi c S) ComplexEmbedding.conjugate hcc
      (fun σ τ hστ => hunit_chi c S σ τ hστ) r' hr0' hr'
  have hq0r : MvPowerSeries.constantCoeff (MvPowerSeries.rename (nu Dw).toEmbedding q') = 0 := by
    rw [MvPowerSeries.constantCoeff_rename, hq0]
  refine ⟨MvPowerSeries.rename (nu Dw).toEmbedding q', hq0r, ?_, ?_, ?_⟩
  · intro m hm
    obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) m
    rw [coeff_rename_emb_lemma] at hm
    rw [degree_embDomain]
    exact hqdeg y hm
  · intro ℓ ℓ' hm
    have hsum : Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1 + Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ') 1 =
        Finsupp.embDomain (nu Dw).toEmbedding (Finsupp.single ℓ 1 + Finsupp.single ℓ' 1) := by
      (rw [Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single]) <;> rfl
    rw [hsum, coeff_rename_emb_lemma] at hm
    exact hqpair ℓ ℓ' hm
  · ext m
    obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) m
    rw [← hrr, coeff_rename_emb_lemma, hqexp,
      PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hq0),
      PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hq0r)]
    congr 1
    funext d
    rw [← map_pow, coeff_rename_emb_lemma]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
