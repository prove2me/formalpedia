-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3.const_diagL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:57.910508+00:00
-- url     : https://prove2.me/submissions/e2dada6f-0063-40ff-b293-5aeab5f78a7b

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_EvalSinglePointId
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix3_const_bilL
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix3_diag_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
attribute [local instance] Over.cartesianMonoidalCategory
section Alg
variable {S : Type} [CommRing S] {d : ℕ}
end Alg
section Unit
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
variable {O : Type} [CommRing O] [StarRing O]
private theorem const_ev_lemma {R : Type} [CommRing R] {e m n : ℕ} (a : Fin m → Pt R n e) (f : PS R m e)
    (ha : ∀ p q, MvPowerSeries.constantCoeff (a p q) = 0) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (ev a f) = 0 := by
  have hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin e => a p.1 p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent
        (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => ha p.1 p.2)
    | exact ⟨fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  rw [MvPowerSeries.constantCoeff_subst hs]
  apply finsum_eq_zero_of_forall_eq_zero
  intro x
  by_cases hx : x = 0
  · subst hx
    simp [hf]
  · obtain ⟨s, hs'⟩ : ∃ s, x s ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hx (Finsupp.ext hc)
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs')]
    · simp
    · rw [map_pow, ha s.1 s.2, zero_pow hs']
end Unit
section Geo
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
end Geo
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
variable {O : Type} [CommRing O] [StarRing O]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
theorem _root_.solution (B : FB S d O) (w0 : O) (cc : Fin d → Fin d → S) :
    MvPowerSeries.constantCoeff (diagL B w0 cc) = 0 := by
  exact const_ev_lemma (![pt S (n := 1) d 0, comp1 (B.A.act w0) (pt S (n := 1) d 0)]) (bilL B.G cc)
    (diag_const B w0) (const_bilL B.G cc)
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
