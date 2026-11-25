-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.expPhi_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:58:22.11435+00:00
-- url     : https://prove2.me/submissions/f5dcf1a2-56ae-472d-9a29-56812d1800d0

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_subst_linPt
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_hasSubst_linPt
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_hasSubst_XX
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_hasSubst___01ac09189af3
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_subst___comp1_f9ac2339a24b
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_atPt_expPhi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_cc_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_cc_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_germComp1_germComp1_eq_substitute
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_germCompOne_identityPoint_left


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
variable {S : Type} [CommRing S] [Algebra ℚ S]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
theorem _root_.solution (G : FGLaw S d) (uvec : Lt1 Dw → Fin d → S) (ℓ ε : Pt S 1 d) (hinv : IsInvPair ε ℓ)
    (htr : transF G.F ε ℓ = pt S (n := 2) d 0 + pt S (n := 2) d 1) (j : Fin d) :
    subst (fun p : Fin 2 × Fin d => atPt p.1 (expPhi uvec ε p.2)) (G.F j) =
      subst (fun q : Fin 1 × Fin (dL Dw) =>
        (X ((0 : Fin 2), q.2) + X ((1 : Fin 2), q.2) : MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) (expPhi uvec ε j) := by
  have hε0 := hinv.1
  have hℓ0 := hinv.2.1
  have hcc : ∀ (b : Fin 2) i, constantCoeff (comp1 ε (pt S (n := 2) d b) i) = 0 :=
    fun b i => cc_comp1 _ _ hε0 (cc_pt b) i
  have hccA : ∀ i, constantCoeff
      (addOf G.F (comp1 ε (pt S (n := 2) d 0)) (comp1 ε (pt S (n := 2) d 1)) i) = 0 :=
    fun i => cc_ev _ (fun k i => by fin_cases k <;> exact hcc _ i) (G.const i)
  have hΦ : addOf G.F (comp1 ε (pt S (n := 2) d 0)) (comp1 ε (pt S (n := 2) d 1)) =
      comp1 ε (pt S (n := 2) d 0 + pt S (n := 2) d 1) := by
    have h1 : comp1 ℓ (addOf G.F (comp1 ε (pt S (n := 2) d 0)) (comp1 ε (pt S (n := 2) d 1))) =
        pt S (n := 2) d 0 + pt S (n := 2) d 1 := htr
    have h2 := congrArg (comp1 ε) h1
    rw [germComp1_germComp1_eq_substitute ε ℓ _ hℓ0 hccA, hinv.2.2.1, germCompOne_identityPoint_left _ hccA] at h2
    exact h2
  have ha : HasSubst (fun p : Fin 2 × Fin d =>
      (![comp1 ε (pt S (n := 2) d 0), comp1 ε (pt S (n := 2) d 1)] : Fin 2 → Pt S 2 d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => by
      obtain ⟨b, i⟩ := p
      fin_cases b <;> exact hcc _ i
  have hL : subst (fun p : Fin 2 × Fin d => atPt p.1 (expPhi uvec ε p.2)) (G.F j) =
      subst (fun p : Fin 2 × Fin d => linPt uvec p.1 p.2)
        (addOf G.F (comp1 ε (pt S (n := 2) d 0)) (comp1 ε (pt S (n := 2) d 1)) j) := by
    rw [addOf, ev, subst_comp_subst_apply ha (hasSubst_Λ uvec)]
    congr 1
    funext p
    obtain ⟨b, i⟩ := p
    rw [atPt_expPhi]
    fin_cases b
    · exact (subst_Λ_comp1 uvec ε 0 i).symm
    · exact (subst_Λ_comp1 uvec ε 1 i).symm
  have hR : subst (fun q : Fin 1 × Fin (dL Dw) =>
      (X ((0 : Fin 2), q.2) + X ((1 : Fin 2), q.2) : MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) (expPhi uvec ε j) =
      subst (fun p : Fin 2 × Fin d => linPt uvec p.1 p.2) (comp1 ε (pt S (n := 2) d 0 + pt S (n := 2) d 1) j) := by
    have hs : HasSubst (fun q : Fin 1 × Fin d =>
        (![pt S (n := 2) d 0 + pt S (n := 2) d 1] : Fin 1 → Pt S 2 d) q.1 q.2) :=
      hasSubst_of_constantCoeff_zero fun q => by
        obtain ⟨k, i⟩ := q
        fin_cases k
        simp [pt]
    rw [expPhi, subst_comp_subst_apply (hasSubst_linPt uvec 0) hasSubst_XX, comp1, ev,
      subst_comp_subst_apply hs (hasSubst_Λ uvec)]
    congr 1
    funext q
    obtain ⟨k, i⟩ := q
    fin_cases k
    show _ = subst (fun p : Fin 2 × Fin d => linPt uvec p.1 p.2)
      (X ((0 : Fin 2), i) + X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × Fin d) S)
    rw [subst_linPt uvec 0 _ hasSubst_XX, ← coe_substAlgHom (hasSubst_Λ uvec), map_add, coe_substAlgHom,
      subst_X (hasSubst_Λ uvec), subst_X (hasSubst_Λ uvec), linPt, linPt, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ℓ' _ => ?_
    rw [mul_add]
  rw [hL, hR, hΦ]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
