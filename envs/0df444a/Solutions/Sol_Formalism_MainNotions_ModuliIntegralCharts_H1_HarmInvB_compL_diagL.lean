-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB.compL_diagL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:53.732809+00:00
-- url     : https://prove2.me/submissions/7d9468eb-7015-4307-a028-d5a364d218eb

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvB
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvB_log_expPhi
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvB_log_expPhi_act
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvB_germCompOne_identityPoint_left
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvB_subst_lg
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_expPhi_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (logOf)
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
theorem _root_.solution {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (w0 : O) (cc : Fin d → Fin d → S)
    (uvec : Lt1 Dw → Fin d → S) (ε : Pt S 1 d) (hinv : IsInvPair ε (fun i => logOf B.G i))
    (a : Fin 1 × Fin (dL Dw) → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (ha : ∀ q, MvPowerSeries.constantCoeff (a q) = 0)
    (hact : ∀ j, MvPowerSeries.subst (fun p : Fin 1 × Fin d => expPhi uvec ε p.2) (B.A.act w0 j) =
      MvPowerSeries.subst a (expPhi uvec ε j)) :
    compL (expPhi uvec ε) (diagL B w0 cc) =
      ∑ i, ∑ l, cc i l • (linPt uvec (0 : Fin 1) i * MvPowerSeries.subst a (linPt uvec (0 : Fin 1) l)) := by
  have hε0 : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0 := by
    obtain ⟨h, -⟩ := hinv
    exact h
  have hE0 : ∀ p : Fin 1 × Fin d, MvPowerSeries.constantCoeff (expPhi uvec ε p.2) = 0 :=
    fun p => Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.expPhi_const uvec ε hε0 p.2
  have hE : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => expPhi uvec ε p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hE0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hE0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hE0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hE0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [hE0 s]; exact IsNilpotent.zero)
  have hV0 : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff ((fun p : Fin 2 × Fin d => (![pt S d 0, comp1 (B.A.act w0) (pt S d 0)] : Fin 2 → Pt S 1 d) p.1 p.2) p) = 0 := by
    intro p
    rcases p with ⟨j, c⟩
    fin_cases j
    · simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
    · simp [germCompOne_identityPoint_left, B.A.const]
  have hV : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d => (![pt S d 0, comp1 (B.A.act w0) (pt S d 0)] : Fin 2 → Pt S 1 d) p.1 p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hV0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hV0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hV0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hV0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [hV0 s]; exact IsNilpotent.zero)
  change MvPowerSeries.subst (fun p : Fin 1 × Fin d => expPhi uvec ε p.2) (MvPowerSeries.subst (fun p : Fin 2 × Fin d => (![pt S d 0, comp1 (B.A.act w0) (pt S d 0)] : Fin 2 → Pt S 1 d) p.1 p.2) (bilL B.G cc)) = _
  rw [← MvPowerSeries.coe_substAlgHom hV, ← MvPowerSeries.coe_substAlgHom hE]
  simp only [Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL, map_sum, map_smul, map_mul]
  simp only [MvPowerSeries.coe_substAlgHom]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => ?_))
  rw [subst_lg B.G (fun p : Fin 2 × Fin d => (![pt S d 0, comp1 (B.A.act w0) (pt S d 0)] : Fin 2 → Pt S 1 d) p.1 p.2) hV0 0 i, subst_lg B.G (fun p : Fin 2 × Fin d => (![pt S d 0, comp1 (B.A.act w0) (pt S d 0)] : Fin 2 → Pt S 1 d) p.1 p.2) hV0 1 l]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, germCompOne_identityPoint_left]
  have hP0 : ∀ p : Fin 1 × Fin d, MvPowerSeries.constantCoeff (pt S (n := 1) d 0 p.2) = 0 := by
    intro p
    simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  have hP : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => pt S (n := 1) d 0 p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hP0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hP0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hP0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [hP0 s]; exact IsNilpotent.zero)
  have hQ0 : ∀ p : Fin 1 × Fin d, MvPowerSeries.constantCoeff (B.A.act w0 p.2) = 0 := fun p => B.A.const w0 p.2
  have hQ : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => B.A.act w0 p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hQ0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hQ0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hQ0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hQ0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [hQ0 s]; exact IsNilpotent.zero)
  rw [MvPowerSeries.subst_comp_subst_apply hP hE, MvPowerSeries.subst_comp_subst_apply hQ hE]
  simp only [hact]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, MvPowerSeries.subst_X hE]
  rw [log_expPhi B.G uvec ε hinv i, log_expPhi_act B.G uvec ε hinv a ha l]
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
