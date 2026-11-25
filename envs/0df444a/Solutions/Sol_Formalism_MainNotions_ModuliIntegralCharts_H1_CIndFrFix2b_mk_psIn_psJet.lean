-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b.mk_psIn_psJet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:12:23.151466+00:00
-- url     : https://prove2.me/submissions/b56a0cf6-499b-441d-a473-dd4049f4b9c9

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HomUniq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddSecondThird
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2b_cc_pt__5e1994025291
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2b_jetSubstP_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2b_mk_X_psJet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_hasSubst_pts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_subst_exp


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing (ev_ev ev_X hasSubst_pts exp_add subst_exp)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
theorem _root_.solution {n n' : ℕ} (m : ℕ) (σ : Fin n → Fin n') (f : PS S n d) :
    Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n' × Fin d) ^ (m + 1)) (psIn d m σ f) =
      psJet m (ev (fun i => pt S d (σ i)) f) := by
  have ha : ∀ p : Fin n × Fin d, MvPowerSeries.constantCoeff ((fun i => pt S d (σ i)) p.1 p.2) = 0 := fun p => cc_pt' _ _
  have hφ : ∀ p : Fin n × Fin d, MvPolynomial.constantCoeff (X (σ p.1, p.2) : MvPolynomial (Fin n' × Fin d) S) = 0 :=
    fun p => by simp
  have hmk : ∀ p : Fin n × Fin d, Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n' × Fin d) ^ (m + 1)) (X (σ p.1, p.2)) =
      psJet m ((fun i => pt S d (σ i)) p.1 p.2) := fun p => mk_X_psJet m (σ p.1, p.2)
  rw [← jetSubstP_psJet m (fun p : Fin n × Fin d => (X (σ p.1, p.2) : MvPolynomial (Fin n' × Fin d) S)) (fun i => pt S d (σ i)) ha hφ hmk f]
  unfold jetSubstP jetMap liftJet psJet psIn
  simp only [MvPolynomial.constantCoeff_X, map_zero, sub_zero, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk,
    AlgHom.coe_toRingHom, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  have hr : (aeval fun i : Fin n × Fin d => (X (σ i.1, i.2) : MvPolynomial (Fin n' × Fin d) S)) =
      rename (fun p : Fin n × Fin d => (σ p.1, p.2)) :=
    MvPolynomial.algHom_ext fun i => by simp
  erw [Ideal.Quotient.lift_mk]
  simp only [AlgHom.coe_toRingHom, AlgHom.comp_apply, hr, Ideal.Quotient.mkₐ_eq_mk]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
