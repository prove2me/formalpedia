-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.thmAGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:51:44.166356+00:00
-- url     : https://prove2.me/submissions/ec566416-f22c-422e-83bd-6aec3711a61a

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_pair_linearity
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_subst_linSub
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_subst_mvExp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_frameM_genA
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sum_genA_eq_rowOp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_map_minorProd
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_thmAOp
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
universe u
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
section JetPair
variable {K : Type u} [Field K] {ι : Type}
end JetPair
section Chain
variable {K : Type u} [Field K] {ι ι' : Type} [Fintype ι] [Fintype ι']
end Chain
section Frames
end Frames
private theorem cc_subst_lemma {K : Type u} [Field K] {σ τ : Type} [Finite σ]
    (a : σ → MvPowerSeries τ K) (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (f : MvPowerSeries σ K) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  classical
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst ha,
    finsum_eq_single _ 0]
  · simp
  · intro e he
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod]
    obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr he
    rw [Finset.prod_eq_zero hs
      (by rw [map_pow, ha0, zero_pow (Finsupp.mem_support_iff.mp hs)]), smul_zero]
end Formalism.DworkPowerSeriesWeights
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : ThmAGen.{u} := by
  unfold ThmAGen
  intro K _ _ _ l d N0 N1 _ hl hl3 hd hde hlt h0 K0 hK0 ζ hζ be hbe x hx g hg0 hg U hU ε hε
    TT colN p hp hp1 I T hT xg hxg nu1 nu2 size hnu1 hnu2 hsize a ha hsa spec hs1 hs2 hs3
  have hOp := thmAOp.{u}
  unfold ThmAOp at hOp
  have key := hOp K l d N0 N1 hl hl3 hd hde hlt h0 K0 hK0 ζ hζ be hbe x hx g hg0 hg U hU ε hε
    TT colN p hp hp1 I T hT nu1 nu2 size hnu1 hnu2 hsize a ha hsa spec hs1 hs2 hs3
  have hJ := jet_pair_linearity.{u}
  unfold JetPairLin at hJ
  have hsub : MvPowerSeries.HasSubst (fun j : ZV d N0 N1 =>
      (∑ i : ZV d N0 N1, MvPowerSeries.C (genA TT T i j) * MvPowerSeries.X i :
        MvPowerSeries (ZV d N0 N1) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun j => by simp)
  have hlin : ∀ z, MvPowerSeries.subst (fun j : ZV d N0 N1 =>
      (∑ i : ZV d N0 N1, MvPowerSeries.C (genA TT T i j) * MvPowerSeries.X i :
        MvPowerSeries (ZV d N0 N1) K))
      (linSub (frameM (N1 := N1) x) z) = linSub (frameM (N1 := N1) xg) z :=
    fun z => subst_linSub (frameM (N1 := N1) x) (genA TT T) (frameM (N1 := N1) xg)
      (fun z i => frameM_genA TT T x xg hxg z i) z
  have hL : ∀ (a0 : Fin N0) (b0 : Fin N1),
      MvPowerSeries.HasSubst (fun s : ZMod d => linSub (frameM (N1 := N1) x) (s, a0, b0)) :=
    fun a0 b0 => MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by simp [linSub])
  have hLx : MvPowerSeries.HasSubst (linSub (frameM (N1 := N1) x)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by simp [linSub])
  have hbe0 : MvPowerSeries.constantCoeff be = 0 := by
    by_contra hne
    have h1 := hbe.2.2.1 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])
    simp [degE] at h1
  have hB : MvPowerSeries.constantCoeff (bSum (frameM (N1 := N1) x) be) = 0 := by
    simp only [bSum, map_sum]
    refine Finset.sum_eq_zero (fun ab _ => ?_)
    rw [cc_subst_lemma, hbe0]
    intro s
    simp [linSub]
  have hf0 : MvPowerSeries.constantCoeff (ε • bSum (frameM (N1 := N1) x) be) = 0 := by
    first
    | (rw [MvPowerSeries.smul_eq_C_mul, map_mul, hB, mul_zero])
    | (rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_smul,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hB]; simp)
  have hF : MvPowerSeries.subst (fun j : ZV d N0 N1 =>
      (∑ i : ZV d N0 N1, MvPowerSeries.C (genA TT T i j) * MvPowerSeries.X i :
        MvPowerSeries (ZV d N0 N1) K))
      (MvPowerSeries.subst (linSub (frameM (N1 := N1) x)) (MvPowerSeries.subst g U) *
        mvExp (ε • bSum (frameM (N1 := N1) x) be)) =
      MvPowerSeries.subst (linSub (frameM (N1 := N1) xg)) (MvPowerSeries.subst g U) *
        mvExp (ε • bSum (frameM (N1 := N1) xg) be) := by
    rw [MvPowerSeries.subst_mul hsub, MvPowerSeries.subst_comp_subst_apply hLx hsub,
      subst_mvExp hsub _ hf0]
    congr 2
    · funext z
      exact hlin z
    · rw [← MvPowerSeries.coe_substAlgHom hsub, map_smul]
      congr 1
      simp only [bSum, map_sum]
      refine Finset.sum_congr rfl (fun ab _ => ?_)
      rw [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_comp_subst_apply (hL ab.1 ab.2) hsub]
      congr 1
      funext s
      exact hlin _
  have hP : MvPolynomial.aeval (fun i : ZV d N0 N1 =>
      (∑ j : ZV d N0 N1, MvPolynomial.C (genA TT T i j) * MvPolynomial.X j :
        MvPolynomial (ZV d N0 N1) K))
      (∏ s : ZMod d, minorProd (fun (i : Fin N0) (b : Fin N1) =>
        (MvPolynomial.X (s, i, b) : MvPolynomial (ZV d N0 N1) K)) (p s) (hp s) (I s)) =
      ∏ s : ZMod d, minorProd (rowOp (N1 := N1) TT T s) (p s) (hp s) (I s) := by
    rw [map_prod]
    refine Finset.prod_congr rfl (fun s _ => ?_)
    rw [map_minorProd]
    congr 1
    funext i b
    rw [MvPolynomial.aeval_X]
    exact sum_genA_eq_rowOp TT T s i b
  have e1 := hJ K (ZV d N0 N1) (ZV d N0 N1) (genA TT T)
    (∏ s : ZMod d, minorProd (fun (i : Fin N0) (b : Fin N1) =>
      (MvPolynomial.X (s, i, b) : MvPolynomial (ZV d N0 N1) K)) (p s) (hp s) (I s))
    (MvPowerSeries.subst (linSub (frameM (N1 := N1) x)) (MvPowerSeries.subst g U) *
      mvExp (ε • bSum (frameM (N1 := N1) x) be))
  rw [hF, hP] at e1
  rw [e1]
  exact key
end Formalism.DworkPowerSeriesWeights
