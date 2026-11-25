-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FormalGermZero.sys_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:06:18.385482+00:00
-- url     : https://prove2.me/submissions/cc431f06-67c4-41e4-ab49-90125caac877

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_coeff_single_subst_lin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_intS_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_coeff_single_substX_tyS
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_isT_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_gsum_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_gsum_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_gsum_lg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_sys_curve
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_chart_log_constantCoeff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_raw_exlg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_raw_lin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_subst_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_intS_ps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.FormalGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)]
namespace Formalism.L2.FormalSeriesBounds.FormalGermZero
theorem _root_.solution (Y : FBChart C V O dd) (p : PairData Y d I) {g : Fin 2} (hg : (Y.raw p).CartHyp V g)
    (S : Sys (RawChart.cart hg)) :
    ∃ P : Fin dd → MvPowerSeries (I g) C, (∀ j, MvPowerSeries.constantCoeff (P j) = 0) ∧
      (∀ j, IntS V (P j)) ∧
      (∀ j c, MvPowerSeries.coeff (Finsupp.single c 1) (P j) = ∑ c', p.u g c' j * S.tan c c') ∧
      ∀ t : I g → MvPowerSeries (I g) C, S.IsT t → ∀ j,
        MvPowerSeries.subst t (P j) =
          MvPowerSeries.subst (fun i => ∑ c', p.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C))
            ((Y.raw p).ex j) := by
  have hl : 2 ≤ V.l := V.l_prime.two_le
  choose γ hγ hlog using fun c => sys_curve Y p hg S c
  have hγ0 : ∀ c, ∀ j, MvPowerSeries.constantCoeff (γ c j) = 0 := fun c j => (hγ c j).1
  have hXc : ∀ c : I g, MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) :=
    fun c => MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X c
  set Γ : I g → Fin dd → MvPowerSeries (I g) C :=
    fun c j => PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (γ c j) with hΓdef
  have hΓ0 : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0 := fun c j =>
    constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X c) (hγ0 c j)
  have hΓI : ∀ c j, IntS V (Γ c j) := fun c j =>
    IntS.subst (fun _ => MvPowerSeries.constantCoeff_X c) (fun _ => intS_X c) (intS_ps.2 (hγ c j).2)

  have hΓlg : ∀ c i, MvPowerSeries.subst (Γ c) (un1 (Y.lg i)) =
      ∑ c', p.u g c' i • PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (tyS V.l (fun s => S.al c s c')) := by
    intro c i
    have e1 : MvPowerSeries.subst (Γ c) (un1 (Y.lg i)) =
        PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (MvPowerSeries.subst (γ c) (un1 (Y.lg i))) := by
      show _ = MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) _
      rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (hγ0 c)) (hXc c)]
      rfl
    rw [e1, hlog c i, ← PowerSeries.coe_substAlgHom
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X c)), map_sum]
    simp only [map_smul]
  set P : Fin dd → MvPowerSeries (I g) C := gsum Y.B.G.F Γ Finset.univ.toList with hPdef
  have hP0 : ∀ j, MvPowerSeries.constantCoeff (P j) = 0 := gsum_const Y Γ hΓ0 _
  have hPlg : ∀ i, MvPowerSeries.subst P (un1 (Y.lg i)) =
      ∑ c, ∑ c', p.u g c' i • PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C)
        (tyS V.l (fun s => S.al c s c')) := by
    intro i
    rw [gsum_lg Y Γ hΓ0 i, Finset.sum_map_toList]
    exact Finset.sum_congr rfl fun c _ => hΓlg c i
  refine ⟨P, hP0, gsum_int Y Γ hΓ0 hΓI _, ?_, ?_⟩
  ·
    intro j c
    have hlin := coeff_single_subst_lin P hP0 (un1 (Y.lg j)) j (Y.raw_lin p j) c
    rw [← hlin, hPlg j, map_sum]
    simp only [map_sum, MvPowerSeries.coeff_smul, coeff_single_substX_tyS hl, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    congr 1
    exact congrFun (S.curve c).2.1 (Sum.inl c')
  ·
    intro t ht j
    have ht0 := ht.1
    have hts := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
    set Q : Fin dd → MvPowerSeries (I g) C := fun j => MvPowerSeries.subst t (P j) with hQ
    have hQ0 : ∀ j, MvPowerSeries.constantCoeff (Q j) = 0 := fun j => constantCoeff_subst_zero ht0 (hP0 j)
    have hPS := MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
    have hQlg : ∀ i, MvPowerSeries.subst Q (un1 (Y.lg i)) =
        ∑ c', p.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C) := by
      intro i
      have e1 : MvPowerSeries.subst Q (un1 (Y.lg i)) = MvPowerSeries.subst t (MvPowerSeries.subst P (un1 (Y.lg i))) := by
        rw [MvPowerSeries.subst_comp_subst_apply hPS hts]
      have e2 : ∀ c (A : PowerSeries C), MvPowerSeries.subst t
          (PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) A) = PowerSeries.subst (t c) A := by
        intro c A
        show MvPowerSeries.subst t (MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) A) =
          MvPowerSeries.subst (fun _ : Unit => t c) A
        rw [MvPowerSeries.subst_comp_subst_apply (hXc c) hts]
        congr 1
        funext u
        rw [MvPowerSeries.subst_X hts]
      rw [e1, hPlg i, ← MvPowerSeries.coe_substAlgHom hts, map_sum]
      simp only [map_sum, map_smul, MvPowerSeries.coe_substAlgHom hts, e2]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [← Finset.smul_sum, isT_sum S ht c']
    have hlgS := MvPowerSeries.hasSubst_of_constantCoeff_zero (Y.chart_log_constantCoeff p)
    have hQS := MvPowerSeries.hasSubst_of_constantCoeff_zero hQ0
    have h := congrArg (MvPowerSeries.subst Q) (Y.raw_exlg p j)
    rw [MvPowerSeries.subst_comp_subst_apply hlgS hQS, MvPowerSeries.subst_X hQS] at h
    show Q j = _
    rw [← h]
    congr 1
    funext i
    exact hQlg i
end Formalism.L2.FormalSeriesBounds.FormalGermZero
