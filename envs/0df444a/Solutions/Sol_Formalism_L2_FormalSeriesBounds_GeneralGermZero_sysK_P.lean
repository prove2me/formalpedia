-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GeneralGermZero.sysK_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:39:11.202241+00:00
-- url     : https://prove2.me/submissions/26be1478-2a1e-406f-b26d-9e61b2eaa301

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GeneralGermZero_gsumK_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GeneralGermZero_gsumK_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GeneralGermZero_gsumK_lg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_coeff_single_substX_tyS
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_coeff_single_subst_lin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_intS_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_isT_sum
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
open Formalism.L2.FormalSeriesBounds.GeneralGermZero
open Formalism.IncomingBounds FormalGermZero
variable {C : Type} [Field C] {κ : Type} [Fintype κ]
variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (X : RawChart C d I κ)
  (F : κ → MvPowerSeries (Fin 2 × κ) C) (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
  (hFI : ∀ k, IntS V (F k)) (hadd : LgAdd F X.lg)
  (hlin : ∀ k (μ : κ →₀ ℕ), μ.degree ≤ 1 → MvPowerSeries.coeff μ (X.lg k) = MvPowerSeries.coeff μ (MvPowerSeries.X k))
  (hexlg : ∀ k, MvPowerSeries.subst X.lg (X.ex k) = (MvPowerSeries.X k : MvPowerSeries κ C))
include hF0 hFI hadd hlin hexlg
namespace Formalism.L2.FormalSeriesBounds.GeneralGermZero
theorem _root_.solution {g : Fin 2} (hg : X.CartHyp V g) (S : Sys (RawChart.cart hg)) :
    ∃ P : κ → MvPowerSeries (I g) C, (∀ j, MvPowerSeries.constantCoeff (P j) = 0) ∧
      (∀ j, IntS V (P j)) ∧
      (∀ j c, MvPowerSeries.coeff (Finsupp.single c 1) (P j) = ∑ c', X.u g c' j * S.tan c c') ∧
      ∀ t : I g → MvPowerSeries (I g) C, S.IsT t → ∀ j,
        MvPowerSeries.subst t (P j) =
          MvPowerSeries.subst (fun i => ∑ c', X.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C)) (X.ex j) := by
  have hl : 2 ≤ V.l := V.l_prime.two_le
  have hlg0 : ∀ k, MvPowerSeries.constantCoeff (X.lg k) = 0 := fun k => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hlin k 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have hcur : ∀ c, ∃ γ : κ → PowerSeries C, IsCv V γ ∧ ∀ i, MvPowerSeries.subst γ (X.lg i) =
      ∑ c' : I g, X.u g c' i • tyS V.l (fun s => S.al c s c') := by
    intro c
    have hm : S.cur c ∈ X.TySet V g := (S.curve c).1
    obtain ⟨γ, lam, hγ, -, hlog, -⟩ := hm
    exact ⟨γ, hγ, hlog⟩
  choose γ hγ hlog using hcur
  have hγ0 : ∀ c, ∀ j, MvPowerSeries.constantCoeff (γ c j) = 0 := fun c j => (hγ c j).1
  have hXc : ∀ c : I g, MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) :=
    fun c => MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X c
  set Γ : I g → κ → MvPowerSeries (I g) C :=
    fun c j => PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (γ c j) with hΓdef
  have hΓ0 : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0 := fun c j =>
    constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X c) (hγ0 c j)
  have hΓI : ∀ c j, IntS V (Γ c j) := fun c j =>
    IntS.subst (fun _ => MvPowerSeries.constantCoeff_X c) (fun _ => intS_X c) (intS_ps.2 (hγ c j).2)
  have hΓlg : ∀ c i, MvPowerSeries.subst (Γ c) (X.lg i) =
      ∑ c', X.u g c' i • PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (tyS V.l (fun s => S.al c s c')) := by
    intro c i
    have e1 : MvPowerSeries.subst (Γ c) (X.lg i) =
        PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (MvPowerSeries.subst (γ c) (X.lg i)) := by
      show _ = MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) _
      rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (hγ0 c)) (hXc c)]
      rfl
    rw [e1, hlog c i, ← PowerSeries.coe_substAlgHom
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X c)), map_sum]
    simp only [map_smul]
  set P : κ → MvPowerSeries (I g) C := gsumK F Γ Finset.univ.toList with hPdef
  have hP0 : ∀ j, MvPowerSeries.constantCoeff (P j) = 0 := gsumK_const hF0 Γ hΓ0 _
  have hPlg : ∀ i, MvPowerSeries.subst P (X.lg i) =
      ∑ c, ∑ c', X.u g c' i • PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C)
        (tyS V.l (fun s => S.al c s c')) := by
    intro i
    rw [gsumK_lg hF0 hadd hlg0 Γ hΓ0 i, Finset.sum_map_toList]
    exact Finset.sum_congr rfl fun c _ => hΓlg c i
  refine ⟨P, hP0, gsumK_int hF0 hFI Γ hΓ0 hΓI _, ?_, ?_⟩
  · intro j c
    have hl1 := coeff_single_subst_lin P hP0 (X.lg j) j (hlin j) c
    rw [← hl1, hPlg j, map_sum]
    simp only [map_sum, MvPowerSeries.coeff_smul, coeff_single_substX_tyS hl, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    congr 1
    exact congrFun (S.curve c).2.1 (Sum.inl c')
  · intro t ht j
    have ht0 := ht.1
    have hts := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
    set Q : κ → MvPowerSeries (I g) C := fun j => MvPowerSeries.subst t (P j) with hQ
    have hQ0 : ∀ j, MvPowerSeries.constantCoeff (Q j) = 0 := fun j => constantCoeff_subst_zero ht0 (hP0 j)
    have hPS := MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
    have hQlg : ∀ i, MvPowerSeries.subst Q (X.lg i) =
        ∑ c', X.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C) := by
      intro i
      have e1 : MvPowerSeries.subst Q (X.lg i) = MvPowerSeries.subst t (MvPowerSeries.subst P (X.lg i)) := by
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
    have hlgS := MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0
    have hQS := MvPowerSeries.hasSubst_of_constantCoeff_zero hQ0
    have h := congrArg (MvPowerSeries.subst Q) (hexlg j)
    rw [MvPowerSeries.subst_comp_subst_apply hlgS hQS, MvPowerSeries.subst_X hQS] at h
    show Q j = _
    rw [← h]
    congr 1
    funext i
    exact hQlg i
end Formalism.L2.FormalSeriesBounds.GeneralGermZero
