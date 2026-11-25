-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AbstractGermZero.one_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:39:46.12755+00:00
-- url     : https://prove2.me/submissions/cc7d9053-eea2-4f60-a29c-8904a604fc5c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_WipDworkInvG
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AbstractGermZero_intS_iff_alt
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_FG_SolveVAux_degree_eq_one
import Theorems.Thm_Formalism_FG_SolveVAux_low_neg
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_subst
import Theorems.Thm_Formalism_FG_SolveVAux_low_subst_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero
import Theorems.Thm_Formalism_FG_solve_exists_vector
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intS_invG
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_Good_comb
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.AbstractGermZero
open Formalism.IncomingBounds
variable {C : Type} [Field C] (V : VF C)
namespace Formalism.L2.FormalSeriesBounds.AbstractGermZero
theorem _root_.solution {σ : Type} [Fintype σ] (t t₂ φ φ₂ : σ → MvPowerSeries σ C)
    (ht0₂ : ∀ c, MvPowerSeries.constantCoeff (t₂ c) = 0) (ht0 : ∀ c, MvPowerSeries.constantCoeff (t c) = 0)
    (hφ0 : ∀ k, MvPowerSeries.constantCoeff (φ k) = 0) (hφ : ∀ k, IntS V (φ k))
    (hL : V.v (Matrix.of fun k c : σ => MvPowerSeries.coeff (Finsupp.single c 1) (φ k)).det = 0)
    (hφ0₂ : ∀ k, MvPowerSeries.constantCoeff (φ₂ k) = 0) (hφ₂ : ∀ k, IntS V (φ₂ k))
    (heq : ∀ k, MvPowerSeries.subst t (φ k) = MvPowerSeries.subst t₂ (φ₂ k)) :
    ∃ h : σ → MvPowerSeries σ C, (∀ c, MvPowerSeries.constantCoeff (h c) = 0) ∧ (∀ c, IntS V (h c)) ∧
      ∀ c, t c = MvPowerSeries.subst t₂ (h c) := by
  classical

  set L : Matrix σ σ C := Matrix.of fun k c : σ => MvPowerSeries.coeff (Finsupp.single c 1) (φ k)
    with hLdef
  have hdet : IsUnit L.det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0] at hL
    simp at hL
  set N : Matrix σ σ C := L⁻¹ with hNdef
  have hLN : L * N = 1 := Matrix.mul_nonsing_inv L hdet
  have hNL : N * L = 1 := Matrix.nonsing_inv_mul L hdet

  have comb : ∀ {M : Type} [AddCommGroup M] [Module C M] (A B : Matrix σ σ C), A * B = 1 →
      ∀ (X : σ → M) (i : σ), ∑ j, A i j • ∑ k, B j k • X k = X i := by
    intro M _ _ A B hAB X i
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have hrow : ∀ k, ∑ j, A i j * B j k = (1 : Matrix σ σ C) i k := fun k => by
      rw [← hAB, Matrix.mul_apply]
    simp only [hrow, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hcoeff : ∀ (ψ : σ → MvPowerSeries σ C) j μ,
      MvPowerSeries.coeff μ (∑ k, N j k • ψ k) = ∑ k, N j k * MvPowerSeries.coeff μ (ψ k) := by
    intro ψ j μ
    simp only [map_sum, MvPowerSeries.coeff_smul]
  have hcc : ∀ (ψ : σ → MvPowerSeries σ C), (∀ k, MvPowerSeries.constantCoeff (ψ k) = 0) →
      ∀ j, MvPowerSeries.constantCoeff (∑ k, N j k • ψ k) = 0 := by
    intro ψ hψ j
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hcoeff]
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hψ]

  have hid : Formalism.FG.IsIdMod2 (fun j => ∑ k, N j k • φ k) := by
    refine ⟨hcc φ hφ0, fun j i => ?_⟩
    show MvPowerSeries.coeff (Finsupp.single i 1) (∑ k, N j k • φ k) = _
    rw [hcoeff]
    have hNLji : ∑ k, N j k * MvPowerSeries.coeff (Finsupp.single i 1) (φ k) = (N * L) j i := by
      rw [Matrix.mul_apply]
      rfl
    rw [hNLji, hNL, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [if_neg (Ne.symm hij), if_neg hij]
  obtain ⟨h, hh0, hhs⟩ := Formalism.FG.solve_exists_vector C σ σ (fun j => ∑ k, N j k • φ k)
    (fun j => ∑ k, N j k • φ₂ k) hid (hcc φ₂ hφ0₂)
  have hsub_h : MvPowerSeries.HasSubst h := MvPowerSeries.hasSubst_of_constantCoeff_zero hh0
  have hlin : ∀ (a : σ → MvPowerSeries σ C), MvPowerSeries.HasSubst a → ∀ j,
      MvPowerSeries.subst a (∑ k, N j k • φ k) = ∑ k, N j k • MvPowerSeries.subst a (φ k) := by
    intro a ha j
    rw [← MvPowerSeries.coe_substAlgHom ha, map_sum, MvPowerSeries.coe_substAlgHom ha]
    exact Finset.sum_congr rfl fun k _ => MvPowerSeries.subst_smul ha _ _

  have hφh : ∀ k, MvPowerSeries.subst h (φ k) = φ₂ k := by
    have h1 : ∀ j, ∑ k, N j k • MvPowerSeries.subst h (φ k) = ∑ k, N j k • φ₂ k := by
      intro j
      rw [← hlin h hsub_h]
      exact hhs j
    intro i
    have e1 := comb L N hLN (fun k => MvPowerSeries.subst h (φ k)) i
    have e2 := comb L N hLN φ₂ i
    simp only [h1] at e1
    exact e1.symm.trans e2
  have hhI : ∀ c, IntS V (h c) := by
    have hint := AltInv.intS_invG φ h φ₂ hφ0 (fun k => (intS_iff_alt V _).mp (hφ k)) hL hh0
      (fun k => (intS_iff_alt V _).mp (hφ₂ k)) hφh
    exact fun c => (intS_iff_alt V _).mpr (hint c)

  have hsub_t : MvPowerSeries.HasSubst t := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
  have hsub_t₂ : MvPowerSeries.HasSubst t₂ := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0₂
  set t' : σ → MvPowerSeries σ C := fun c => MvPowerSeries.subst t₂ (h c) with ht'
  have hL1t : ∀ i, Formalism.FG.SolveVAux.Low 1 (t i) :=
    fun i => (Formalism.FG.SolveVAux.low_one_iff _).mpr (ht0 i)
  have hL1t' : ∀ i, Formalism.FG.SolveVAux.Low 1 (t' i) := fun i =>
    Formalism.FG.SolveVAux.low_subst (fun j => (Formalism.FG.SolveVAux.low_one_iff _).mpr (ht0₂ j))
      ((Formalism.FG.SolveVAux.low_one_iff _).mpr (hh0 i))
  have hsub_t' : MvPowerSeries.HasSubst t' :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => (Formalism.FG.SolveVAux.low_one_iff _).mp (hL1t' i)
  have hφt : ∀ k, MvPowerSeries.subst t (φ k) = MvPowerSeries.subst t' (φ k) := by
    intro k
    rw [heq k, ← hφh k]
    exact MvPowerSeries.subst_comp_subst_apply hsub_h hsub_t₂ (φ k)
  have hg2 : ∀ j, Formalism.FG.SolveVAux.Low 2 ((∑ k, N j k • φ k) - MvPowerSeries.X j) := by
    intro j
    unfold Formalism.FG.SolveVAux.Low
    intro d hd
    rw [map_sub]
    rcases (by omega : d.degree = 0 ∨ d.degree = 1) with hd0 | hd1
    · have hd00 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hd0
      subst hd00
      simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ0]
    · obtain ⟨i, rfl⟩ := Formalism.FG.SolveVAux.degree_eq_one d hd1
      rw [show MvPowerSeries.coeff (Finsupp.single i 1) (∑ k, N j k • φ k) =
        if i = j then 1 else 0 from hid.2 j i, MvPowerSeries.coeff_X]
      by_cases hij : i = j
      · subst hij
        simp
      · rw [if_neg hij, if_neg]
        · simp
        · intro h'
          exact hij (Finsupp.single_left_injective one_ne_zero h')
  have hlow : ∀ (M : ℕ) (i : σ), Formalism.FG.SolveVAux.Low M (t i - t' i) := by
    intro M
    induction M with
    | zero => exact fun i => Formalism.FG.SolveVAux.low_zero _
    | succ M ih =>
      intro i
      have hsplit : ∀ a : σ → MvPowerSeries σ C, MvPowerSeries.HasSubst a →
          MvPowerSeries.subst a (∑ k, N i k • φ k) =
            a i + MvPowerSeries.subst a ((∑ k, N i k • φ k) - MvPowerSeries.X i) := by
        intro a ha
        rw [MvPowerSeries.subst_sub ha, MvPowerSeries.subst_X ha]
        abel
      have hfeq : MvPowerSeries.subst t (∑ k, N i k • φ k) =
          MvPowerSeries.subst t' (∑ k, N i k • φ k) := by
        rw [hlin t hsub_t, hlin t' hsub_t']
        simp only [hφt]
      have h1 := hsplit t hsub_t
      have h2 := hsplit t' hsub_t'
      rw [hfeq] at h1
      have hdiff : t i - t' i =
          -(MvPowerSeries.subst t ((∑ k, N i k • φ k) - MvPowerSeries.X i) -
            MvPowerSeries.subst t' ((∑ k, N i k • φ k) - MvPowerSeries.X i)) := by
        linear_combination h2 - h1
      rw [hdiff]
      exact Formalism.FG.SolveVAux.low_neg (Formalism.FG.SolveVAux.low_subst_sub hL1t hL1t' ih (hg2 i))
  have htt : t = t' := by
    funext i
    ext d
    have hd := hlow (d.degree + 1) i d (Nat.lt_succ_self _)
    rw [map_sub] at hd
    exact sub_eq_zero.mp hd
  exact ⟨h, hh0, hhI, fun c => congrFun htt c⟩
end Formalism.L2.FormalSeriesBounds.AbstractGermZero
