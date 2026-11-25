-- Prove2me | solution 1 for Formalism.FG.HeightVAux.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:37:54.207091+00:00
-- url     : https://prove2.me/submissions/d0dc7042-5016-4129-9f53-3fac30d9deb1

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_HeightV
import Theorems.Thm_Formalism_FG_HeightVAux_subst_shift_shiftLog
import Theorems.Thm_Formalism_FG_HeightVAux_hasSubst0
import Theorems.Thm_Formalism_FG_HeightVAux_hasSubst_vX
import Theorems.Thm_Formalism_FG_HeightVAux_hasSubst_vY
import Theorems.Thm_Formalism_FG_HeightVAux_constantCoeff_atXv
import Theorems.Thm_Formalism_FG_HeightVAux_constantCoeff_atYv
import Theorems.Thm_Formalism_FG_HeightVAux_subst_atXv
import Theorems.Thm_Formalism_FG_HeightVAux_subst_atYv
import Theorems.Thm_Formalism_FG_HeightVAux_atXv_subst
import Theorems.Thm_Formalism_FG_HeightVAux_atYv_subst
import Theorems.Thm_Formalism_FG_HeightVAux_map_atXv
import Theorems.Thm_Formalism_FG_HeightVAux_map_atYv
import Theorems.Thm_Formalism_FG_HeightVAux_coe_map_injective
import Theorems.Thm_Formalism_FG_HeightVAux_constantCoeff_of_map
import Theorems.Thm_Formalism_FG_HeightVAux_map_liftZ
import Theorems.Thm_Formalism_FG_HeightVAux_dvd_of_norm_le
import Theorems.Thm_Formalism_FG_HeightVAux_toZMod_eq_zero_iff
import Theorems.Thm_Formalism_FG_frobenius_lift_padic_square
import Theorems.Thm_Formalism_FG_functional_equation_hom_vector
import Theorems.Thm_Formalism_FG_shift_functional_equation
import Theorems.Thm_Formalism_FG_subst_injective_vector


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.HeightVAux
open MvPowerSeries Formalism.G Formalism.LT
open PadicInt
namespace Formalism.FG.HeightVAux
theorem _root_.solution (hC : Formalism.FG.FunEqCongrV.{0, 0, 0}) : Formalism.FG.ShiftHeight := by
  intro l _ m _ F hF
  have hlp : l.Prime := Fact.out
  have hl2 : 2 ≤ l := hlp.two_le
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hlp.ne_zero
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast hlp.ne_zero
  obtain ⟨hf, hfeq⟩ := Formalism.FG.shift_functional_equation.{0} ℚ_[l] l hlp m (RingHom.id ℚ_[l])
  have hS := Formalism.FG.frobenius_lift_padic_square l
  have hM : IntegralMat (shiftMat ℚ_[l] m) := by
    intro j k; unfold shiftMat; split_ifs <;> simp
  have hXI : ∀ j : ZMod m, IntegralMv (X j : MvPowerSeries (ZMod m) ℚ_[l]) := by
    intro j d; rw [coeff_X]; split_ifs <;> simp
  have hfE : IsFunEqTypeV l (l ^ 2) hq (RingHom.id ℚ_[l]) (shiftMat ℚ_[l] m)
      (shiftLog ℚ_[l] l m) := by
    intro j; rw [hfeq j]; exact hXI j

  have hsum : ∀ j : ZMod m, ∑ k, shiftMat ℚ_[l] m j k •
        MvPowerSeries.expand (l ^ 2) hq
          (MvPowerSeries.map (RingHom.id ℚ_[l]) (shiftLog ℚ_[l] l m k)) =
      MvPowerSeries.expand (l ^ 2) hq (shiftLog ℚ_[l] l m (j - 1)) := by
    intro j
    simp [shiftMat]
  have hexp : ∀ j : ZMod m, MvPowerSeries.expand (l ^ 2) hq (shiftLog ℚ_[l] l m (j - 1)) =
      (l : ℚ_[l]) • (shiftLog ℚ_[l] l m j - X j) := by
    intro j
    have h1 := hfeq j
    rw [hsum j] at h1
    rw [← h1, sub_sub_cancel, smul_smul, mul_inv_cancel₀ hl0, one_smul]

  have hgE : IsFunEqTypeV l (l ^ 2) hq (RingHom.id ℚ_[l]) (shiftMat ℚ_[l] m)
      (fun j => (l : ℚ_[l]) • shiftLog ℚ_[l] l m j) := by
    intro j
    have : (l : ℚ_[l]) • shiftLog ℚ_[l] l m j - ((l : ℕ) : ℚ_[l])⁻¹ • ∑ k, shiftMat ℚ_[l] m j k •
        MvPowerSeries.expand (l ^ 2) hq
          (MvPowerSeries.map (RingHom.id ℚ_[l]) ((l : ℚ_[l]) • shiftLog ℚ_[l] l m k)) =
        (l : ℚ_[l]) • (X j : MvPowerSeries (ZMod m) ℚ_[l]) := by
      have h2 : ∀ k, MvPowerSeries.map (RingHom.id ℚ_[l]) ((l : ℚ_[l]) • shiftLog ℚ_[l] l m k) =
          (l : ℚ_[l]) • MvPowerSeries.map (RingHom.id ℚ_[l]) (shiftLog ℚ_[l] l m k) := by
        intro k; simp
      have h3 : ∑ k, shiftMat ℚ_[l] m j k • (l : ℚ_[l]) • MvPowerSeries.expand (l ^ 2) hq
            (MvPowerSeries.map (RingHom.id ℚ_[l]) (shiftLog ℚ_[l] l m k)) =
          (l : ℚ_[l]) • ∑ k, shiftMat ℚ_[l] m j k • MvPowerSeries.expand (l ^ 2) hq
            (MvPowerSeries.map (RingHom.id ℚ_[l]) (shiftLog ℚ_[l] l m k)) := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
      simp only [h2, map_smul]
      rw [h3, hsum j, hexp j]
      rw [smul_smul ((l : ℚ_[l])⁻¹), inv_mul_cancel₀ hl0, one_smul, ← smul_sub, sub_sub_cancel]
    rw [this]
    intro d
    rw [coeff_smul, norm_mul]
    exact mul_le_one₀ Padic.norm_p_lt_one.le (norm_nonneg _) (hXI j d)
  have hg0 : ∀ j : ZMod m, constantCoeff ((l : ℚ_[l]) • shiftLog ℚ_[l] l m j) = 0 := by
    intro j
    rw [smul_eq_C_mul, map_mul, hf.1 j, mul_zero]
  obtain ⟨h, hh0, hhI, hh⟩ := Formalism.FG.functional_equation_hom_vector.{0, 0, 0} ℚ_[l] l (l ^ 2) hq
    (RingHom.id ℚ_[l]) hS (ZMod m) (shiftMat ℚ_[l] m) hM (shiftLog ℚ_[l] l m) hf hfE (ZMod m)
    (fun j => (l : ℚ_[l]) • shiftLog ℚ_[l] l m j) hg0 hgE
  set e : ZMod m → MvPowerSeries (ZMod m) ℤ_[l] := fun i => liftZ (h i) (hhI i) with he_def
  have he : ∀ i, map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (e i) = h i :=
    fun i => map_liftZ (h i) (hhI i)
  have he0 : ∀ i, constantCoeff (e i) = 0 :=
    fun i => constantCoeff_of_map _ (by rw [he i]; exact hh0 i)
  have hF0 : ∀ i, constantCoeff (F i) = 0 := fun i => constantCoeff_of_map _ (hF.1 i)

  set FK : ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℚ_[l] :=
    fun i => map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (F i) with hFK
  set EK : Fin 2 × ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℚ_[l] :=
    fun x => if x.1 = 0 then atXv (h x.2) else atYv (h x.2) with hEK
  have hFKs : HasSubst FK := hasSubst0 FK hF.1
  have hhs : HasSubst h := hasSubst0 h hh0
  have hEK0 : ∀ x, constantCoeff (EK x) = 0 := by
    intro x
    simp only [hEK]
    split_ifs
    · exact constantCoeff_atXv (hh0 _)
    · exact constantCoeff_atYv (hh0 _)
  have hEKs : HasSubst EK := hasSubst0 EK hEK0

  have hkey : (fun i => subst FK (h i)) = (fun i => subst EK (FK i)) := by
    refine Formalism.FG.subst_injective_vector.{0, 0, 0} ℚ_[l] (ZMod m) (Fin 2 × ZMod m)
      (shiftLog ℚ_[l] l m) _ _ hf
      (fun i => constantCoeff_subst_eq_zero hFKs hF.1 (hh0 i))
      (fun i => constantCoeff_subst_eq_zero hEKs hEK0 (hF.1 i)) (fun j => ?_)
    rw [← subst_comp_subst_apply hhs hFKs, hh j, subst_smul hFKs, hF.2.2 j,
      ← subst_comp_subst_apply hFKs hEKs, hF.2.2 j, subst_add hEKs,
      subst_atXv EK hEKs, subst_atYv EK hEKs]
    have hx : (fun i => EK (0, i)) = fun i => atXv (h i) := by
      funext i; simp [hEK]
    have hy : (fun i => EK (1, i)) = fun i => atYv (h i) := by
      funext i; simp [hEK]
    rw [hx, hy, ← atXv_subst h hh0, ← atYv_subst h hh0, hh j, smul_add]
    unfold atXv atYv
    rw [subst_smul hasSubst_vX, subst_smul hasSubst_vY]
  have hFs : HasSubst F := hasSubst0 F hF0
  have hE0 : ∀ x : Fin 2 × ZMod m, constantCoeff
      ((fun x : Fin 2 × ZMod m => if x.1 = 0 then atXv (e x.2) else atYv (e x.2)) x) = 0 := by
    intro x
    simp only
    split_ifs
    · exact constantCoeff_atXv (he0 _)
    · exact constantCoeff_atYv (he0 _)
  have hHom : IsHomV F F e := by
    refine ⟨he0, fun i => ?_⟩
    apply coe_map_injective
    rw [map_subst hFs, map_subst (hasSubst0 _ hE0), he i]
    have := congrFun hkey i
    rw [this]
    congr 1
    funext x
    simp only [hEK]
    split_ifs
    · rw [map_atXv, he]
    · rw [map_atYv, he]
  have hfe : (fun k => map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (e k)) = h := funext he

  set β : ZMod m → MvPowerSeries (ZMod m) ℚ_[l] := fun k => X (k - 1) ^ (l ^ 2) with hβ
  have hβ0 : ∀ k, constantCoeff (β k) = 0 := by
    intro k; simp [hβ, hlp.ne_zero]
  have hβI : ∀ k, IntegralMv (β k) := by
    intro k d; simp only [hβ]; rw [coeff_X_pow]; split_ifs <;> simp
  have hρs : HasSubst (fun k : ZMod m => (X (k - 1) : MvPowerSeries (ZMod m) ℚ_[l])) :=
    hasSubst0 _ (fun _ => constantCoeff_X _)
  have hβf : ∀ j, subst β (shiftLog ℚ_[l] l m j) =
      MvPowerSeries.expand (l ^ 2) hq (shiftLog ℚ_[l] l m (j - 1)) := by
    intro j
    have : β = fun k => MvPowerSeries.expand (l ^ 2) hq (X (k - 1)) := by
      funext k; simp [hβ]
    rw [this, ← expand_subst _ _ hρs, subst_shift_shiftLog hl2]
  have hdiv := (hC ℚ_[l] l (l ^ 2) hq (RingHom.id _) hS (ZMod m) (shiftMat ℚ_[l] m) hM
    (shiftLog ℚ_[l] l m) hf hfE (ZMod m) h β hh0 hβ0 hhI hβI 1 le_rfl).mpr (by
      intro j d
      rw [hh j, hβf j, hexp j, ← smul_sub, sub_sub_cancel, pow_one, coeff_smul, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hXI j d))
  have hcongr : ∀ j n, (l : ℤ_[l]) ∣ coeff n (e j - X (j - 1) ^ (l ^ 2)) := by
    intro j n
    apply dvd_of_norm_le
    have hmap : h j - β j =
        map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (e j - X (j - 1) ^ (l ^ 2)) := by
      rw [map_sub, map_pow, map_X, he j]
    have := hdiv j n
    rw [hmap, coeff_map, pow_one] at this
    exact this

  have hred : ∀ j, map (PadicInt.toZMod : ℤ_[l] →+* ZMod l) (e j) = X (j - 1) ^ (l ^ 2) := by
    intro j
    have h0 : map (PadicInt.toZMod : ℤ_[l] →+* ZMod l) (e j - X (j - 1) ^ (l ^ 2)) = 0 := by
      ext n
      rw [coeff_map, map_zero, toZMod_eq_zero_iff]
      exact hcongr j n
    rwa [map_sub, map_pow, map_X, sub_eq_zero] at h0
  have hit : ∀ n : ℕ, (∀ i, constantCoeff (iterV e n i) = 0) ∧
      ∀ i, map (PadicInt.toZMod : ℤ_[l] →+* ZMod l) (iterV e n i) =
        X (i - (n : ZMod m)) ^ ((l ^ 2) ^ n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simp [iterV]
      · simp [iterV, map_X]
    | succ n ih =>
      have hsucc : ∀ i, iterV e (n + 1) i = subst (iterV e n) (e i) := by
        intro i
        simp only [iterV]
        rw [Function.iterate_succ_apply']
      have hs1 : HasSubst (iterV e n) := hasSubst0 _ ih.1
      refine ⟨fun i => ?_, fun i => ?_⟩
      · rw [hsucc]
        exact constantCoeff_subst_eq_zero hs1 ih.1 (he0 i)
      · rw [hsucc, map_subst hs1, hred i, subst_pow (hs1.map _), subst_X (hs1.map _), ih.2,
          ← pow_mul, ← pow_succ]
        congr 2
        push_cast
        ring
  refine ⟨e, hHom, fun j => by rw [hfe]; exact hh j, hcongr, fun j n => ?_⟩
  rw [← toZMod_eq_zero_iff, ← coeff_map, map_sub, (hit m).2 j, ZMod.natCast_self, sub_zero,
    ← pow_mul, map_pow, map_X, sub_self, map_zero]
end Formalism.FG.HeightVAux
