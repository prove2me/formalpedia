-- Prove2me | solution 1 for CuspForm.exists_gamma1_div_coe_eq_heckeU_of_dvd_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/39f7b6d5-9e51-5cac-80e6-fd9990ac679b

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_ModularForm_mdifferentiable_heckeU
import Theorems.Thm_CuspFormClass_isZeroAt_heckeU
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_gamma1_div_coe_eq_heckeU_of_dvd_div

set_option autoImplicit false

open CongruenceSubgroup ModularForm UpperHalfPlane
open scoped ModularForm UpperHalfPlane MatrixGroups

noncomputable section

namespace ULowerGamma1

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

@[scoped simp] theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

theorem val_mapGL_eq (g : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![((g 0 0 : ℤ) : ℝ), ((g 0 1 : ℤ) : ℝ); ((g 1 0 : ℤ) : ℝ), ((g 1 1 : ℤ) : ℝ)] := by
  ext i j
  rw [mapGL_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem det_entries (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := γ.det_coe
  rwa [Matrix.det_fin_two] at h

theorem denom_SL (γ : SL(2, ℤ)) (τ : ℍ) :
    denom (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) τ
      = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) :=
  ModularGroup.denom_apply γ τ

theorem SL_slash_apply' (k : ℤ) (F : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    (F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) τ
      = F (γ • τ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (-k) := by
  have h := ModularForm.SL_slash_apply (f := F) (k := k) γ τ
  rw [ModularGroup.denom_apply] at h
  exact h

theorem denom_SL_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  rw [← denom_SL]
  exact denom_ne_zero _ τ

theorem sum_slash {ι : Type*} (s : Finset ι) (k : ℤ) (F : ι → ℍ → ℂ) (g : GL (Fin 2) ℝ) :
    (∑ i ∈ s, F i) ∣[k] g = ∑ i ∈ s, F i ∣[k] g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

section neb

variable {M : ℕ} {k : ℤ}

theorem slash_eq_smul_of_hasNebentypus {ε : DirichletCharacter ℂ M} {g : CuspForm Γ₁(M) k}
    (hg : CuspForm.HasNebentypus ε g) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
      = ε ((γ 1 1 : ℤ) : ZMod M) • (⇑g : ℍ → ℂ) := by
  funext τ
  rw [SL_slash_apply', hg γ hγ τ, Pi.smul_apply, smul_eq_mul]
  have hne := denom_SL_ne_zero γ τ
  have hk : (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k ≠ 0 := zpow_ne_zero k hne
  rw [zpow_neg]
  field_simp

theorem hasNebentypus_of_slash_eq_smul {ε : DirichletCharacter ℂ M} {g : CuspForm Γ₁(M) k}
    (hg : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
      (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
        = ε ((γ 1 1 : ℤ) : ZMod M) • (⇑g : ℍ → ℂ)) :
    CuspForm.HasNebentypus ε g := by
  intro γ hγ τ
  have h := congrFun (hg γ hγ) τ
  rw [SL_slash_apply', Pi.smul_apply, smul_eq_mul] at h
  have hne := denom_SL_ne_zero γ τ
  have hk : (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (-k) ≠ 0 := zpow_ne_zero _ hne
  have h2 : g (γ • τ) = ε ((γ 1 1 : ℤ) : ZMod M) * g τ *
      (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k := by
    have := congrArg (fun z => z * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k) h
    rwa [mul_assoc, ← zpow_add₀ hne, neg_add_cancel, zpow_zero, mul_one] at this
  rw [h2]
  ring

end neb

section cocycle

variable {ℓ : ℕ}

def cocycleMat (ℓ : ℕ) (γ : SL(2, ℤ)) (j j' b' : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![γ 0 0 + j * γ 1 0, b'; ℓ * γ 1 0, γ 1 1 - γ 1 0 * j']

theorem det_cocycleMat (γ : SL(2, ℤ)) {j j' b' : ℤ}
    (hb' : (ℓ : ℤ) * b' = γ 0 1 + j * γ 1 1 - (γ 0 0 + j * γ 1 0) * j') :
    (cocycleMat ℓ γ j j' b').det = 1 := by
  rw [cocycleMat, Matrix.det_fin_two_of]
  linear_combination (-(γ 1 0)) * hb' + det_entries γ

def cocycleSL (ℓ : ℕ) (γ : SL(2, ℤ)) (j j' b' : ℤ)
    (hb' : (ℓ : ℤ) * b' = γ 0 1 + j * γ 1 1 - (γ 0 0 + j * γ 1 0) * j') : SL(2, ℤ) :=
  ⟨cocycleMat ℓ γ j j' b', det_cocycleMat γ hb'⟩

@[scoped simp] theorem cocycleSL_apply (γ : SL(2, ℤ)) (j j' b' : ℤ)
    (hb' : (ℓ : ℤ) * b' = γ 0 1 + j * γ 1 1 - (γ 0 0 + j * γ 1 0) * j') (i i' : Fin 2) :
    (cocycleSL ℓ γ j j' b' hb') i i' = cocycleMat ℓ γ j j' b' i i' := rfl

theorem cocycleSL_00 (γ : SL(2, ℤ)) (j j' b' : ℤ) (hb') :
    (cocycleSL ℓ γ j j' b' hb') 0 0 = γ 0 0 + j * γ 1 0 := rfl
theorem cocycleSL_01 (γ : SL(2, ℤ)) (j j' b' : ℤ) (hb') :
    (cocycleSL ℓ γ j j' b' hb') 0 1 = b' := rfl
theorem cocycleSL_10 (γ : SL(2, ℤ)) (j j' b' : ℤ) (hb') :
    (cocycleSL ℓ γ j j' b' hb') 1 0 = ℓ * γ 1 0 := rfl
theorem cocycleSL_11 (γ : SL(2, ℤ)) (j j' b' : ℤ) (hb') :
    (cocycleSL ℓ γ j j' b' hb') 1 1 = γ 1 1 - γ 1 0 * j' := rfl

theorem heckeMatrix_mul_eq (hℓ : ℓ ≠ 0) (γ : SL(2, ℤ)) (j j' : ℕ) (b' : ℤ)
    (hb' : (ℓ : ℤ) * b' = γ 0 1 + j * γ 1 1 - (γ 0 0 + j * γ 1 0) * j') :
    heckeMatrix ℓ j * (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ (cocycleSL ℓ γ j j' b' hb') : GL (Fin 2) ℝ)
          * heckeMatrix ℓ j' := by
  have hb'R : (ℓ : ℝ) * (b' : ℝ) = γ 0 1 + j * γ 1 1 - (γ 0 0 + j * γ 1 0) * j' := by
    exact_mod_cast hb'
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_heckeMatrix hℓ, val_heckeMatrix hℓ, val_mapGL_eq,
    val_mapGL_eq, cocycleSL_00, cocycleSL_01, cocycleSL_10, cocycleSL_11]
  push_cast
  simp only [Matrix.mul_fin_two]
  ext i i'
  fin_cases i <;> fin_cases i'
  · simp
  · simp; linear_combination -hb'R
  · simp
  · simp; ring

end cocycle

section residues

variable {L ℓ : ℕ}

def perm (ℓ : ℕ) (γ : SL(2, ℤ)) (r : ZMod ℓ) : ZMod ℓ :=
  (γ 1 1 : ZMod ℓ) * ((γ 0 1 : ZMod ℓ) + r * (γ 1 1 : ZMod ℓ))

def permInv (ℓ : ℕ) (γ : SL(2, ℤ)) (r : ZMod ℓ) : ZMod ℓ :=
  (γ 0 0 : ZMod ℓ) * ((γ 0 0 : ZMod ℓ) * r - (γ 0 1 : ZMod ℓ))

theorem ad_eq_one {γ : SL(2, ℤ)} (hc : (ℓ : ℤ) ∣ γ 1 0) :
    (γ 0 0 : ZMod ℓ) * (γ 1 1 : ZMod ℓ) = 1 := by
  have hc0 : ((γ 1 0 : ℤ) : ZMod ℓ) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
  have := congrArg (Int.cast : ℤ → ZMod ℓ) (det_entries γ)
  push_cast at this
  rwa [hc0, mul_zero, sub_zero] at this

theorem permInv_perm {γ : SL(2, ℤ)} (hc : (ℓ : ℤ) ∣ γ 1 0) (r : ZMod ℓ) :
    permInv ℓ γ (perm ℓ γ r) = r := by
  have h := ad_eq_one hc
  unfold perm permInv
  linear_combination ((γ 0 0 : ZMod ℓ) * (γ 0 1 : ZMod ℓ)
    + r * ((γ 0 0 : ZMod ℓ) * (γ 1 1 : ZMod ℓ) + 1)) * h

theorem perm_permInv {γ : SL(2, ℤ)} (hc : (ℓ : ℤ) ∣ γ 1 0) (r : ZMod ℓ) :
    perm ℓ γ (permInv ℓ γ r) = r := by
  have h := ad_eq_one hc
  unfold perm permInv
  linear_combination (r * ((γ 0 0 : ZMod ℓ) * (γ 1 1 : ZMod ℓ) + 1)
    - (γ 1 1 : ZMod ℓ) * (γ 0 1 : ZMod ℓ)) * h

theorem dvd_numerator [NeZero ℓ] {γ : SL(2, ℤ)} (hc : (ℓ : ℤ) ∣ γ 1 0) (j : ℕ) :
    (ℓ : ℤ) ∣ γ 0 1 + j * γ 1 1 - (γ 0 0 + j * γ 1 0) * ((perm ℓ γ (j : ZMod ℓ)).val : ℤ) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hc0 : ((γ 1 0 : ℤ) : ZMod ℓ) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
  have h := ad_eq_one hc
  push_cast
  rw [ZMod.natCast_zmod_val, hc0, perm]
  linear_combination (-((γ 0 1 : ZMod ℓ) + (j : ZMod ℓ) * (γ 1 1 : ZMod ℓ))) * h

end residues

section main

variable {N : ℕ} {k : ℤ} {ℓ : ℕ}

theorem isUnit_entry {M : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    IsUnit ((γ 1 1 : ℤ) : ZMod M) := by
  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := by simpa using Gamma0_mem.mp hγ
  have := congrArg (Int.cast : ℤ → ZMod M) (det_entries γ)
  push_cast at this
  rw [hc, mul_zero, sub_zero] at this
  exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact this)

theorem heckeU_slash_of_mem_Gamma0_div (hℓN : ℓ ∣ N) (hℓ : ℓ ∣ N / ℓ) (hℓ0 : ℓ ≠ 0)
    (ε' : DirichletCharacter ℂ (N / ℓ)) (F : ℍ → ℂ)
    (hF : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 N →
      F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ)
        = ε' ((γ' 1 1 : ℤ) : ZMod (N / ℓ)) • F)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / ℓ)) :
    heckeU k ℓ F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
      = ε' ((γ 1 1 : ℤ) : ZMod (N / ℓ)) • heckeU k ℓ F := by
  haveI : NeZero ℓ := ⟨hℓ0⟩
  have hLc : ((N / ℓ : ℕ) : ℤ) ∣ γ 1 0 := by
    have := Gamma0_mem.mp hγ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  have hc : (ℓ : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hℓ).trans hLc

  have hdata : ∀ j : ℕ, ∃ b' : ℤ,
      (ℓ : ℤ) * b' = γ 0 1 + j * γ 1 1 - (γ 0 0 + j * γ 1 0) * ((perm ℓ γ (j : ZMod ℓ)).val : ℤ) :=
    fun j => ⟨_, Int.mul_ediv_cancel' (dvd_numerator hc j)⟩
  choose b' hb' using hdata

  have hterm : ∀ j : ℕ, (F ∣[k] heckeMatrix ℓ j) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
      = ε' ((γ 1 1 : ℤ) : ZMod (N / ℓ)) • (F ∣[k] heckeMatrix ℓ (perm ℓ γ (j : ZMod ℓ)).val) := by
    intro j
    set γ' := cocycleSL ℓ γ j ((perm ℓ γ (j : ZMod ℓ)).val) (b' j) (hb' j) with hγ'
    have hγ'0 : γ' ∈ Gamma0 N := by
      rw [Gamma0_mem, hγ', cocycleSL_10, ZMod.intCast_zmod_eq_zero_iff_dvd]
      obtain ⟨t, ht⟩ := hLc
      rw [ht, ← mul_assoc, ← Nat.cast_mul, Nat.mul_div_cancel' hℓN]
      exact dvd_mul_right _ _
    rw [← SlashAction.slash_mul, heckeMatrix_mul_eq hℓ0 γ j _ (b' j) (hb' j), SlashAction.slash_mul,
      ← hγ', hF γ' hγ'0, ModularForm.smul_slash, σ_heckeMatrix]
    simp only [ContinuousAlgEquiv.refl_apply]
    congr 1

    congr 1
    rw [hγ', cocycleSL_11]
    push_cast
    have : ((γ 1 0 : ℤ) : ZMod (N / ℓ)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hLc
    rw [this, zero_mul, sub_zero]

  rw [heckeU, sum_slash]
  simp_rw [hterm]
  rw [← Finset.smul_sum]
  congr 1
  symm
  refine Finset.sum_nbij' (fun j => (permInv ℓ γ (j : ZMod ℓ)).val)
    (fun j => (perm ℓ γ (j : ZMod ℓ)).val) ?_ ?_ ?_ ?_ ?_
  · intro j _; exact Finset.mem_range.mpr (ZMod.val_lt _)
  · intro j _; exact Finset.mem_range.mpr (ZMod.val_lt _)
  · intro j hj
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, perm_permInv hc]
    exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · intro j hj
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, permInv_perm hc]
    exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · intro j hj
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, perm_permInv hc]
    rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hj)]

variable [NeZero N]

theorem neZero_div (hℓN : ℓ ∣ N) : NeZero (N / ℓ) := by
  refine ⟨fun h => ?_⟩
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · exact NeZero.ne N (zero_dvd_iff.mp hℓN)
  · exact NeZero.ne N (Nat.eq_zero_of_dvd_of_div_eq_zero hℓN h)

theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁(M)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

def lowerForm (hℓN : ℓ ∣ N) (hℓ : ℓ ∣ N / ℓ) (ε' : DirichletCharacter ℂ (N / ℓ))
    (f : CuspForm Γ₁(N) k)
    (hf : CuspForm.HasNebentypus (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hℓN) ε') f) :
    CuspForm Γ₁(N / ℓ) k :=
  haveI : NeZero (N / ℓ) := neZero_div hℓN
  have hℓ0 : ℓ ≠ 0 := fun h => NeZero.ne N (zero_dvd_iff.mp (h ▸ hℓN))
  have hF : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 N →
      (⇑f : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ)
        = ε' ((γ' 1 1 : ℤ) : ZMod (N / ℓ)) • (⇑f : ℍ → ℂ) := by
    intro γ' hγ'
    rw [slash_eq_smul_of_hasNebentypus hf hγ']
    congr 1
    have hu := isUnit_entry hγ'
    rw [← hu.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd ε' (Nat.div_dvd_of_dvd hℓN),
      hu.unit_spec, ZMod.cast_intCast (Nat.div_dvd_of_dvd hℓN)]
  { toFun := heckeU k ℓ ⇑f
    slash_action_eq' := by
      intro A hA
      obtain ⟨γ, hγ, rfl⟩ := hA
      have hγ0 : γ ∈ Gamma0 (N / ℓ) := by
        rw [Gamma0_mem]; exact (Gamma1_mem _ _ |>.mp hγ).2.2
      have hd : ((γ 1 1 : ℤ) : ZMod (N / ℓ)) = 1 := (Gamma1_mem _ _ |>.mp hγ).2.1
      rw [heckeU_slash_of_mem_Gamma0_div hℓN hℓ hℓ0 ε' ⇑f hF hγ0, hd, map_one, one_smul]
    holo' := ModularForm.mdifferentiable_heckeU f.holo' k ℓ
    zero_at_cusps' := by
      intro c hc
      refine CuspFormClass.isZeroAt_heckeU f ℓ ?_
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
      exact hc }

theorem coe_lowerForm (hℓN : ℓ ∣ N) (hℓ : ℓ ∣ N / ℓ) (ε' : DirichletCharacter ℂ (N / ℓ))
    (f : CuspForm Γ₁(N) k)
    (hf : CuspForm.HasNebentypus (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hℓN) ε') f) :
    (⇑(lowerForm hℓN hℓ ε' f hf) : ℍ → ℂ) = heckeU k ℓ ⇑f := rfl

theorem main (hℓN : ℓ ∣ N) (hℓ : ℓ ∣ N / ℓ) (ε' : DirichletCharacter ℂ (N / ℓ))
    (f : CuspForm Γ₁(N) k)
    (hf : CuspForm.HasNebentypus (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hℓN) ε') f) :
    ∃ h : CuspForm Γ₁(N / ℓ) k,
      (⇑h : ℍ → ℂ) = heckeU k ℓ ⇑f ∧
      (∀ n : ℕ, ModularFormClass.qCoeff h n = ModularFormClass.qCoeff f (ℓ * n)) ∧
      CuspForm.HasNebentypus ε' h := by
  haveI : NeZero (N / ℓ) := neZero_div hℓN
  have hℓ0 : ℓ ≠ 0 := fun h => NeZero.ne N (zero_dvd_iff.mp (h ▸ hℓN))
  refine ⟨lowerForm hℓN hℓ ε' f hf, rfl, fun n => ?_, ?_⟩
  · rw [coe_lowerForm, ModularFormClass.qCoeff_heckeU f (one_mem_strictPeriods N) hℓ0 n,
      coeffHeckeU_apply, mul_comm]
  · refine hasNebentypus_of_slash_eq_smul fun γ hγ => ?_
    have hF : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 N →
        (⇑f : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ)
          = ε' ((γ' 1 1 : ℤ) : ZMod (N / ℓ)) • (⇑f : ℍ → ℂ) := by
      intro γ' hγ'
      rw [slash_eq_smul_of_hasNebentypus hf hγ']
      congr 1
      have hu := isUnit_entry hγ'
      rw [← hu.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd ε' (Nat.div_dvd_of_dvd hℓN),
        hu.unit_spec, ZMod.cast_intCast (Nat.div_dvd_of_dvd hℓN)]
    rw [coe_lowerForm]
    exact heckeU_slash_of_mem_Gamma0_div hℓN hℓ hℓ0 ε' ⇑f hF hγ

end main

end ULowerGamma1
p2m_reactivate "P2MW.S_CuspForm_exists_gamma1_div_coe_eq_heckeU_of_dvd_div.ULowerGamma1"

end
p2m_reactivate "P2MW.S_CuspForm_exists_gamma1_div_coe_eq_heckeU_of_dvd_div.ULowerGamma1"

open scoped MatrixGroups in
theorem solution
    {N : ℕ} [NeZero N] (k : ℤ) {ℓ : ℕ} (hℓN : ℓ ∣ N) (hℓ : ℓ ∣ N / ℓ)
    (ε' : DirichletCharacter ℂ (N / ℓ)) (f : CuspForm (CongruenceSubgroup.Gamma1 N) k)
    (hf : CuspForm.HasNebentypus
      (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hℓN) ε') f) :
    ∃ h : CuspForm (CongruenceSubgroup.Gamma1 (N / ℓ)) k,
      (⇑h : UpperHalfPlane → ℂ) = ModularForm.heckeU k ℓ ⇑f ∧
      (∀ n : ℕ, ModularFormClass.qCoeff h n = ModularFormClass.qCoeff f (ℓ * n)) ∧
      CuspForm.HasNebentypus ε' h :=
  ULowerGamma1.main hℓN hℓ ε' f hf

end S_CuspForm_exists_gamma1_div_coe_eq_heckeU_of_dvd_div
end P2MW
export P2MW.S_CuspForm_exists_gamma1_div_coe_eq_heckeU_of_dvd_div (solution)
