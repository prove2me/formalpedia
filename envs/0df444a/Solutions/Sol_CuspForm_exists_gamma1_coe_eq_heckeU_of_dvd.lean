-- Prove2me | solution 1 for CuspForm.exists_gamma1_coe_eq_heckeU_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/36f68f4b-d895-59c5-87a5-580c59627da1

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_CuspFormClass_isZeroAt_heckeU
import Theorems.Thm_ModularForm_mdifferentiable_heckeU
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_gamma1_coe_eq_heckeU_of_dvd

set_option autoImplicit false

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace HeckeUGamma1

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

theorem heckeMatrix_mul_of_eq {ℓ : ℕ} (hℓ : ℓ ≠ 0) (g : SL(2, ℤ)) (j j' : ℕ) (e : ℤ)
    (he : g 0 1 + j * g 1 1 = j' * (g 0 0 + j * g 1 0) + ℓ * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = ℓ * g 1 0 ∧ g' 1 1 = g 1 1 - g 1 0 * j' ∧
      heckeMatrix ℓ j * mapGL ℝ g = mapGL ℝ g' * heckeMatrix ℓ j' := by
  have hdet := det_eq g
  refine ⟨⟨!![g 0 0 + j * g 1 0, e; ℓ * g 1 0, g 1 1 - g 1 0 * j'], ?_⟩, rfl, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 1 0) * he
  · ext i i'
    fin_cases i <;> fin_cases i' <;>
      simp [hℓ, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

def perm {ℓ : ℕ} (g : SL(2, ℤ)) (hc : ((g 1 0 : ℤ) : ZMod ℓ) = 0) : ZMod ℓ ≃ ZMod ℓ where
  toFun j := ((g 1 1 : ℤ) : ZMod ℓ) * (((g 0 1 : ℤ) : ZMod ℓ) + j * ((g 1 1 : ℤ) : ZMod ℓ))
  invFun j' := ((g 0 0 : ℤ) : ZMod ℓ) * (((g 0 0 : ℤ) : ZMod ℓ) * j' - ((g 0 1 : ℤ) : ZMod ℓ))
  left_inv j := by
    have had : ((g 0 0 : ℤ) : ZMod ℓ) * ((g 1 1 : ℤ) : ZMod ℓ) = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod ℓ) (det_eq g)
      push_cast at this
      rw [hc] at this
      linear_combination this
    simp only
    linear_combination (((g 0 0 : ℤ) : ZMod ℓ) * ((g 0 1 : ℤ) : ZMod ℓ) +
      j + j * ((g 0 0 : ℤ) : ZMod ℓ) * ((g 1 1 : ℤ) : ZMod ℓ)) * had
  right_inv j' := by
    have had : ((g 0 0 : ℤ) : ZMod ℓ) * ((g 1 1 : ℤ) : ZMod ℓ) = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod ℓ) (det_eq g)
      push_cast at this
      rw [hc] at this
      linear_combination this
    simp only
    linear_combination (j' + ((g 0 0 : ℤ) : ZMod ℓ) * ((g 1 1 : ℤ) : ZMod ℓ) * j'
      - ((g 0 1 : ℤ) : ZMod ℓ) * ((g 1 1 : ℤ) : ZMod ℓ)) * had

theorem perm_apply {ℓ : ℕ} (g : SL(2, ℤ)) (hc : ((g 1 0 : ℤ) : ZMod ℓ) = 0) (j : ZMod ℓ) :
    perm g hc j = ((g 1 1 : ℤ) : ZMod ℓ) * (((g 0 1 : ℤ) : ZMod ℓ) + j * ((g 1 1 : ℤ) : ZMod ℓ)) := rfl

theorem exists_cocycle {N ℓ : ℕ} (hℓ : ℓ ≠ 0) (hℓN : ℓ ∣ N) (g : SL(2, ℤ)) (hg : g ∈ Gamma0 N)
    (x : ZMod ℓ) :
    ∃ g' : SL(2, ℤ), (N : ℤ) ∣ g' 1 0 ∧ ((g' 1 1 : ℤ) : ZMod N) = ((g 1 1 : ℤ) : ZMod N) ∧
      heckeMatrix ℓ x.val * mapGL ℝ g =
        mapGL ℝ g' * heckeMatrix ℓ
          (perm g (by
            have hc : ((g 1 0 : ℤ) : ZMod N) = 0 := by simpa using Gamma0_mem.mp hg
            rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc ⊢
            exact dvd_trans (Int.natCast_dvd_natCast.mpr hℓN) hc) x).val := by
  haveI : NeZero ℓ := ⟨hℓ⟩
  have hcN : ((g 1 0 : ℤ) : ZMod N) = 0 := by simpa using Gamma0_mem.mp hg
  have hNc : (N : ℤ) ∣ g 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcN
  have hcℓ : ((g 1 0 : ℤ) : ZMod ℓ) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hℓN) hNc
  have had : ((g 0 0 : ℤ) : ZMod ℓ) * ((g 1 1 : ℤ) : ZMod ℓ) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod ℓ) (det_eq g)
    push_cast at this
    rw [hcℓ] at this
    linear_combination this
  set y : ZMod ℓ := perm g hcℓ x with hy

  obtain ⟨e, he⟩ : (ℓ : ℤ) ∣ g 0 1 + x.val * g 1 1 - y.val * (g 0 0 + x.val * g 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hcℓ, hy, perm_apply]
    linear_combination (-(((g 0 1 : ℤ) : ZMod ℓ)) - x * ((g 1 1 : ℤ) : ZMod ℓ)) * had
  obtain ⟨g', hc', hd', hmul⟩ := heckeMatrix_mul_of_eq hℓ g x.val y.val e (by linear_combination he)
  refine ⟨g', ?_, ?_, hmul⟩
  · rw [hc']
    exact dvd_mul_of_dvd_right hNc _
  · rw [hd']
    push_cast
    rw [hcN, zero_mul, sub_zero]

theorem sum_range_eq_sum_zmod {ℓ : ℕ} [NeZero ℓ] {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ j ∈ Finset.range ℓ, F j = ∑ x : ZMod ℓ, F x.val := by
  refine Finset.sum_nbij' (fun j : ℕ ↦ (j : ZMod ℓ)) (fun x : ZMod ℓ ↦ x.val) (fun _ _ ↦ Finset.mem_univ _)
    (fun x _ ↦ Finset.mem_range.mpr x.val_lt) (fun j hj ↦ ?_) (fun x _ ↦ ?_) (fun j hj ↦ ?_)
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · exact ZMod.natCast_zmod_val x
  · rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hj)]

theorem heckeU_eq_sum_zmod {ℓ : ℕ} [NeZero ℓ] (k : ℤ) (f : ℍ → ℂ) :
    heckeU k ℓ f = ∑ x : ZMod ℓ, f ∣[k] heckeMatrix ℓ x.val := by
  rw [heckeU_def]
  exact sum_range_eq_sum_zmod _

theorem heckeU_slash_eq_smul {N ℓ : ℕ} (hℓN : ℓ ∣ N) (k : ℤ) (f : ℍ → ℂ) (g : SL(2, ℤ))
    (hg : g ∈ Gamma0 N) (C : ℂ)
    (hf : ∀ g' : SL(2, ℤ), (N : ℤ) ∣ g' 1 0 → ((g' 1 1 : ℤ) : ZMod N) = ((g 1 1 : ℤ) : ZMod N) →
      f ∣[k] mapGL ℝ g' = C • f) :
    (heckeU k ℓ f) ∣[k] mapGL ℝ g = C • heckeU k ℓ f := by
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · simp
  haveI : NeZero ℓ := ⟨hℓ⟩
  have hcℓ : ((g 1 0 : ℤ) : ZMod ℓ) = 0 := by
    have hc : ((g 1 0 : ℤ) : ZMod N) = 0 := by simpa using Gamma0_mem.mp hg
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc ⊢
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hℓN) hc
  rw [heckeU_eq_sum_zmod, SlashAction.sum_slash, Finset.smul_sum]
  calc ∑ x : ZMod ℓ, (f ∣[k] heckeMatrix ℓ x.val) ∣[k] mapGL ℝ g
      = ∑ x : ZMod ℓ, C • f ∣[k] heckeMatrix ℓ (perm g hcℓ x).val := by
        refine Finset.sum_congr rfl fun x _ => ?_
        obtain ⟨g', hc', hd', hmul⟩ := exists_cocycle hℓ hℓN g hg x
        rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul, hf g' hc' hd', ModularForm.smul_slash,
          σ_heckeMatrix]
        rfl
    _ = ∑ x : ZMod ℓ, C • f ∣[k] heckeMatrix ℓ x.val :=
        Equiv.sum_comp (perm g hcℓ) (fun x ↦ C • f ∣[k] heckeMatrix ℓ x.val)

theorem mem_Gamma1_of {N : ℕ} {γ : SL(2, ℤ)} (hc : (N : ℤ) ∣ γ 1 0) (hd : ((γ 1 1 : ℤ) : ZMod N) = 1) :
    γ ∈ Gamma1 N := by
  have hc' : ((γ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
  have ha : ((γ 0 0 : ℤ) : ZMod N) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod N) (det_eq γ)
    push_cast at this
    rw [hc', hd, mul_one, mul_zero, sub_zero] at this
    exact this
  rw [Gamma1_mem]
  exact ⟨by simpa using ha, by simpa using hd, by simpa using hc'⟩

variable {N : ℕ} {k : ℤ}

def heckeUForm [NeZero N] {ℓ : ℕ} (hℓN : ℓ ∣ N) (f : CuspForm Γ₁(N) k) : CuspForm Γ₁(N) k where
  toFun := heckeU k ℓ ⇑f
  slash_action_eq' := by
    intro A hA
    obtain ⟨γ, hγ, rfl⟩ := hA
    have h1 := heckeU_slash_eq_smul hℓN k (⇑f) γ (Gamma1_in_Gamma0 N hγ) 1 (fun g' hc' hd' => by
      rw [one_smul]
      have hdγ : ((γ 1 1 : ℤ) : ZMod N) = 1 := by simpa using ((Gamma1_mem N γ).mp hγ).2.1
      exact SlashInvariantFormClass.slash_action_eq f _
        (Subgroup.mem_map_of_mem _ (mem_Gamma1_of hc' (hd'.trans hdγ))))
    rwa [one_smul] at h1
  holo' := ModularForm.mdifferentiable_heckeU f.holo' k ℓ
  zero_at_cusps' := fun hc => CuspFormClass.isZeroAt_heckeU f ℓ hc

theorem coe_heckeUForm [NeZero N] {ℓ : ℕ} (hℓN : ℓ ∣ N) (f : CuspForm Γ₁(N) k) :
    (⇑(heckeUForm hℓN f) : ℍ → ℂ) = heckeU k ℓ ⇑f := rfl

theorem one_mem_strictPeriods (L : ℕ) : (1 : ℝ) ∈ (Γ₁(L)).strictPeriods := by
  rw [strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

theorem qCoeff_heckeUForm [NeZero N] {ℓ : ℕ} (hℓN : ℓ ∣ N) (f : CuspForm Γ₁(N) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(heckeUForm hℓN f)) n = ModularFormClass.qCoeff (⇑f) (ℓ * n) := by
  have hℓ : ℓ ≠ 0 := fun h0 => (NeZero.ne N) (Nat.eq_zero_of_zero_dvd (h0 ▸ hℓN))
  rw [coe_heckeUForm, ModularFormClass.qCoeff_heckeU f (one_mem_strictPeriods N) hℓ n,
    coeffHeckeU_apply, mul_comm]

theorem denom_mapGL (γ : SL(2, ℤ)) (τ : ℍ) :
    denom (mapGL ℝ γ : GL (Fin 2) ℝ) τ = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
  simp [denom]

theorem slash_mapGL_apply (F : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    (F ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ)) τ
      = F (γ • τ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (-k) := by
  have := ModularForm.SL_slash_apply (f := F) (k := k) γ τ
  rw [ModularForm.SL_slash] at this
  convert this using 2
  rfl
  rfl

theorem J_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  rw [← denom_mapGL]
  exact denom_ne_zero _ τ

theorem slash_eq_smul_of_hasNebentypus {ε : DirichletCharacter ℂ N} {f : CuspForm Γ₁(N) k}
    (hf : CuspForm.HasNebentypus ε f) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    (⇑f : ℍ → ℂ) ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = ε ((γ 1 1 : ℤ) : ZMod N) • (⇑f : ℍ → ℂ) := by
  funext τ
  rw [slash_mapGL_apply, hf γ hγ τ, Pi.smul_apply, smul_eq_mul]
  have hJ := zpow_ne_zero k (J_ne_zero γ τ)
  rw [zpow_neg]
  field_simp

theorem hasNebentypus_of_slash_eq_smul {ε : DirichletCharacter ℂ N} {F : CuspForm Γ₁(N) k}
    (hF : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N →
      (⇑F : ℍ → ℂ) ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = ε ((γ 1 1 : ℤ) : ZMod N) • (⇑F : ℍ → ℂ)) :
    CuspForm.HasNebentypus ε F := by
  intro γ hγ τ
  have hpt := congrFun (hF γ hγ) τ
  rw [slash_mapGL_apply, Pi.smul_apply, smul_eq_mul] at hpt
  have hJ := J_ne_zero γ τ
  have hzk : (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (-k) ≠ 0 := zpow_ne_zero _ hJ
  have key : F (γ • τ) = ε ((γ 1 1 : ℤ) : ZMod N) * F τ *
      ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (-k))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hzk]
    exact hpt
  rw [key, ← zpow_neg, neg_neg]
  ring

theorem hasNebentypus_heckeUForm [NeZero N] {ℓ : ℕ} (hℓN : ℓ ∣ N) {ε : DirichletCharacter ℂ N}
    {f : CuspForm Γ₁(N) k} (hf : CuspForm.HasNebentypus ε f) :
    CuspForm.HasNebentypus ε (heckeUForm hℓN f) := by
  refine hasNebentypus_of_slash_eq_smul fun γ hγ => ?_
  rw [coe_heckeUForm]
  refine heckeU_slash_eq_smul hℓN k (⇑f) γ hγ _ fun g' hc' hd' => ?_
  have hg'0 : g' ∈ Gamma0 N := Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc')
  rw [slash_eq_smul_of_hasNebentypus hf g' hg'0, hd']

end HeckeUGamma1

end

open scoped MatrixGroups in
theorem solution
    {N : ℕ} [NeZero N] (k : ℤ) {ℓ : ℕ} (hℓ : ℓ ∣ N) (f : CuspForm (CongruenceSubgroup.Gamma1 N) k) :
    ∃ U : CuspForm (CongruenceSubgroup.Gamma1 N) k,
      (⇑U : UpperHalfPlane → ℂ) = ModularForm.heckeU k ℓ ⇑f ∧
      (∀ n : ℕ, ModularFormClass.qCoeff U n = ModularFormClass.qCoeff f (ℓ * n)) ∧
      ∀ ε : DirichletCharacter ℂ N, CuspForm.HasNebentypus ε f → CuspForm.HasNebentypus ε U :=
  ⟨HeckeUGamma1.heckeUForm hℓ f, HeckeUGamma1.coe_heckeUForm hℓ f, HeckeUGamma1.qCoeff_heckeUForm hℓ f,
    fun _ hf => HeckeUGamma1.hasNebentypus_heckeUForm hℓ hf⟩

end S_CuspForm_exists_gamma1_coe_eq_heckeU_of_dvd
end P2MW
export P2MW.S_CuspForm_exists_gamma1_coe_eq_heckeU_of_dvd (solution)
