-- Prove2me | solution 1 for CuspForm.exists_degeneracy_gamma1_hasNebentypus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d2381269-22a6-57cc-b488-8a1c3ebbb620

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_degeneracy_gamma1_hasNebentypus

set_option autoImplicit false

open CongruenceSubgroup ModularForm UpperHalfPlane Filter Function
open scoped ModularForm UpperHalfPlane MatrixGroups

noncomputable section

namespace DegeneracyGamma1

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₀(" M ")" => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Cocycle

variable {M N d : ℕ}

open FreyPackage.ModMCarrier in

theorem exists_cocycle (hd : d ≠ 0) (hdMN : d * M ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma0 M ∧
      diagMatInt d * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * diagMatInt d ∧
      γ' 0 0 = γ 0 0 ∧ γ' 1 1 = γ 1 1 ∧ γ' 1 0 * d = γ 1 0 := by
  obtain ⟨γ', hγ', hconj⟩ := exists_cocycle_rescale hdMN hγ
  have key : ∀ i j, (diagMatInt d * (γ : Matrix (Fin 2) (Fin 2) ℤ)) i j
      = ((γ' : Matrix (Fin 2) (Fin 2) ℤ) * diagMatInt d) i j := fun i j => by rw [hconj]
  have e00 := key 0 0
  have e11 := key 1 1
  have e10 := key 1 0
  simp [diagMatInt, Matrix.mul_apply, Fin.sum_univ_two] at e00 e11 e10
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd
  refine ⟨γ', hγ', hconj, ?_, ?_, ?_⟩
  ·
    have h' : (d : ℤ) * γ' 0 0 = (d : ℤ) * γ 0 0 := by linear_combination e00.symm
    exact mul_left_cancel₀ hd' h'
  · linear_combination e11.symm
  · linear_combination e10.symm

theorem mem_Gamma1_of_cocycle (hMN : M ∣ N) {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N)
    (hγ' : γ' ∈ Gamma0 M) (h00 : γ' 0 0 = γ 0 0) (h11 : γ' 1 1 = γ 1 1) : γ' ∈ Gamma1 M := by
  rw [Gamma1_mem] at hγ ⊢
  obtain ⟨ha, he, -⟩ := hγ
  refine ⟨?_, ?_, by simpa using Gamma0_mem.mp hγ'⟩
  · rw [h00]
    have := (ZMod.castHom hMN (ZMod M)).congr_arg ha
    simpa only [map_intCast, map_one] using this
  · rw [h11]
    have := (ZMod.castHom hMN (ZMod M)).congr_arg he
    simpa only [map_intCast, map_one] using this

open FreyPackage.ModMCarrier in

theorem heckeDiagMatrix_mul_eq (hd : d ≠ 0) {γ γ' : SL(2, ℤ)}
    (hconj : diagMatInt d * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * diagMatInt d) :
    heckeDiagMatrix d * Matrix.SpecialLinearGroup.mapGL ℝ γ
      = Matrix.SpecialLinearGroup.mapGL ℝ γ' * heckeDiagMatrix d := by
  have mapGL_coe_eq : ∀ s : SL(2, ℤ),
      ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := fun _ => rfl
  have map_int_mul_eq : ∀ A B : Matrix (Fin 2) (Fin 2) ℤ,
      (A * B).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * B.map (algebraMap ℤ ℝ) := by
    intro A B
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← diagMatInt_map_eq hd, mapGL_coe_eq, mapGL_coe_eq,
    ← map_int_mul_eq, ← map_int_mul_eq, hconj]

end Cocycle

section Form

variable {M N d : ℕ} [NeZero N] {k : ℤ}

theorem neZero_of_dvd (hMN : M ∣ N) : NeZero M :=
  ⟨fun h0 => (NeZero.ne N) (Nat.eq_zero_of_zero_dvd (h0 ▸ hMN))⟩

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  simp [Gamma1_mem, ModularGroup.T]

theorem periodic_of_slash_T {F : ℍ → ℂ}
    (h : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = F) :
    Periodic (F ∘ ofComplex) 1 := by
  have hT : ∀ τ : ℍ, F ((1 : ℝ) +ᵥ τ) = F τ := by
    intro τ
    have := congrFun h τ
    change (F ∣[k] ModularGroup.T) τ = F τ at this
    rw [SL_slash_apply] at this
    rw [← modular_T_smul]
    rw [← this]
    simp [denom, ModularGroup.T]
  intro w
  by_cases hw : 0 < w.im
  · have : 0 < (w + 1).im := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    convert hT ⟨w, hw⟩ using 2
    ext
    simp [add_comm]
  · have hw : w.im ≤ 0 := le_of_not_gt hw
    have : (w + 1).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

def stretchSlash (hd : d ≠ 0) (hdMN : d * M ∣ N) (g : CuspForm Γ₁(M) k) : CuspForm Γ₁(N) k :=
  haveI : NeZero M := neZero_of_dvd (dvd_of_mul_left_dvd hdMN)
  { toFun := (⇑g : ℍ → ℂ) ∣[k] heckeDiagMatrix d
    slash_action_eq' := by
      intro A hA
      obtain ⟨γ, hγ, rfl⟩ := hA
      obtain ⟨γ', hγ'0, hconj, h00, h11, -⟩ := exists_cocycle hd hdMN (Gamma1_in_Gamma0 N hγ)
      have hγ'1 : γ' ∈ Gamma1 M :=
        mem_Gamma1_of_cocycle (dvd_of_mul_left_dvd hdMN) hγ hγ'0 h00 h11
      rw [← SlashAction.slash_mul, heckeDiagMatrix_mul_eq hd hconj, SlashAction.slash_mul]
      congr 1
      exact SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ'1)
    holo' := g.holo'.slash k _
    zero_at_cusps' := by
      intro c hc
      have hc0 : IsCusp c Γ₀(N) := by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢; exact hc
      refine FreyPackage.ModMCarrier.rescaleSlash_isZeroAt (R := M) (M := N) hd k ?_ hc0
      intro c' hc'
      have hc'1 : IsCusp c' Γ₁(M) := by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc' ⊢; exact hc'
      exact CuspFormClass.zero_at_cusps g hc'1 }

theorem stretchSlash_apply (hd : d ≠ 0) (hdMN : d * M ∣ N) (g : CuspForm Γ₁(M) k) (τ : ℍ) :
    stretchSlash hd hdMN g τ = (d : ℂ) ^ (k - 1) * g (heckeDiagMatrix d • τ) :=
  slash_heckeDiagMatrix_apply k hd _ τ

def stretch (hd : d ≠ 0) (hdMN : d * M ∣ N) (g : CuspForm Γ₁(M) k) : CuspForm Γ₁(N) k :=
  ((d : ℂ) ^ (k - 1))⁻¹ • stretchSlash hd hdMN g

theorem stretch_apply (hd : d ≠ 0) (hdMN : d * M ∣ N) (g : CuspForm Γ₁(M) k) (τ : ℍ) :
    stretch hd hdMN g τ = g (heckeDiagMatrix d • τ) := by
  have hpk : ((d : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hd)
  rw [stretch, CuspForm.IsGLPos.smul_apply, stretchSlash_apply, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hpk, one_mul]

theorem qCoeff_stretch (hd : d ≠ 0) (hdMN : d * M ∣ N) (g : CuspForm Γ₁(M) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(stretch hd hdMN g)) n
      = if d ∣ n then ModularFormClass.qCoeff (⇑g) (n / d) else 0 := by
  haveI : NeZero M := neZero_of_dvd (dvd_of_mul_left_dvd hdMN)
  have hcoe : (⇑(stretch hd hdMN g) : ℍ → ℂ) = fun τ => g (heckeDiagMatrix d • τ) :=
    funext (stretch_apply hd hdMN g)
  rw [hcoe]
  have hgT : (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = ⇑g :=
    SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ (T_mem_Gamma1 M))
  exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul (periodic_of_slash_T hgT) g.holo'
    (ModularFormClass.bdd_at_infty g) hd n

theorem hasNebentypus_stretch (hd : d ≠ 0) (hdMN : d * M ∣ N) (g : CuspForm Γ₁(M) k)
    (ε : DirichletCharacter ℂ M) (hg : CuspForm.HasNebentypus ε g) :
    CuspForm.HasNebentypus (DirichletCharacter.changeLevel (dvd_of_mul_left_dvd hdMN) ε)
      (stretch hd hdMN g) := by
  haveI : NeZero M := neZero_of_dvd (dvd_of_mul_left_dvd hdMN)
  have hMN : M ∣ N := dvd_of_mul_left_dvd hdMN
  intro γ hγ τ
  obtain ⟨γ', hγ'0, hconj, h00, h11, h10⟩ := exists_cocycle hd hdMN hγ
  have hGL := heckeDiagMatrix_mul_eq hd hconj
  rw [stretch_apply, stretch_apply]

  have hsm : heckeDiagMatrix d • (γ • τ) = γ' • (heckeDiagMatrix d • τ) := by
    change heckeDiagMatrix d • ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) • τ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ) • (heckeDiagMatrix d • τ)
    rw [← mul_smul, hGL, mul_smul]
  rw [hsm, hg γ' hγ'0 (heckeDiagMatrix d • τ)]

  have hunit : IsUnit ((γ 1 1 : ℤ) : ZMod N) := by
    have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := by simpa using Gamma0_mem.mp hγ
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have h := γ.det_coe; rwa [Matrix.det_fin_two] at h
    have := congrArg (Int.cast : ℤ → ZMod N) hdet
    push_cast at this
    rw [hc, mul_zero, sub_zero] at this
    exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact this)
  have hchar : (DirichletCharacter.changeLevel hMN ε) ((γ 1 1 : ℤ) : ZMod N)
      = ε ((γ' 1 1 : ℤ) : ZMod M) := by
    rw [h11, ← hunit.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd ε hMN,
      hunit.unit_spec, ZMod.cast_intCast hMN]
  rw [hchar]

  have hcoe : ((heckeDiagMatrix d • τ : ℍ) : ℂ) = (d : ℂ) * (τ : ℂ) := coe_heckeDiagMatrix_smul hd τ
  have hfac : ((γ' 1 0 : ℤ) : ℂ) * ((heckeDiagMatrix d • τ : ℍ) : ℂ) + ((γ' 1 1 : ℤ) : ℂ)
      = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
    rw [hcoe, h11, ← h10]
    push_cast
    ring
  rw [hfac]

end Form

end DegeneracyGamma1

end

open scoped MatrixGroups in
theorem solution
    {k : ℤ} {M N d : ℕ} [NeZero N] (hd : M * d ∣ N) (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) :
    ∃ G : CuspForm (CongruenceSubgroup.Gamma1 N) k,
      (∀ τ : UpperHalfPlane, G τ = g (ModularForm.heckeDiagMatrix d • τ)) ∧
      (∀ n : ℕ, ModularFormClass.qCoeff G n =
        if d ∣ n then ModularFormClass.qCoeff g (n / d) else 0) ∧
      ∀ ε : DirichletCharacter ℂ M, CuspForm.HasNebentypus ε g →
        CuspForm.HasNebentypus (DirichletCharacter.changeLevel (dvd_of_mul_right_dvd hd) ε) G := by
  have hdMN : d * M ∣ N := by rwa [mul_comm] at hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact (NeZero.ne N) (Nat.eq_zero_of_zero_dvd (by simpa using hd))
  exact ⟨DegeneracyGamma1.stretch hd0 hdMN g, DegeneracyGamma1.stretch_apply hd0 hdMN g,
    DegeneracyGamma1.qCoeff_stretch hd0 hdMN g,
    fun ε hε => DegeneracyGamma1.hasNebentypus_stretch hd0 hdMN g ε hε⟩

end S_CuspForm_exists_degeneracy_gamma1_hasNebentypus
end P2MW
export P2MW.S_CuspForm_exists_degeneracy_gamma1_hasNebentypus (solution)
