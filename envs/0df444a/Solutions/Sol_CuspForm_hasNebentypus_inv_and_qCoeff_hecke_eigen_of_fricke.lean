-- Prove2me | solution 1 for CuspForm.hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/6de3c74c-a849-58f3-82ea-34e971dd175b

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_ModularForm_periodic_heckeU_comp_ofComplex
import Theorems.Thm_UpperHalfPlane_qCoeff_heckeU
import Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke

set_option autoImplicit false
set_option maxHeartbeats 3200000

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter Function
open scoped ModularForm MatrixGroups

noncomputable section

namespace FrickeHecke

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Fricke

variable (M : ℕ) [NeZero M]

def frickeGL : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

@[scoped simp] theorem val_frickeGL :
    ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

theorem det_frickeGL : ((frickeGL M).det : ℝ) = M := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_frickeGL, Matrix.det_fin_two_of]; ring

theorem det_frickeGL_pos : 0 < ((frickeGL M).det : ℝ) := by
  rw [det_frickeGL]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)

variable {M}

theorem coe_frickeGL_smul (τ : ℍ) : (↑(frickeGL M • τ) : ℂ) = -1 / ((M : ℂ) * (τ : ℂ)) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_frickeGL_pos M)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom]

theorem frickeGL_smul_mul (τ : ℍ) : ((frickeGL M • τ : ℍ) : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 := by
  rw [coe_frickeGL_smul]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  field_simp

def frickeConj (γ : SL(2, ℤ)) (hγ : (M : ℤ) ∣ γ 1 0) : SL(2, ℤ) :=
  ⟨!![γ 1 1, -(γ 1 0 / M); -(M * γ 0 1), γ 0 0], by
    rw [Matrix.det_fin_two_of]
    have h1 := Matrix.det_fin_two γ.1
    rw [γ.2] at h1
    obtain ⟨c', hc'⟩ := hγ
    have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
    rw [hc', Int.mul_ediv_cancel_left _ hM]
    rw [hc'] at h1
    linear_combination (-1 : ℤ) * h1⟩

theorem coe_frickeConj (γ : SL(2, ℤ)) (c' : ℤ) (hc' : γ 1 0 = M * c') :
    ((frickeConj γ ⟨c', hc'⟩ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![γ 1 1, -c'; -(M * γ 0 1), γ 0 0] := by
  have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hq : γ 1 0 / M = c' := by rw [hc', Int.mul_ediv_cancel_left _ hM]
  simp [frickeConj, hq]

theorem frickeConj_apply_11 (γ : SL(2, ℤ)) (hγ : (M : ℤ) ∣ γ 1 0) : (frickeConj γ hγ) 1 1 = γ 0 0 := by
  obtain ⟨c', hc'⟩ := hγ; simp [coe_frickeConj γ c' hc']

theorem frickeConj_apply_10 (γ : SL(2, ℤ)) (hγ : (M : ℤ) ∣ γ 1 0) :
    (frickeConj γ hγ) 1 0 = -(M * γ 0 1) := by
  obtain ⟨c', hc'⟩ := hγ; simp [coe_frickeConj γ c' hc']

theorem frickeConj_mem_Gamma0 (γ : SL(2, ℤ)) (hγ : (M : ℤ) ∣ γ 1 0) : frickeConj γ hγ ∈ Gamma0 M := by
  rw [Gamma0_mem, frickeConj_apply_10]
  push_cast
  simp

theorem frickeGL_mul_coe (γ : SL(2, ℤ)) (hγ : (M : ℤ) ∣ γ 1 0) :
    frickeGL M * (γ : GL (Fin 2) ℝ) = ((frickeConj γ hγ : SL(2, ℤ)) : GL (Fin 2) ℝ) * frickeGL M := by
  obtain ⟨c', hc'⟩ := hγ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      coe_frickeConj γ c' hc', hc'] <;> ring

end Fricke

section Toolkit

variable {M : ℕ} {k : ℤ} {p : ℕ}

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  simp [Gamma1_mem, ModularGroup.T]

theorem T_pow_mem_Gamma1 (N n : ℕ) : ModularGroup.T ^ n ∈ Gamma1 N :=
  pow_mem (T_mem_Gamma1 N) n

@[scoped simp] theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

theorem heckeDiagMatrix_mul_T (hp : p ≠ 0) :
    heckeDiagMatrix p * (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T)
      = Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ p) * heckeDiagMatrix p := by
  have hTp : ((ModularGroup.T ^ p : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (p : ℤ); 0, 1] := by
    rw [show ModularGroup.T ^ p = ModularGroup.T ^ (p : ℤ) from (zpow_natCast _ p).symm]
    exact ModularGroup.coe_T_zpow (p : ℤ)
  ext i j
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, mapGL_apply, mapGL_apply, mapGL_apply, mapGL_apply, hTp, ModularGroup.coe_T,
    val_heckeDiagMatrix hp]
  fin_cases i <;> fin_cases j <;> simp

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

theorem slash_heckeDiagMatrix_slash_T (hp : p ≠ 0) {F : ℍ → ℂ}
    (h : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ p)) = F) :
    (F ∣[k] heckeDiagMatrix p) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T)
      = F ∣[k] heckeDiagMatrix p := by
  rw [← SlashAction.slash_mul, heckeDiagMatrix_mul_T hp, SlashAction.slash_mul, h]

theorem isBoundedAtImInfty_slash_heckeMatrix (hp : p ≠ 0) (j : ℕ) {F : ℍ → ℂ}
    (hF : IsBoundedAtImInfty F) : IsBoundedAtImInfty (F ∣[k] heckeMatrix p j) :=
  hF.slash k (by simp [val_heckeMatrix hp])

theorem isBoundedAtImInfty_slash_heckeDiagMatrix (hp : p ≠ 0) {F : ℍ → ℂ}
    (hF : IsBoundedAtImInfty F) : IsBoundedAtImInfty (F ∣[k] heckeDiagMatrix p) :=
  hF.slash k (by simp [val_heckeDiagMatrix hp])

theorem isBoundedAtImInfty_heckeU (hp : p ≠ 0) {F : ℍ → ℂ} (hF : IsBoundedAtImInfty F) :
    IsBoundedAtImInfty (heckeU k p F) := by
  rw [heckeU_def]
  induction (Finset.range p) using Finset.induction_on with
  | empty => (simp; exact (Filter.zero_zeroAtFilter atImInfty).boundedAtFilter)
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (isBoundedAtImInfty_slash_heckeMatrix hp j hF).add ih

theorem mdifferentiable_heckeU {F : ℍ → ℂ}
    (hF : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (heckeU k p F) := by
  rw [heckeU_def]
  induction (Finset.range p) using Finset.induction_on with
  | empty => (simp; exact mdifferentiable_const)
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (hF.slash k _).add ih

theorem periodic_add_smul {F G : ℍ → ℂ} (hF : Periodic (F ∘ ofComplex) 1)
    (hG : Periodic (G ∘ ofComplex) 1) (c : ℂ) : Periodic ((F + c • G) ∘ ofComplex) 1 := by
  intro w
  have h1 := hF w
  have h2 := hG w
  simp only [comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  rw [h1, h2]

theorem periodic_smul {G : ℍ → ℂ} (hG : Periodic (G ∘ ofComplex) 1) (c : ℂ) :
    Periodic ((c • G) ∘ ofComplex) 1 := by
  intro w
  have h2 := hG w
  simp only [comp_apply, Pi.smul_apply, smul_eq_mul] at h2 ⊢
  rw [h2]

end Toolkit

section Nebentypus

variable {M : ℕ} [NeZero M] {k : ℤ}

theorem fricke_apply {g h : CuspForm (Γ₁ℝ M) k}
    (hh : ∀ τ τ' : ℍ, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 → g τ' = (τ : ℂ) ^ k * h τ) (τ : ℍ) :
    h τ = (τ : ℂ) ^ (-k) * g (frickeGL M • τ) := by
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  rw [hh τ (frickeGL M • τ) (frickeGL_smul_mul τ), ← mul_assoc, ← zpow_add₀ hτ, neg_add_cancel,
    zpow_zero, one_mul]

omit [NeZero M] in
theorem det_mod (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    ((γ 0 0 : ℤ) : ZMod M) * ((γ 1 1 : ℤ) : ZMod M) = 1 := by
  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := by simpa using Gamma0_mem.mp hγ
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have := congrArg (Int.cast : ℤ → ZMod M) hdet
  push_cast at this
  rw [hc] at this
  linear_combination this

omit [NeZero M] in

theorem dirichlet_apply_00 (ε : DirichletCharacter ℂ M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    ε ((γ 0 0 : ℤ) : ZMod M) = ε⁻¹ ((γ 1 1 : ℤ) : ZMod M) := by
  have hu := det_mod γ hγ
  rw [MulChar.inv_apply_eq_inv']
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, hu, map_one]

theorem hasNebentypus_inv (ε : DirichletCharacter ℂ M) {g h : CuspForm (Γ₁ℝ M) k}
    (hg : CuspForm.HasNebentypus ε g)
    (hh : ∀ τ τ' : ℍ, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 → g τ' = (τ : ℂ) ^ k * h τ) :
    CuspForm.HasNebentypus ε⁻¹ h := by
  intro γ hγ τ
  have hc : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (Gamma0_mem.mp hγ)
  obtain ⟨c', hc'⟩ := hc
  set γW := frickeConj γ ⟨c', hc'⟩ with hγW

  have hpt : frickeGL M • ((γ : GL (Fin 2) ℝ) • τ) = (γW : GL (Fin 2) ℝ) • (frickeGL M • τ) := by
    rw [← mul_smul, ← mul_smul, frickeGL_mul_coe γ ⟨c', hc'⟩]
  have h1 : h (γ • τ) = ((γ • τ : ℍ) : ℂ) ^ (-k) * g (γW • (frickeGL M • τ)) := by
    rw [fricke_apply hh (γ • τ), ModularGroup.sl_moeb, hpt, ModularGroup.sl_moeb]
  have h2 := hg γW (frickeConj_mem_Gamma0 γ ⟨c', hc'⟩) (frickeGL M • τ)
  have h3 : h τ = (τ : ℂ) ^ (-k) * g (frickeGL M • τ) := fricke_apply hh τ

  have e11 : ((γW 1 1 : ℤ) : ℂ) = ((γ 0 0 : ℤ) : ℂ) := by rw [hγW, frickeConj_apply_11]
  have e10 : ((γW 1 0 : ℤ) : ℂ) = -((M : ℂ) * ((γ 0 1 : ℤ) : ℂ)) := by
    rw [hγW, frickeConj_apply_10]; push_cast; ring
  have e11' : ((γW 1 1 : ℤ) : ZMod M) = ((γ 0 0 : ℤ) : ZMod M) := by rw [hγW, frickeConj_apply_11]
  rw [h1, h2, e11', dirichlet_apply_00 ε γ hγ, e11, e10, coe_frickeGL_smul]

  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hden : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ
    simpa [denom] using this
  have hnum : ((γ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 0 1 : ℤ) : ℂ) ≠ 0 := by
    intro h0
    have hne := UpperHalfPlane.ne_zero (γ • τ)
    rw [ModularGroup.sl_moeb, UpperHalfPlane.coe_smul_of_det_pos (by simp)] at hne
    apply hne
    simp only [UpperHalfPlane.num, UpperHalfPlane.denom, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
      Matrix.map_apply, Complex.ofReal_intCast]
    rw [h0, zero_div]
  have hcoe : ((γ • τ : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) /
      (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp
  rw [hcoe, h3]

  have hlin : -((M : ℂ) * ((γ 0 1 : ℤ) : ℂ)) * (-1 / ((M : ℂ) * (τ : ℂ))) + ((γ 0 0 : ℤ) : ℂ) =
      (((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) / (τ : ℂ) := by
    field_simp
    ring
  have hτk : (τ : ℂ) ^ k * (τ : ℂ) ^ (-k) = 1 := by
    rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero k hτ)]
  rw [hlin, div_zpow, div_zpow, zpow_neg, zpow_neg]
  field_simp
  linear_combination
    (-((↑τ * ((γ 1 0 : ℤ) : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k * ε⁻¹ ((γ 1 1 : ℤ) : ZMod M) *
      g (frickeGL M • τ))) * hτk

end Nebentypus

section Phi

variable {M : ℕ} {k : ℤ} {p : ℕ}

def phi (k : ℤ) (p : ℕ) (c : ℂ) (F : ℍ → ℂ) : ℍ → ℂ :=
  heckeU k p F + c • (F ∣[k] heckeDiagMatrix p)

theorem phi_apply (hp : p ≠ 0) (c : ℂ) (F : ℍ → ℂ) (τ : ℍ) :
    phi k p c F τ = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, F (heckeMatrix p j • τ)
      + c * ((p : ℂ) ^ (k - 1) * F (heckeDiagMatrix p • τ)) := by
  rw [phi, Pi.add_apply, Pi.smul_apply, smul_eq_mul, heckeU_apply k hp,
    slash_heckeDiagMatrix_apply k hp]

variable (F : CuspForm (Γ₁ℝ M) k)

theorem cusp_slash_T_pow (n : ℕ) :
    (⇑F : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ n)) = ⇑F :=
  SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ (T_pow_mem_Gamma1 M n))

theorem cusp_periodic : Periodic (⇑F ∘ ofComplex) 1 :=
  periodic_of_slash_T (k := k) (by simpa using cusp_slash_T_pow F 1)

theorem cusp_bdd : IsBoundedAtImInfty (⇑F : ℍ → ℂ) := by
  have h1 : (1 : ℝ) ∈ (Γ₁ℝ M).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _
  haveI : Fact (IsCusp OnePoint.infty (Γ₁ℝ M)) := ⟨(Γ₁ℝ M).isCusp_of_mem_strictPeriods one_pos h1⟩
  exact ModularFormClass.bdd_at_infty F

theorem phi_props (hp : p ≠ 0) (c : ℂ) :
    Periodic (phi k p c ⇑F ∘ ofComplex) 1 ∧
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (phi k p c ⇑F) ∧
    IsBoundedAtImInfty (phi k p c ⇑F) ∧
    ∀ n : ℕ, qCoeff (phi k p c ⇑F) n =
      qCoeff (⇑F) (p * n) + c * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff (⇑F) (n / p) else 0) := by
  have hFper := cusp_periodic F
  have hFhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) := F.holo'
  have hFbdd := cusp_bdd F
  set U : ℍ → ℂ := heckeU k p (⇑F) with hU
  set D : ℍ → ℂ := (⇑F : ℍ → ℂ) ∣[k] heckeDiagMatrix p with hD
  have hUper : Periodic (U ∘ ofComplex) 1 := ModularForm.periodic_heckeU_comp_ofComplex hFper k p
  have hDT : D ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = D :=
    slash_heckeDiagMatrix_slash_T hp (cusp_slash_T_pow F p)
  have hDper : Periodic (D ∘ ofComplex) 1 := periodic_of_slash_T hDT
  have hUhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) U :=
    mdifferentiable_heckeU hFhol
  have hDhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) D :=
    hFhol.slash k _
  have hUbdd : IsBoundedAtImInfty U := isBoundedAtImInfty_heckeU hp hFbdd
  have hDbdd : IsBoundedAtImInfty D := isBoundedAtImInfty_slash_heckeDiagMatrix hp hFbdd
  have hφ : phi k p c ⇑F = U + c • D := rfl
  refine ⟨hφ ▸ periodic_add_smul hUper hDper c, hφ ▸ hUhol.add (hDhol.const_smul c),
    hφ ▸ hUbdd.add (hDbdd.smul c), fun n => ?_⟩

  have hanU := analyticAt_cuspFunction_zero one_pos hUper hUhol hUbdd
  have hancD : AnalyticAt ℂ (cuspFunction 1 (c • D)) 0 :=
    analyticAt_cuspFunction_zero one_pos (periodic_smul hDper c) (hDhol.const_smul c) (hDbdd.smul c)
  have hanD := analyticAt_cuspFunction_zero one_pos hDper hDhol hDbdd
  set G : ℍ → ℂ := fun τ => F (heckeDiagMatrix p • τ) with hG
  have hDG : D = ((p : ℂ) ^ (k - 1)) • G := by
    funext τ
    rw [hD, slash_heckeDiagMatrix_apply k hp, Pi.smul_apply, smul_eq_mul]
  have hpk : ((p : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp)
  have hGD : G = ((p : ℂ) ^ (k - 1))⁻¹ • D := by
    rw [hDG, smul_smul, inv_mul_cancel₀ hpk, one_smul]
  have hanG : AnalyticAt ℂ (cuspFunction 1 G) 0 := by
    rw [hGD]
    exact analyticAt_cuspFunction_zero one_pos (periodic_smul hDper _) (hDhol.const_smul _)
      (hDbdd.smul _)
  have hqD : qCoeff D n = (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff (⇑F) (n / p) else 0) := by
    rw [qCoeff, hDG, qExpansion_smul hanG, map_smul, smul_eq_mul]
    congr 1
    exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul hFper hFhol hFbdd hp n
  have hqU : qCoeff U n = qCoeff (⇑F) (p * n) := by
    rw [hU, UpperHalfPlane.qCoeff_heckeU hFper hFhol hFbdd k hp n, coeffHeckeU_apply, mul_comm]
  rw [hφ, qCoeff, qExpansion_add hanU hancD, qExpansion_smul hanD, map_add, map_smul, smul_eq_mul]
  have h1 := hqU
  have h2 := hqD
  simp only [qCoeff] at h1 h2 ⊢
  rw [h1, h2, mul_assoc]

theorem phi_eq_smul_of_qCoeff (hp : p ≠ 0) (c lam : ℂ)
    (hrel : ∀ n : ℕ, qCoeff (⇑F) (p * n) + c * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then qCoeff (⇑F) (n / p) else 0) = lam * qCoeff (⇑F) n) :
    phi k p c ⇑F = lam • (⇑F : ℍ → ℂ) := by
  obtain ⟨hper, hhol, hbdd, hq⟩ := phi_props F hp c
  have hFper := cusp_periodic F
  have hFhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) := F.holo'
  have hFbdd := cusp_bdd F
  have hang := analyticAt_cuspFunction_zero one_pos hFper hFhol hFbdd
  refine UpperHalfPlane.eq_of_forall_qCoeff_eq hper hhol hbdd (periodic_smul hFper lam)
    (hFhol.const_smul lam) (hFbdd.smul lam) (fun n => ?_)
  rw [hq n, hrel n, qCoeff, qCoeff, qExpansion_smul hang, map_smul, smul_eq_mul]

theorem qCoeff_of_phi_eq_smul (hp : p ≠ 0) (c μ : ℂ)
    (hfun : ∀ τ : ℍ, phi k p c ⇑F τ = μ * F τ) (n : ℕ) :
    qCoeff (⇑F) (p * n) + c * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then qCoeff (⇑F) (n / p) else 0) = μ * qCoeff (⇑F) n := by
  obtain ⟨-, -, -, hq⟩ := phi_props F hp c
  have hFper := cusp_periodic F
  have hFhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) := F.holo'
  have hFbdd := cusp_bdd F
  have hang := analyticAt_cuspFunction_zero one_pos hFper hFhol hFbdd
  have heq : phi k p c ⇑F = μ • (⇑F : ℍ → ℂ) := by
    funext τ; rw [hfun τ, Pi.smul_apply, smul_eq_mul]
  rw [← hq n, heq, qCoeff, qCoeff, qExpansion_smul hang, map_smul, smul_eq_mul]

end Phi

section Matrices

variable {M : ℕ} [NeZero M] {p : ℕ}

theorem heckeDiagMatrix_mul_frickeGL (hp : p ≠ 0) :
    heckeDiagMatrix p * frickeGL M = frickeGL M * heckeMatrix p 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, val_heckeMatrix hp, val_heckeDiagMatrix hp, mul_comm]

theorem heckeMatrix_zero_mul_frickeGL (hp : p ≠ 0) :
    heckeMatrix p 0 * frickeGL M = frickeGL M * heckeDiagMatrix p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, val_heckeMatrix hp, val_heckeDiagMatrix hp, mul_comm]

end Matrices

section Sig

variable (M p : ℕ)

def sig (j : ℕ) : ℕ := (-((M : ZMod p) * (j : ZMod p))⁻¹).val

variable {M p} [Fact p.Prime]

theorem M_ne_zero_mod (hpM : ¬ p ∣ M) : (M : ZMod p) ≠ 0 := by
  rwa [Ne, ZMod.natCast_eq_zero_iff]

omit [Fact p.Prime] in
theorem mem_S_iff (j : ℕ) : j ∈ (Finset.range p).erase 0 ↔ j < p ∧ j ≠ 0 := by
  rw [Finset.mem_erase, Finset.mem_range, and_comm]

theorem cast_ne_zero_of_mem {j : ℕ} (hj : j ∈ (Finset.range p).erase 0) : (j : ZMod p) ≠ 0 := by
  rw [mem_S_iff] at hj
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => hj.2 (Nat.eq_zero_of_dvd_of_lt h hj.1)

theorem sig_cast (j : ℕ) : ((sig M p j : ℕ) : ZMod p) = -((M : ZMod p) * (j : ZMod p))⁻¹ := by
  rw [sig, ZMod.natCast_zmod_val]

theorem sig_lt (j : ℕ) : sig M p j < p := ZMod.val_lt _

theorem sig_mem (hpM : ¬ p ∣ M) {j : ℕ} (hj : j ∈ (Finset.range p).erase 0) :
    sig M p j ∈ (Finset.range p).erase 0 := by
  rw [mem_S_iff]
  refine ⟨sig_lt j, fun h0 => ?_⟩
  have h1 : ((sig M p j : ℕ) : ZMod p) = 0 := by rw [h0, Nat.cast_zero]
  rw [sig_cast, neg_eq_zero, inv_eq_zero] at h1
  exact mul_ne_zero (M_ne_zero_mod hpM) (cast_ne_zero_of_mem hj) h1

theorem dvd_sig (hpM : ¬ p ∣ M) {j : ℕ} (hj : j ∈ (Finset.range p).erase 0) :
    p ∣ M * j * sig M p j + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [sig_cast, mul_neg, mul_inv_cancel₀ (mul_ne_zero (M_ne_zero_mod hpM) (cast_ne_zero_of_mem hj))]
  ring

theorem sig_sig (hpM : ¬ p ∣ M) {j : ℕ} (hj : j ∈ (Finset.range p).erase 0) :
    sig M p (sig M p j) = j := by
  have hjlt : j < p := ((mem_S_iff j).1 hj).1
  have hMz := M_ne_zero_mod (p := p) hpM
  have hjz := cast_ne_zero_of_mem hj
  have hcast : ((sig M p (sig M p j) : ℕ) : ZMod p) = (j : ZMod p) := by
    rw [sig_cast, sig_cast, mul_neg, mul_inv, ← mul_assoc, mul_inv_cancel₀ hMz, one_mul, inv_neg,
      inv_inv, neg_neg]
  have := congrArg ZMod.val hcast
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (sig_lt (M := M) (p := p) (sig M p j)),
    Nat.mod_eq_of_lt hjlt] at this

end Sig

section Gam

variable {M : ℕ} [NeZero M] {p : ℕ}

def gam (p j j' q : ℕ) (h : M * j * j' + 1 = p * q) : SL(2, ℤ) :=
  ⟨!![(q : ℤ), (j : ℤ); ((M * j' : ℕ) : ℤ), (p : ℤ)], by
    rw [Matrix.det_fin_two_of]
    have hint : ((M * j * j' + 1 : ℕ) : ℤ) = ((p * q : ℕ) : ℤ) := by rw [h]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hint
    simp only [Nat.cast_mul]
    linear_combination (-1 : ℤ) * hint⟩

omit [NeZero M] in
theorem gam_apply_11 (p j j' q : ℕ) (h : M * j * j' + 1 = p * q) : (gam p j j' q h) 1 1 = p := rfl

omit [NeZero M] in
theorem gam_apply_10 (p j j' q : ℕ) (h : M * j * j' + 1 = p * q) :
    (gam p j j' q h) 1 0 = ((M * j' : ℕ) : ℤ) := rfl

omit [NeZero M] in
theorem gam_mem_Gamma0 (p j j' q : ℕ) (h : M * j * j' + 1 = p * q) : gam (M := M) p j j' q h ∈ Gamma0 M := by
  rw [Gamma0_mem, gam_apply_10]
  push_cast
  simp

theorem heckeMatrix_mul_frickeGL (hp : p ≠ 0) (j j' q : ℕ) (h : M * j * j' + 1 = p * q) :
    heckeMatrix p j * frickeGL M =
      ((gam (M := M) p j j' q h : SL(2, ℤ)) : GL (Fin 2) ℝ) * (frickeGL M * heckeMatrix p j') := by
  have hreal : (M : ℝ) * j * j' + 1 = p * q := by exact_mod_cast h
  ext i i'
  fin_cases i <;> fin_cases i' <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, val_heckeMatrix hp, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      gam] <;> nlinarith [hreal]

end Gam

section Pointwise

variable {M : ℕ} [NeZero M] {k : ℤ} {p : ℕ}

theorem div_zpow_neg (x : ℂ) (p : ℂ) (k : ℤ) : (x / p) ^ (-k) = p ^ k * x ^ (-k) := by
  rw [div_zpow, zpow_neg, zpow_neg, div_eq_mul_inv, inv_inv, mul_comm]

theorem main_pointwise (ε : DirichletCharacter ℂ M) {g h : CuspForm (Γ₁ℝ M) k}
    (hg : CuspForm.HasNebentypus ε g)
    (hh : ∀ τ τ' : ℍ, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 → g τ' = (τ : ℂ) ^ k * h τ)
    (hp : p.Prime) (hpM : ¬ p ∣ M) (lam : ℂ)
    (hΦg : ∀ w : ℍ, phi k p (ε (p : ZMod M)) ⇑g w = lam * g w) (τ : ℍ) :
    phi k p (ε⁻¹ (p : ZMod M)) ⇑h τ = ε⁻¹ (p : ZMod M) * lam * h τ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  set W := frickeGL M with hW
  set e := ε (p : ZMod M) with he
  set e' := ε⁻¹ (p : ZMod M) with he'

  have hunit : IsUnit ((p : ℕ) : ZMod M) := (ZMod.isUnit_prime_iff_not_dvd hp).2 hpM
  have hee : e' * e = 1 := by
    have h1 : (ε⁻¹ * ε) (p : ZMod M) = 1 := by
      rw [inv_mul_cancel, MulChar.one_apply hunit]
    rwa [MulChar.coeToFun_mul, Pi.mul_apply] at h1

  have hha : ∀ w : ℍ, h w = (w : ℂ) ^ (-k) * g (W • w) := fricke_apply hh

  set S := (Finset.range p).erase 0 with hS
  have h0mem : (0 : ℕ) ∈ Finset.range p := Finset.mem_range.2 hp.pos
  set L : ℕ → ℂ := fun j => ((heckeMatrix p j • τ : ℍ) : ℂ) ^ (-k) * g (W • heckeMatrix p j • τ)
    with hL
  set Lδ : ℂ := e' * ((p : ℂ) ^ (k - 1) *
    (((heckeDiagMatrix p • τ : ℍ) : ℂ) ^ (-k) * g (W • heckeDiagMatrix p • τ))) with hLδ
  set R : ℕ → ℂ := fun j => g (heckeMatrix p j • W • τ) with hR
  set Rδ : ℂ := g (heckeDiagMatrix p • W • τ) with hRδ

  have T0 : (p : ℂ)⁻¹ * L 0 = e' * (τ : ℂ) ^ (-k) * (e * ((p : ℂ) ^ (k - 1) * Rδ)) := by
    have hpt : W • heckeMatrix p 0 • τ = heckeDiagMatrix p • W • τ := by
      rw [← mul_smul, ← mul_smul, heckeDiagMatrix_mul_frickeGL hp0]
    have hcoe : ((heckeMatrix p 0 • τ : ℍ) : ℂ) = (τ : ℂ) / p := by
      rw [coe_heckeMatrix_smul hp0]; simp
    simp only [hL]
    rw [hpt, hcoe, div_zpow_neg, zpow_sub_one₀ hpC]
    linear_combination (-((τ : ℂ) ^ (-k) * (p : ℂ) ^ k * (p : ℂ)⁻¹ * Rδ)) * hee

  have Tδ : Lδ = e' * (τ : ℂ) ^ (-k) * ((p : ℂ)⁻¹ * R 0) := by
    have hpt : W • heckeDiagMatrix p • τ = heckeMatrix p 0 • W • τ := by
      rw [← mul_smul, ← mul_smul, heckeMatrix_zero_mul_frickeGL hp0]
    have hcoe : ((heckeDiagMatrix p • τ : ℍ) : ℂ) = (p : ℂ) * (τ : ℂ) := coe_heckeDiagMatrix_smul hp0 τ
    have hpk : (p : ℂ) ^ k * (p : ℂ) ^ (-k) = 1 := by
      rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero k hpC)]
    simp only [hLδ]
    rw [hpt, hcoe, mul_zpow, zpow_sub_one₀ hpC]
    linear_combination (e' * (p : ℂ)⁻¹ * (τ : ℂ) ^ (-k) * R 0) * hpk

  have Tj : ∀ j ∈ S, e' * (τ : ℂ) ^ (-k) * ((p : ℂ)⁻¹ * R j) = (p : ℂ)⁻¹ * L (sig M p j) := by
    intro j hj
    set j' := sig M p j with hj'
    obtain ⟨q, hq⟩ : p ∣ M * j * j' + 1 := dvd_sig hpM hj
    set γ : SL(2, ℤ) := gam (M := M) p j j' q hq with hγ
    set z : ℍ := W • heckeMatrix p j' • τ with hz
    have hpt : heckeMatrix p j • W • τ = γ • z := by
      rw [ModularGroup.sl_moeb, hz, ← mul_smul, ← mul_smul, ← mul_smul,
        heckeMatrix_mul_frickeGL hp0 j j' q hq, mul_assoc]
    have hneb := hg γ (gam_mem_Gamma0 p j j' q hq) z
    set x : ℂ := (τ : ℂ) + (j' : ℂ) with hx
    have hx0 : x ≠ 0 := by
      intro h0
      have : x.im = 0 := by rw [h0, Complex.zero_im]
      rw [hx, Complex.add_im, Complex.natCast_im, add_zero, UpperHalfPlane.coe_im] at this
      exact (ne_of_gt τ.im_pos) this
    have hcoem : ((heckeMatrix p j' • τ : ℍ) : ℂ) = x / p := by
      rw [coe_heckeMatrix_smul hp0]
    have hcoez : (z : ℂ) = -1 / ((M : ℂ) * (x / p)) := by
      rw [hz, coe_frickeGL_smul, hcoem]
    have e11 : ((γ 1 1 : ℤ) : ZMod M) = (p : ZMod M) := by rw [hγ, gam_apply_11, Int.cast_natCast]
    have e11' : ((γ 1 1 : ℤ) : ℂ) = (p : ℂ) := by rw [hγ, gam_apply_11, Int.cast_natCast]
    have e10 : ((γ 1 0 : ℤ) : ℂ) = (M : ℂ) * (j' : ℂ) := by
      rw [hγ, gam_apply_10]; push_cast; ring
    have hlin : ((γ 1 0 : ℤ) : ℂ) * (z : ℂ) + ((γ 1 1 : ℤ) : ℂ) = (p : ℂ) * (τ : ℂ) / x := by
      rw [e10, e11', hcoez]
      have hxj : x - (j' : ℂ) = (τ : ℂ) := by rw [hx]; ring
      rw [← hxj]
      field_simp
      ring
    simp only [hR, hL]
    rw [hpt, hneb, e11, hlin, hcoem, ← he]
    rw [show W • heckeMatrix p j' • τ = z from rfl]
    rw [div_zpow, mul_zpow, div_zpow_neg, zpow_neg (τ : ℂ) k, zpow_neg x k]
    have hτk0 : (τ : ℂ) ^ k ≠ 0 := zpow_ne_zero k hτ
    have hxk0 : x ^ k ≠ 0 := zpow_ne_zero k hx0
    have hpk0 : (p : ℂ) ^ k ≠ 0 := zpow_ne_zero k hpC
    field_simp
    linear_combination (g z) * hee

  have hsumL : ∑ j ∈ Finset.range p, L j = L 0 + ∑ j ∈ S, L j :=
    (Finset.add_sum_erase _ _ h0mem).symm
  have hsumR : ∑ j ∈ Finset.range p, R j = R 0 + ∑ j ∈ S, R j :=
    (Finset.add_sum_erase _ _ h0mem).symm
  have hreidx : ∑ j ∈ S, e' * (τ : ℂ) ^ (-k) * ((p : ℂ)⁻¹ * R j) = ∑ j ∈ S, (p : ℂ)⁻¹ * L j := by
    rw [Finset.sum_congr rfl Tj]
    exact Finset.sum_nbij' (sig M p) (sig M p) (fun a ha => sig_mem hpM ha)
      (fun a ha => sig_mem hpM ha) (fun a ha => sig_sig hpM ha) (fun a ha => sig_sig hpM ha)
      (fun a _ => rfl)
  have key : (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, L j + Lδ =
      e' * (τ : ℂ) ^ (-k) * ((p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, R j + e * ((p : ℂ) ^ (k - 1) * Rδ)) := by
    rw [hsumL, hsumR, mul_add, Finset.mul_sum, T0, Tδ, ← hreidx, mul_add ((p : ℂ)⁻¹), Finset.mul_sum,
      mul_add (e' * (τ : ℂ) ^ (-k)), mul_add (e' * (τ : ℂ) ^ (-k)), Finset.mul_sum]
    ring

  calc phi k p e' ⇑h τ
      = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, L j + Lδ := by
        rw [phi_apply hp0]
        simp only [hha, hL, hLδ]
    _ = e' * (τ : ℂ) ^ (-k) * ((p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, R j + e * ((p : ℂ) ^ (k - 1) * Rδ)) := key
    _ = e' * (τ : ℂ) ^ (-k) * phi k p e ⇑g (W • τ) := by rw [phi_apply hp0]
    _ = e' * (τ : ℂ) ^ (-k) * (lam * g (W • τ)) := by rw [hΦg]
    _ = e' * lam * h τ := by rw [hha τ]; ring

end Pointwise

section Main

variable {M : ℕ} [NeZero M] {k : ℤ}

theorem main (ε : DirichletCharacter ℂ M) (g h : CuspForm (Γ₁ℝ M) k)
    (hg : CuspForm.HasNebentypus ε g)
    (hh : ∀ τ τ' : ℍ, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 → g τ' = (τ : ℂ) ^ k * h τ) :
    CuspForm.HasNebentypus ε⁻¹ h ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ lam : ℂ,
        (∀ n : ℕ, qCoeff (⇑g) (p * n) +
            ε (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff (⇑g) (n / p) else 0) =
          lam * qCoeff (⇑g) n) →
        ∀ n : ℕ, qCoeff (⇑h) (p * n) +
            ε⁻¹ (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff (⇑h) (n / p) else 0) =
          ε⁻¹ (p : ZMod M) * lam * qCoeff (⇑h) n := by
  refine ⟨hasNebentypus_inv ε hg hh, fun p hp hpM lam hrel n => ?_⟩
  have hp0 : p ≠ 0 := hp.ne_zero

  have hΦg : phi k p (ε (p : ZMod M)) ⇑g = lam • (⇑g : ℍ → ℂ) :=
    phi_eq_smul_of_qCoeff g hp0 _ lam hrel
  have hΦg' : ∀ w : ℍ, phi k p (ε (p : ZMod M)) ⇑g w = lam * g w := fun w => by
    rw [hΦg, Pi.smul_apply, smul_eq_mul]

  exact qCoeff_of_phi_eq_smul h hp0 (ε⁻¹ (p : ZMod M)) (ε⁻¹ (p : ZMod M) * lam)
    (main_pointwise ε hg hh hp hpM lam hΦg') n

end Main

end FrickeHecke
p2m_reactivate "P2MW.S_CuspForm_hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke.FrickeHecke"

end
p2m_reactivate "P2MW.S_CuspForm_hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke.FrickeHecke"

open scoped MatrixGroups in
theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g h : CuspForm (Gamma1 M) k)
    (hg : CuspForm.HasNebentypus ε g)
    (hh : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 →
      g τ' = (τ : ℂ) ^ k * h τ) :
    CuspForm.HasNebentypus ε⁻¹ h ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ lam : ℂ,
        (∀ n : ℕ, ModularFormClass.qCoeff g (p * n) +
            ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
              (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
          lam * ModularFormClass.qCoeff g n) →
        ∀ n : ℕ, ModularFormClass.qCoeff h (p * n) +
            ε⁻¹ (p : ZMod M) * (p : ℂ) ^ (k - 1) *
              (if p ∣ n then ModularFormClass.qCoeff h (n / p) else 0) =
          ε⁻¹ (p : ZMod M) * lam * ModularFormClass.qCoeff h n :=
  FrickeHecke.main ε g h hg hh

end S_CuspForm_hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke
end P2MW
export P2MW.S_CuspForm_hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke (solution)
