-- Prove2me | solution 1 for CuspForm.qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/d60da8ba-c813-52d7-bb2f-4d1a2bdead50

import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_stableT
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_ModularForm_periodic_heckeU_comp_ofComplex
import Theorems.Thm_UpperHalfPlane_qCoeff_heckeU
import Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH

set_option autoImplicit false

p2m_open "CongruenceSubgroup ModularForm~mdifferentiable_heckeU ModularFormClass UpperHalfPlane Filter Function"
open scoped MatrixGroups ModularForm

noncomputable section

namespace QExpHeckeTH

local notation "ΓHℝ" M ", " H => ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ} {p : ℕ}

theorem Gamma1_le_GammaH' (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  obtain ⟨h00, h11, h10⟩ := hA
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := by rw [CongruenceSubgroup.Gamma0_mem]; exact h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]
  exact one_mem H

theorem one_mem_strictPeriods_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ (ΓHℝ M, H).strictPeriods := by
  have h1 : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    show (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma1 M)).strictPeriods
    rw [CongruenceSubgroup.strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples _
  rw [Subgroup.mem_strictPeriods_iff] at h1 ⊢
  have hle : ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ (ΓHℝ M, H) :=
    Subgroup.map_mono (Gamma1_le_GammaH' M H)
  exact hle h1

theorem T_pow_mem_Gamma1 (N n : ℕ) : ModularGroup.T ^ n ∈ Gamma1 N := by
  refine pow_mem ?_ n
  simp [Gamma1_mem, ModularGroup.T]

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

theorem periodic_smul {G : ℍ → ℂ} (hG : Periodic (G ∘ ofComplex) 1) (c : ℂ) :
    Periodic ((c • G) ∘ ofComplex) 1 := by
  intro w
  have h2 := hG w
  simp only [comp_apply, Pi.smul_apply, smul_eq_mul] at h2 ⊢
  rw [h2]

variable (F : CuspForm (ΓHℝ M, H) k)

theorem cusp_slash_T_pow (n : ℕ) :
    (⇑F : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ n)) = ⇑F :=
  SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ (Gamma1_le_GammaH' M H (T_pow_mem_Gamma1 M n)))

theorem cusp_periodic : Periodic (⇑F ∘ ofComplex) 1 :=
  periodic_of_slash_T (k := k) (by simpa using cusp_slash_T_pow F 1)

theorem cusp_holo : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) := F.holo'

theorem cusp_bdd : IsBoundedAtImInfty (⇑F : ℍ → ℂ) := by
  have h1 : (1 : ℝ) ∈ (ΓHℝ M, H).strictPeriods := one_mem_strictPeriods_GammaH M H
  haveI : Fact (IsCusp OnePoint.infty (ΓHℝ M, H)) := ⟨(ΓHℝ M, H).isCusp_of_mem_strictPeriods one_pos h1⟩
  exact ModularFormClass.bdd_at_infty F

theorem qCoeff_heckeU_add_slash (hp : p ≠ 0) (G : CuspForm (ΓHℝ M, H) k) (n : ℕ) :
    qCoeff (heckeU k p ⇑F + (⇑G) ∣[k] heckeDiagMatrix p) n =
      qCoeff (⇑F) (p * n) + (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff (⇑G) (n / p) else 0) := by
  have hFper := cusp_periodic F
  have hFhol := cusp_holo F
  have hFbdd := cusp_bdd F
  have hGper := cusp_periodic G
  have hGhol := cusp_holo G
  have hGbdd := cusp_bdd G
  set U : ℍ → ℂ := heckeU k p (⇑F) with hU
  set D : ℍ → ℂ := (⇑G : ℍ → ℂ) ∣[k] heckeDiagMatrix p with hD
  have hUper : Periodic (U ∘ ofComplex) 1 := ModularForm.periodic_heckeU_comp_ofComplex hFper k p
  have hDT : D ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = D :=
    slash_heckeDiagMatrix_slash_T hp (cusp_slash_T_pow G p)
  have hDper : Periodic (D ∘ ofComplex) 1 := periodic_of_slash_T hDT
  have hUhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) U :=
    mdifferentiable_heckeU hFhol
  have hDhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) D :=
    hGhol.slash k _
  have hUbdd : IsBoundedAtImInfty U := isBoundedAtImInfty_heckeU hp hFbdd
  have hDbdd : IsBoundedAtImInfty D := isBoundedAtImInfty_slash_heckeDiagMatrix hp hGbdd
  have hanU := analyticAt_cuspFunction_zero one_pos hUper hUhol hUbdd
  have hanD := analyticAt_cuspFunction_zero one_pos hDper hDhol hDbdd
  set G' : ℍ → ℂ := fun τ => G (heckeDiagMatrix p • τ) with hG'
  have hDG : D = ((p : ℂ) ^ (k - 1)) • G' := by
    funext τ
    rw [hD, slash_heckeDiagMatrix_apply k hp, Pi.smul_apply, smul_eq_mul]
  have hpk : ((p : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp)
  have hGD : G' = ((p : ℂ) ^ (k - 1))⁻¹ • D := by
    rw [hDG, smul_smul, inv_mul_cancel₀ hpk, one_smul]
  have hanG : AnalyticAt ℂ (cuspFunction 1 G') 0 := by
    rw [hGD]
    exact analyticAt_cuspFunction_zero one_pos (periodic_smul hDper _) (hDhol.const_smul _)
      (hDbdd.smul _)
  have hqD : qCoeff D n = (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff (⇑G) (n / p) else 0) := by
    rw [qCoeff, hDG, qExpansion_smul hanG, map_smul, smul_eq_mul]
    congr 1
    exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul hGper hGhol hGbdd hp n
  have hqU : qCoeff U n = qCoeff (⇑F) (p * n) := by
    rw [hU, UpperHalfPlane.qCoeff_heckeU hFper hFhol hFbdd k hp n, coeffHeckeU_apply, mul_comm]
  rw [qCoeff, qExpansion_add hanU hanD, map_add]
  have h1 := hqU
  have h2 := hqD
  simp only [qCoeff] at h1 h2 ⊢
  rw [h1, h2]

end QExpHeckeTH
p2m_reactivate "P2MW.S_CuspForm_qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH.QExpHeckeTH"

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (f : CuspForm (CohCarrier.GammaH M H) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(CuspForm.heckeTLinH k hℓ hℓM f)) n =
      ModularFormClass.qCoeff (⇑f) (n * ℓ) +
        (ℓ : ℂ) ^ (k - 1) *
          (if ℓ ∣ n then
            ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH k (CuspForm.unitOfPrimeNotDvd hℓ hℓM) f)) (n / ℓ)
           else 0) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  rw [CuspForm.coe_heckeTLinH_apply k hℓ hℓM (CuspForm.stableT M H k hℓ hℓM) f, SlashAction.slash_mul,
    ← CuspForm.coe_diamondLinH_apply k (CuspForm.stableD M H k) (CuspForm.unitOfPrimeNotDvd hℓ hℓM) f,
    mul_comm n ℓ]
  exact QExpHeckeTH.qCoeff_heckeU_add_slash f hℓ.ne_zero
    (CuspForm.diamondLinH k (CuspForm.unitOfPrimeNotDvd hℓ hℓM) f) n

end
p2m_reactivate "P2MW.S_CuspForm_qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH.QExpHeckeTH"

end S_CuspForm_qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH
end P2MW
export P2MW.S_CuspForm_qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH (solution)
