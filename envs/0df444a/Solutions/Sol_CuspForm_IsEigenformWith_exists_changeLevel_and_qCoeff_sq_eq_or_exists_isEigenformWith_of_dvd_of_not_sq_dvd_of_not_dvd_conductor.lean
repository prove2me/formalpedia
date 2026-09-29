-- Prove2me | solution 1 for CuspForm.IsEigenformWith.exists_changeLevel_and_qCoeff_sq_eq_or_exists_isEigenformWith_of_dvd_of_not_sq_dvd_of_not_dvd_conductor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/8091ab68-fcf4-5f45-86ff-73680aa398e3

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd
import Theorems.Thm_CuspForm_IsEigenformWith_exists_isEigenformWith_changeLevel_qCoeff_eq_of_dvd
import Theorems.Thm_CuspForm_exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen
import Theorems.Thm_ModularForm_heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0
import Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic
import Theorems.Thm_ModularForm_mdifferentiable_heckeU
import Theorems.Thm_CuspFormClass_isZeroAt_heckeU
import Theorems.Thm_CuspFormClass_isZeroAt_heckeT
import Theorems.Thm_ModularForm_periodic_heckeU_comp_ofComplex
import Theorems.Thm_UpperHalfPlane_qCoeff_heckeU
import Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsEigenformWith_exists_changeLevel_and_qCoeff_sq_eq_or_exists_isEigenformWith_of_dvd_of_not_sq_dvd_of_not_dvd_conductor
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FreyPackage.ModMCarrier.coe_rescaleLin_apply FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter Function
open scoped ModularForm MatrixGroups

noncomputable section

namespace ALLiP

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₀ℝ" M => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section API

theorem mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

theorem map_int_mul (A P : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * P).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

theorem det_entries (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := γ.det_coe
  rwa [Matrix.det_fin_two] at h

theorem SL_slash_apply' (k : ℤ) (F : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    (F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) τ
      = F (γ • τ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (-k) := by
  have h := ModularForm.SL_slash_apply (f := F) (k := k) γ τ
  rw [ModularGroup.denom_apply] at h
  exact h

theorem denom_SL_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  rw [← ModularGroup.denom_apply]
  exact denom_ne_zero _ τ

theorem isUnit_entry {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    IsUnit ((γ 1 1 : ℤ) : ZMod N) := by
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := by simpa using Gamma0_mem.mp hγ
  have := congrArg (Int.cast : ℤ → ZMod N) (det_entries γ)
  push_cast at this
  rw [hc, mul_zero, sub_zero] at this
  exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact this)

end API

section Neb

variable {M : ℕ} {k : ℤ}

theorem slash_eq_smul_of_hasNebentypus {ε : DirichletCharacter ℂ M} {g : CuspForm (Γ₁ℝ M) k}
    (hg : CuspForm.HasNebentypus ε g) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
      = ε ((γ 1 1 : ℤ) : ZMod M) • (⇑g : ℍ → ℂ) := by
  funext τ
  rw [SL_slash_apply', hg γ hγ τ, Pi.smul_apply, smul_eq_mul]
  have hne := denom_SL_ne_zero γ τ
  have hk : (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k ≠ 0 := zpow_ne_zero k hne
  rw [zpow_neg]
  field_simp

theorem hasNebentypus_of_slash_eq_smul {ε : DirichletCharacter ℂ M} {g : CuspForm (Γ₁ℝ M) k}
    (hg : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
      (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
        = ε ((γ 1 1 : ℤ) : ZMod M) • (⇑g : ℍ → ℂ)) :
    CuspForm.HasNebentypus ε g := by
  intro γ hγ τ
  have h := congrFun (hg γ hγ) τ
  rw [SL_slash_apply', Pi.smul_apply, smul_eq_mul] at h
  have hne := denom_SL_ne_zero γ τ
  have h2 : g (γ • τ) = ε ((γ 1 1 : ℤ) : ZMod M) * g τ *
      (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k := by
    have := congrArg (fun z => z * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k) h
    rwa [mul_assoc, ← zpow_add₀ hne, neg_add_cancel, zpow_zero, mul_one] at this
  rw [h2]
  ring

theorem changeLevel_apply_prime {R : ℕ} [NeZero M] (hR : R ∣ M) (ε' : DirichletCharacter ℂ R)
    {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) :
    DirichletCharacter.changeLevel hR ε' (p : ZMod M) = ε' (p : ZMod R) := by
  have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpM
  have hu : ((ZMod.unitOfCoprime p hcop : (ZMod M)ˣ) : ZMod M) = (p : ZMod M) :=
    ZMod.coe_unitOfCoprime p hcop
  rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd ε' hR, hu, ZMod.cast_natCast hR]

end Neb

section PhiDef

variable {k : ℤ}

theorem smul_slash_pos (k : ℤ) {A : GL (Fin 2) ℝ} (hA : 0 < (A.det : ℝ)) (c : ℂ) (F : ℍ → ℂ) :
    (c • F) ∣[k] A = c • F ∣[k] A := by
  rw [ModularForm.smul_slash]
  congr 1
  rw [UpperHalfPlane.σ, if_pos hA]
  rfl

def phi (k : ℤ) (p : ℕ) (c : ℂ) (F : ℍ → ℂ) : ℍ → ℂ :=
  heckeU k p F + c • (F ∣[k] heckeDiagMatrix p)

theorem phi_add (k : ℤ) (p : ℕ) (c : ℂ) (F G : ℍ → ℂ) :
    phi k p c (F + G) = phi k p c F + phi k p c G := by
  simp only [phi, heckeU_add, SlashAction.add_slash, smul_add]
  abel

theorem phi_smul (k : ℤ) (p : ℕ) (c a : ℂ) (F : ℍ → ℂ) :
    phi k p c (a • F) = a • phi k p c F := by
  rw [phi, phi, heckeU_smul, smul_slash_pos k (det_heckeDiagMatrix_pos p), smul_comm, smul_add]

end PhiDef

section Phi

variable {L : ℕ} {k : ℤ} {p : ℕ}

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

theorem isBoundedAtImInfty_heckeU (hp : p ≠ 0) {F : ℍ → ℂ} (hF : IsBoundedAtImInfty F) :
    IsBoundedAtImInfty (heckeU k p F) := by
  rw [heckeU_def]
  induction (Finset.range p) using Finset.induction_on with
  | empty => first | simpa using (Filter.zero_zeroAtFilter atImInfty).boundedAtFilter | exact (Filter.zero_zeroAtFilter atImInfty).boundedAtFilter
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (hF.slash k (by simp [val_heckeMatrix hp])).add ih

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

variable (F : CuspForm (Γ₁ℝ L) k)

theorem cusp_slash_T_pow (n : ℕ) :
    (⇑F : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ n)) = ⇑F :=
  SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ (T_pow_mem_Gamma1 L n))

theorem cusp_periodic : Periodic (⇑F ∘ ofComplex) 1 :=
  periodic_of_slash_T (k := k) (by simpa using cusp_slash_T_pow F 1)

theorem cusp_bdd : IsBoundedAtImInfty (⇑F : ℍ → ℂ) := by
  have h1 : (1 : ℝ) ∈ (Γ₁ℝ L).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _
  haveI : Fact (IsCusp OnePoint.infty (Γ₁ℝ L)) := ⟨(Γ₁ℝ L).isCusp_of_mem_strictPeriods one_pos h1⟩
  exact ModularFormClass.bdd_at_infty F

theorem qCoeff_smul (c : ℂ) (n : ℕ) : qCoeff (c • (⇑F : ℍ → ℂ)) n = c * qCoeff (⇑F) n := by
  have hang := analyticAt_cuspFunction_zero one_pos (cusp_periodic F) F.holo' (cusp_bdd F)
  rw [qCoeff, qCoeff, qExpansion_smul hang, map_smul, smul_eq_mul]

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
    ModularForm.mdifferentiable_heckeU hFhol k p
  have hDhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) D :=
    hFhol.slash k _
  have hUbdd : IsBoundedAtImInfty U := isBoundedAtImInfty_heckeU hp hFbdd
  have hDbdd : IsBoundedAtImInfty D := hFbdd.slash k (by simp [val_heckeDiagMatrix hp])
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
  have hFhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) := F.holo'
  refine UpperHalfPlane.eq_of_forall_qCoeff_eq hper hhol hbdd (periodic_smul (cusp_periodic F) lam)
    (hFhol.const_smul lam) ((cusp_bdd F).smul lam) (fun n => ?_)
  rw [hq n, hrel n, qCoeff_smul]

theorem qCoeff_of_phi_eq_smul (hp : p ≠ 0) (c μ : ℂ) (hfun : phi k p c ⇑F = μ • (⇑F : ℍ → ℂ))
    (n : ℕ) :
    qCoeff (⇑F) (p * n) + c * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then qCoeff (⇑F) (n / p) else 0) = μ * qCoeff (⇑F) n := by
  obtain ⟨-, -, -, hq⟩ := phi_props F hp c
  rw [← hq n, hfun, qCoeff_smul]

theorem heckeU_eq_smul_of_qCoeff {ℓ : ℕ} (hℓ : ℓ ≠ 0) (a : ℂ)
    (ha : ∀ n : ℕ, qCoeff (⇑F) (ℓ * n) = a * qCoeff (⇑F) n) :
    heckeU k ℓ ⇑F = a • (⇑F : ℍ → ℂ) := by
  have hFper := cusp_periodic F
  have hFhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) := F.holo'
  have hFbdd := cusp_bdd F
  refine UpperHalfPlane.eq_of_forall_qCoeff_eq (ModularForm.periodic_heckeU_comp_ofComplex hFper k ℓ)
    (ModularForm.mdifferentiable_heckeU hFhol k ℓ) (isBoundedAtImInfty_heckeU hℓ hFbdd)
    (periodic_smul hFper a) (hFhol.const_smul a) (hFbdd.smul a) (fun n => ?_)
  rw [UpperHalfPlane.qCoeff_heckeU hFper hFhol hFbdd k hℓ n, coeffHeckeU_apply, mul_comm n ℓ, ha n,
    qCoeff_smul]

end Phi

section Packet

variable {N : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (N : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ N).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

theorem qCoeff_add' (F G : CuspForm (Γ₁ℝ N) k) (n : ℕ) :
    qCoeff (⇑(F + G)) n = qCoeff (⇑F) n + qCoeff (⇑G) n := by
  have hF := ModularFormClass.analyticAt_cuspFunction_zero F one_pos (one_mem_strictPeriods N)
  have hG := ModularFormClass.analyticAt_cuspFunction_zero G one_pos (one_mem_strictPeriods N)
  rw [qCoeff, qCoeff, qCoeff, CuspForm.coe_add, qExpansion_add hF hG, map_add]

theorem qCoeff_smul' (c : ℂ) (F : CuspForm (Γ₁ℝ N) k) (n : ℕ) :
    qCoeff (⇑(c • F)) n = c * qCoeff (⇑F) n := by
  rw [CuspForm.IsGLPos.coe_smul, qCoeff_smul]

theorem qCoeff_zero' (n : ℕ) : qCoeff (⇑(0 : CuspForm (Γ₁ℝ N) k)) n = 0 := by
  rw [CuspForm.coe_zero, qCoeff, UpperHalfPlane.qExpansion_zero, map_zero]

def Rel (ℓ : ℕ) (e lam : ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, a (ℓ * n) + e * (if ℓ ∣ n then a (n / ℓ) else 0) = lam * a n

theorem Rel.add {ℓ : ℕ} {e lam : ℂ} {a b : ℕ → ℂ} (ha : Rel ℓ e lam a) (hb : Rel ℓ e lam b) :
    Rel ℓ e lam (fun n => a n + b n) := by
  intro n
  have h1 := ha n
  have h2 := hb n
  split_ifs at h1 h2 ⊢ <;> linear_combination h1 + h2

theorem Rel.smul {ℓ : ℕ} {e lam : ℂ} {a : ℕ → ℂ} (ha : Rel ℓ e lam a) (c : ℂ) :
    Rel ℓ e lam (fun n => c * a n) := by
  intro n
  have h1 := ha n
  split_ifs at h1 ⊢ <;> linear_combination c * h1

theorem Rel.zero (ℓ : ℕ) (e lam : ℂ) : Rel ℓ e lam (fun _ => 0) := by
  intro n; split_ifs <;> simp

theorem Rel.hecke {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ) {e lam : ℂ} (ep : ℂ)
    {a b : ℕ → ℂ} (ha : Rel ℓ e lam a)
    (hb : ∀ n : ℕ, b n = a (p * n) + ep * (if p ∣ n then a (n / p) else 0)) :
    Rel ℓ e lam b := by
  intro n
  have hℓp : ¬ ℓ ∣ p := fun h' => hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h').symm
  have hpℓ' : ¬ p ∣ ℓ := fun h' => hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp h')
  have hℓpm : ∀ m : ℕ, (ℓ ∣ p * m) ↔ ℓ ∣ m := fun m =>
    ⟨fun h' => ((Nat.Prime.dvd_mul hℓ).mp h').resolve_left hℓp, fun h' => h'.mul_left p⟩
  have hpℓm : ∀ m : ℕ, (p ∣ ℓ * m) ↔ p ∣ m := fun m =>
    ⟨fun h' => ((Nat.Prime.dvd_mul hp).mp h').resolve_left hpℓ', fun h' => h'.mul_left ℓ⟩
  rw [hb (ℓ * n), hb n]
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    have h1 : ℓ * (p * m) / p = ℓ * m := by rw [mul_left_comm, Nat.mul_div_cancel_left _ hp.pos]
    rw [if_pos ((hpℓm _).mpr (dvd_mul_right p m)), if_pos (dvd_mul_right p m), h1,
      Nat.mul_div_cancel_left m hp.pos]
    by_cases hℓm : ℓ ∣ p * m
    · obtain ⟨r, rfl⟩ := (hℓpm m).mp hℓm
      have h2 : p * (ℓ * r) / ℓ = p * r := by rw [mul_left_comm, Nat.mul_div_cancel_left _ hℓ.pos]
      rw [if_pos hℓm, h2, hb (p * r), if_pos (dvd_mul_right p r), Nat.mul_div_cancel_left r hp.pos]
      have e1 := ha (p * (p * (ℓ * r)))
      have e2 := ha (ℓ * r)
      have h3 : p * (p * (ℓ * r)) / ℓ = p * (p * r) := by
        rw [show p * (p * (ℓ * r)) = ℓ * (p * (p * r)) by ring, Nat.mul_div_cancel_left _ hℓ.pos]
      rw [if_pos ((hℓpm _).mpr hℓm), h3] at e1
      rw [if_pos (dvd_mul_right ℓ r), Nat.mul_div_cancel_left r hℓ.pos] at e2
      rw [show p * (ℓ * (p * (ℓ * r))) = ℓ * (p * (p * (ℓ * r))) by ring]
      linear_combination e1 + ep * e2
    · have hℓm' : ¬ ℓ ∣ m := fun h' => hℓm (h'.mul_left p)
      rw [if_neg hℓm]
      have e1 := ha (p * (p * m))
      have e2 := ha m
      have hℓppm : ¬ ℓ ∣ p * (p * m) := fun h' => hℓm ((hℓpm _).mp h')
      rw [if_neg hℓppm] at e1
      rw [if_neg hℓm'] at e2
      rw [show p * (ℓ * (p * m)) = ℓ * (p * (p * m)) by ring]
      linear_combination e1 + ep * e2
  · rw [if_neg (fun h' => hpn ((hpℓm _).mp h')), if_neg hpn]
    by_cases hℓn : ℓ ∣ n
    · obtain ⟨r, rfl⟩ := hℓn
      have hpr : ¬ p ∣ r := fun h' => hpn (h'.mul_left ℓ)
      rw [if_pos (dvd_mul_right ℓ r), Nat.mul_div_cancel_left r hℓ.pos, hb r, if_neg hpr]
      have e1 := ha (p * (ℓ * r))
      have h2 : p * (ℓ * r) / ℓ = p * r := by rw [mul_left_comm, Nat.mul_div_cancel_left _ hℓ.pos]
      rw [if_pos ((hℓpm _).mpr (dvd_mul_right ℓ r)), h2] at e1
      rw [show p * (ℓ * (ℓ * r)) = ℓ * (p * (ℓ * r)) by ring]
      linear_combination e1
    · rw [if_neg hℓn]
      have e1 := ha (p * n)
      rw [if_neg (fun h' => hℓn ((hℓpm _).mp h'))] at e1
      rw [show p * (ℓ * n) = ℓ * (p * n) by ring]
      linear_combination e1

theorem hasNebentypus_add {ε : DirichletCharacter ℂ N} {F G : CuspForm (Γ₁ℝ N) k}
    (hF : CuspForm.HasNebentypus ε F) (hG : CuspForm.HasNebentypus ε G) :
    CuspForm.HasNebentypus ε (F + G) := by
  intro γ hγ τ
  rw [CuspForm.add_apply, CuspForm.add_apply, hF γ hγ τ, hG γ hγ τ]
  ring

theorem hasNebentypus_smul {ε : DirichletCharacter ℂ N} {F : CuspForm (Γ₁ℝ N) k}
    (hF : CuspForm.HasNebentypus ε F) (c : ℂ) :
    CuspForm.HasNebentypus ε (c • F) := by
  intro γ hγ τ
  rw [CuspForm.IsGLPos.smul_apply, CuspForm.IsGLPos.smul_apply, hF γ hγ τ, smul_eq_mul, smul_eq_mul]
  ring

theorem hasNebentypus_zero (ε : DirichletCharacter ℂ N) :
    CuspForm.HasNebentypus ε (0 : CuspForm (Γ₁ℝ N) k) := by
  intro γ hγ τ
  simp

variable (N k)

def packet (ε' : DirichletCharacter ℂ N) (M : ℕ) (lam : ℕ → ℂ) :
    Submodule ℂ (CuspForm (Γ₁ℝ N) k) where
  carrier := {F | CuspForm.HasNebentypus ε' F ∧
    ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M →
      Rel ℓ (ε' (ℓ : ZMod N) * (ℓ : ℂ) ^ (k - 1)) (lam ℓ) (fun n => qCoeff (⇑F) n)}
  add_mem' := by
    rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    refine ⟨hasNebentypus_add hF hG, fun ℓ hℓ hℓM => ?_⟩
    have := (hF' ℓ hℓ hℓM).add (hG' ℓ hℓ hℓM)
    intro n
    simpa only [qCoeff_add'] using this n
  zero_mem' := by
    refine ⟨hasNebentypus_zero ε', fun ℓ hℓ hℓM => ?_⟩
    intro n
    simpa only [qCoeff_zero'] using Rel.zero ℓ _ (lam ℓ) n
  smul_mem' := by
    rintro c F ⟨hF, hF'⟩
    refine ⟨hasNebentypus_smul hF c, fun ℓ hℓ hℓM => ?_⟩
    have := (hF' ℓ hℓ hℓM).smul c
    intro n
    simpa only [qCoeff_smul'] using this n

variable {N k}

theorem mem_packet_iff {ε' : DirichletCharacter ℂ N} {M : ℕ} {lam : ℕ → ℂ}
    {F : CuspForm (Γ₁ℝ N) k} :
    F ∈ packet N k ε' M lam ↔ CuspForm.HasNebentypus ε' F ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M →
        Rel ℓ (ε' (ℓ : ZMod N) * (ℓ : ℂ) ^ (k - 1)) (lam ℓ) (fun n => qCoeff (⇑F) n) :=
  Iff.rfl

variable [NeZero N]

omit [NeZero N] in

theorem isZeroAt_smul {c₀ : OnePoint ℝ} {G : ℍ → ℂ} (h : OnePoint.IsZeroAt c₀ G k) (a : ℂ) :
    OnePoint.IsZeroAt c₀ (a • G) k := fun g hg => by
  rw [ModularForm.smul_slash]
  exact (h g hg).smul _

def tpForm (ε' : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (F : CuspForm (Γ₁ℝ N) k) (hF : CuspForm.HasNebentypus ε' F) : CuspForm (Γ₁ℝ N) k where
  toFun := phi k p (ε' (p : ZMod N)) ⇑F
  slash_action_eq' := by
    intro A hA
    obtain ⟨γ, hγ, rfl⟩ := hA
    have hγ0 : γ ∈ Gamma0 N := by
      rw [Gamma0_mem]; exact (Gamma1_mem _ _ |>.mp hγ).2.2
    have hd : ((γ 1 1 : ℤ) : ZMod N) = 1 := (Gamma1_mem _ _ |>.mp hγ).2.1
    have h := ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0 k hp hpN ε'
      (fun _ hγ' => slash_eq_smul_of_hasNebentypus hF hγ') γ hγ0
    rw [hd, map_one, one_smul] at h
    exact h
  holo' := (ModularForm.mdifferentiable_heckeU F.holo' k p).add
    ((F.holo'.slash k _).const_smul _)
  zero_at_cusps' := by
    intro c hc
    have h1 := CuspFormClass.isZeroAt_heckeU F p hc
    have h2 := CuspFormClass.isZeroAt_heckeT F p hc
    have h3 := CuspFormClass.isZeroAt_heckeU (-F) p hc
    have hD : OnePoint.IsZeroAt c ((⇑F : ℍ → ℂ) ∣[k] heckeDiagMatrix p) k := by
      have e : heckeT k p ⇑F + heckeU k p ⇑(-F) = (⇑F : ℍ → ℂ) ∣[k] heckeDiagMatrix p := by
        rw [CuspForm.coe_neg, heckeU_neg, heckeT_eq_heckeU_add]; abel
      rw [← e]
      exact h2.add h3
    exact h1.add (isZeroAt_smul hD _)

@[scoped simp] theorem coe_tpForm (ε' : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (F : CuspForm (Γ₁ℝ N) k) (hF : CuspForm.HasNebentypus ε' F) :
    ⇑(tpForm ε' hp hpN F hF) = phi k p (ε' (p : ZMod N)) ⇑F := rfl

theorem hasNebentypus_tpForm (ε' : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (F : CuspForm (Γ₁ℝ N) k) (hF : CuspForm.HasNebentypus ε' F) :
    CuspForm.HasNebentypus ε' (tpForm ε' hp hpN F hF) :=
  hasNebentypus_of_slash_eq_smul fun γ hγ =>
    ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0 k hp hpN ε'
      (fun _ hγ' => slash_eq_smul_of_hasNebentypus hF hγ') γ hγ

theorem tpForm_mem_packet (ε' : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    {M : ℕ} (hpM : p ∣ M) (lam : ℕ → ℂ) {F : CuspForm (Γ₁ℝ N) k}
    (hF : F ∈ packet N k ε' M lam) :
    tpForm ε' hp hpN F hF.1 ∈ packet N k ε' M lam := by
  refine ⟨hasNebentypus_tpForm ε' hp hpN F hF.1, fun ℓ hℓ hℓM => ?_⟩
  have hpℓ : p ≠ ℓ := fun h' => hℓM (h' ▸ hpM)
  obtain ⟨-, -, -, hq⟩ := phi_props F hp.ne_zero (ε' (p : ZMod N))
  exact (hF.2 ℓ hℓ hℓM).hecke hp hℓ hpℓ (ε' (p : ZMod N) * (p : ℂ) ^ (k - 1))
    (fun n => by rw [coe_tpForm, hq n, mul_assoc])

def tpLin (ε' : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    {M : ℕ} (hpM : p ∣ M) (lam : ℕ → ℂ) :
    packet N k ε' M lam →ₗ[ℂ] packet N k ε' M lam where
  toFun F := ⟨tpForm ε' hp hpN F.1 F.2.1, tpForm_mem_packet ε' hp hpN hpM lam F.2⟩
  map_add' F G := by
    apply Subtype.ext
    apply DFunLike.ext'
    show phi k p (ε' (p : ZMod N)) ⇑((F : CuspForm (Γ₁ℝ N) k) + (G : CuspForm (Γ₁ℝ N) k))
      = ⇑(tpForm ε' hp hpN F.1 F.2.1 + tpForm ε' hp hpN G.1 G.2.1)
    rw [CuspForm.coe_add, CuspForm.coe_add, coe_tpForm, coe_tpForm, phi_add]
  map_smul' c F := by
    apply Subtype.ext
    apply DFunLike.ext'
    show phi k p (ε' (p : ZMod N)) ⇑(c • (F : CuspForm (Γ₁ℝ N) k))
      = ⇑(c • tpForm ε' hp hpN F.1 F.2.1)
    rw [CuspForm.IsGLPos.coe_smul, CuspForm.IsGLPos.coe_smul, coe_tpForm, phi_smul]

theorem coe_tpLin_apply (ε' : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    {M : ℕ} (hpM : p ∣ M) (lam : ℕ → ℂ) (F : packet N k ε' M lam) :
    ((tpLin ε' hp hpN hpM lam F : packet N k ε' M lam) : CuspForm (Γ₁ℝ N) k)
      = tpForm ε' hp hpN F.1 F.2.1 := rfl

theorem exists_eigen (ε' : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    {M : ℕ} (hpM : p ∣ M) (lam : ℕ → ℂ) {G : CuspForm (Γ₁ℝ N) k} (hG : G ∈ packet N k ε' M lam)
    (hG0 : G ≠ 0) :
    ∃ (F : CuspForm (Γ₁ℝ N) k) (μ : ℂ), F ≠ 0 ∧ F ∈ packet N k ε' M lam ∧
      Rel p (ε' (p : ZMod N) * (p : ℂ) ^ (k - 1)) μ (fun n => qCoeff (⇑F) n) := by
  set V := packet N k ε' M lam with hV
  haveI : FiniteDimensional ℂ (CuspForm (Γ₁ℝ N) k) :=
    CuspForm.finiteDimensional_of_isArithmetic (Γ₁ℝ N) k
  haveI : FiniteDimensional ℂ V := FiniteDimensional.finiteDimensional_submodule V
  haveI : Nontrivial V := ⟨⟨⟨G, hG⟩, 0, fun h => hG0 (congrArg Subtype.val h)⟩⟩
  set T : Module.End ℂ V := tpLin ε' hp hpN hpM lam with hT
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv1 : T v = μ • v := Module.End.mem_eigenspace_iff.mp hv.1
  have hv0 : v ≠ 0 := hv.2
  refine ⟨v.1, μ, fun h0 => hv0 (Subtype.ext h0), v.2, ?_⟩

  have hfun : phi k p (ε' (p : ZMod N)) ⇑(v.1 : CuspForm (Γ₁ℝ N) k)
      = μ • (⇑(v.1 : CuspForm (Γ₁ℝ N) k) : ℍ → ℂ) := by
    have h1 := congrArg (fun w : V => ((w : CuspForm (Γ₁ℝ N) k) : ℍ → ℂ)) hv1
    rw [hT, coe_tpLin_apply, coe_tpForm] at h1
    rw [h1, Submodule.coe_smul, CuspForm.IsGLPos.coe_smul]
  intro n
  exact qCoeff_of_phi_eq_smul v.1 hp.ne_zero _ _ hfun n

end Packet

section Characters

variable {N : ℕ} [NeZero N]

theorem dirichletCharacter_eq_of_forall_prime {χ ψ : DirichletCharacter ℂ N}
    (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → χ (ℓ : ZMod N) = ψ (ℓ : ZMod N)) : χ = ψ := by
  refine MulChar.ext fun u => ?_
  obtain ⟨ℓ, hℓN, hℓ, hℓu⟩ := Nat.forall_exists_prime_gt_and_eq_mod (Units.isUnit u) N
  have hndvd : ¬ ℓ ∣ N := fun hd => (Nat.le_of_dvd (NeZero.pos N) hd).not_gt hℓN
  rw [← hℓu]
  exact h ℓ hℓ hndvd

end Characters

section Main

variable {M : ℕ}

theorem ne_zero_of_qCoeff_one {L : ℕ} {k : ℤ} {g : CuspForm (Γ₁ℝ L) k} (h1 : qCoeff (⇑g) 1 = 1) :
    g ≠ 0 := by
  intro h0
  rw [h0] at h1
  simp [qCoeff, UpperHalfPlane.qExpansion_zero] at h1

theorem exists_changeLevel [NeZero M] {ε : DirichletCharacter ℂ M} {p : ℕ} (hp : p.Prime) (hpM : p ∣ M)
    (hpε : ¬ p ∣ ε.conductor) :
    ∃ ε' : DirichletCharacter ℂ (M / p), ε = DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hpM) ε' := by
  have hcop : Nat.Coprime ε.conductor p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpε).symm
  have hdvdM : ε.conductor ∣ (M / p) * p := by
    rw [Nat.div_mul_cancel hpM]; exact ε.conductor_dvd_level
  have hdvd : ε.conductor ∣ M / p := hcop.dvd_of_dvd_mul_right hdvdM
  have hft : ε.FactorsThrough (M / p) :=
    (DirichletCharacter.mem_conductorSet_iff_conductor_dvd ε (Nat.div_dvd_of_dvd hpM)).mpr hdvd
  obtain ⟨hd, ε', hε'⟩ := hft
  exact ⟨ε', hε'⟩

theorem exists_isEigenformWith_of_packet {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) (hM : M = p * N) (ε' : DirichletCharacter ℂ N) (lam : ℕ → ℂ)
    {G : CuspForm (Γ₁ℝ N) k} (hG0 : G ≠ 0) (hGneb : CuspForm.HasNebentypus ε' G)
    (hGrel : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ∀ n : ℕ,
      qCoeff (⇑G) (ℓ * n) + ε' (ℓ : ZMod N) * (ℓ : ℂ) ^ (k - 1) *
        (if ℓ ∣ n then qCoeff (⇑G) (n / ℓ) else 0) = lam ℓ * qCoeff (⇑G) n) :
    ∃ h' : CuspForm (Γ₁ℝ N) k, CuspForm.IsEigenformWith ε' h' ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → qCoeff (⇑h') ℓ = lam ℓ := by
  have hpM : p ∣ M := hM ▸ dvd_mul_right p N
  have hGmem : G ∈ packet N k ε' M lam := ⟨hGneb, fun ℓ hℓ hℓM n => hGrel ℓ hℓ hℓM n⟩
  obtain ⟨F, μ, hF0, hFmem, hFp⟩ := exists_eigen ε' hp hpN hpM lam hGmem hG0

  let lam' : ℕ → ℂ := fun ℓ => if ℓ = p then μ else lam ℓ
  have hrel : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ∀ n : ℕ,
      qCoeff (⇑F) (ℓ * n) + ε' (ℓ : ZMod N) * (ℓ : ℂ) ^ (k - 1) *
        (if ℓ ∣ n then qCoeff (⇑F) (n / ℓ) else 0) = lam' ℓ * qCoeff (⇑F) n := by
    intro ℓ hℓ hℓN n
    by_cases hℓp : ℓ = p
    · subst hℓp
      simp only [lam', if_true]
      exact hFp n
    · have hℓM : ¬ ℓ ∣ M := by
        rw [hM]; intro h'
        rcases (Nat.Prime.dvd_mul hℓ).mp h' with h'' | h''
        · exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h'')
        · exact hℓN h''
      simp only [lam', hℓp, if_false]
      exact hFmem.2 ℓ hℓ hℓM n

  obtain ⟨M₀, _, ε₀, g₀, hM₀N, hprim, hval⟩ :=
    CuspForm.exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen N k ε' F hF0 hFmem.1 lam' hrel

  obtain ⟨h', hh', hq'⟩ := hprim.isEigenformWith.exists_isEigenformWith_changeLevel_qCoeff_eq_of_dvd
    (N := N) hM₀N

  have hchar : DirichletCharacter.changeLevel hM₀N ε₀ = ε' := by
    refine dirichletCharacter_eq_of_forall_prime fun ℓ hℓ hℓN => ?_
    rw [changeLevel_apply_prime hM₀N ε₀ hℓ hℓN]
    exact (hval ℓ hℓ hℓN).2
  rw [hchar] at hh'
  refine ⟨h', hh', fun ℓ hℓ hℓM => ?_⟩
  have hℓN : ¬ ℓ ∣ N := fun h' => hℓM (hM ▸ h'.mul_left p)
  have hℓp : ℓ ≠ p := fun h' => hℓM (h' ▸ hpM)
  rw [hq' ℓ hℓ (fun h => absurd h hℓN), (hval ℓ hℓ hℓN).1]
  simp only [lam', hℓp, if_false]

theorem main [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (Γ₁ℝ M) 2}
    (hh : CuspForm.IsEigenformWith ε h)
    (p : ℕ) (hp : p.Prime) (hpM : p ∣ M) (hp2 : ¬ p ^ 2 ∣ M) (hpε : ¬ p ∣ ε.conductor) :
    ∃ ε' : DirichletCharacter ℂ (M / p),
      ε = DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hpM) ε' ∧
      (qCoeff (⇑h) p ^ 2 = ε' (p : ZMod (M / p)) ∨
       ∃ h' : CuspForm (Γ₁ℝ (M / p)) 2,
         CuspForm.IsEigenformWith ε' h' ∧
         ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → qCoeff (⇑h') ℓ = qCoeff (⇑h) ℓ) := by
  obtain ⟨ε', hε'⟩ := exists_changeLevel hp hpM hpε
  refine ⟨ε', hε', ?_⟩
  subst hε'
  haveI : NeZero (M / p) := ⟨fun h0 => by
    have := Nat.div_mul_cancel hpM
    rw [h0, zero_mul] at this
    exact NeZero.ne M this.symm⟩
  have hpN : ¬ p ∣ M / p := fun h' => hp2 (by rw [sq]; exact Nat.mul_dvd_of_dvd_div hpM h')
  have hMeq : M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm

  have hf0 : h ≠ 0 := ne_zero_of_qCoeff_one hh.qCoeff_one
  have hU : ∀ n : ℕ, qCoeff (⇑h) (p * n) = qCoeff (⇑h) p * qCoeff (⇑h) n :=
    fun n => hh.hecke_of_dvd hp hpM n
  have hT : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ∀ n : ℕ,
      qCoeff (⇑h) (ℓ * n) + ε' (ℓ : ZMod (M / p)) * (ℓ : ℂ) ^ ((2 : ℤ) - 1) *
        (if ℓ ∣ n then qCoeff (⇑h) (n / ℓ) else 0) = qCoeff (⇑h) ℓ * qCoeff (⇑h) n := by
    intro ℓ hℓ hℓM n
    rw [← changeLevel_apply_prime (Nat.div_dvd_of_dvd hpM) ε' hℓ hℓM]
    exact hh.hecke_of_not_dvd hℓ hℓM n
  rcases CuspForm.qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd
      M 2 hp hpM hp2 ε' h hf0 hh.hasNebentypus hU hT with hnew | ⟨G, hG0, hGneb, hGrel⟩
  · left
    simpa using hnew
  · right
    obtain ⟨h', hh', hq⟩ := exists_isEigenformWith_of_packet hp hpN hMeq ε'
      (fun ℓ => qCoeff (⇑h) ℓ) hG0 hGneb hGrel
    exact ⟨h', hh', hq⟩

end Main

end ALLiP
p2m_reactivate "P2MW.S_CuspForm_IsEigenformWith_exists_changeLevel_and_qCoeff_sq_eq_or_exists_isEigenformWith_of_dvd_of_not_sq_dvd_of_not_dvd_conductor.ALLiP"

end
p2m_reactivate "P2MW.S_CuspForm_IsEigenformWith_exists_changeLevel_and_qCoeff_sq_eq_or_exists_isEigenformWith_of_dvd_of_not_sq_dvd_of_not_dvd_conductor.ALLiP"

open scoped MatrixGroups in
theorem solution
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h)
    (p : ℕ) (hp : p.Prime) (hpM : p ∣ M) (hp2 : ¬ p ^ 2 ∣ M) (hpε : ¬ p ∣ ε.conductor) :
    ∃ ε' : DirichletCharacter ℂ (M / p),
      ε = DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hpM) ε' ∧
      (ModularFormClass.qCoeff h p ^ 2 = ε' (p : ZMod (M / p)) ∨
       ∃ h' : CuspForm (CongruenceSubgroup.Gamma1 (M / p)) 2,
         CuspForm.IsEigenformWith ε' h' ∧
         ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ModularFormClass.qCoeff h' ℓ = ModularFormClass.qCoeff h ℓ) :=
  ALLiP.main hh p hp hpM hp2 hpε

end S_CuspForm_IsEigenformWith_exists_changeLevel_and_qCoeff_sq_eq_or_exists_isEigenformWith_of_dvd_of_not_sq_dvd_of_not_dvd_conductor
end P2MW
export P2MW.S_CuspForm_IsEigenformWith_exists_changeLevel_and_qCoeff_sq_eq_or_exists_isEigenformWith_of_dvd_of_not_sq_dvd_of_not_dvd_conductor (solution)
