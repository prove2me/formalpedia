-- Prove2me | solution 1 for CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/bff2eae6-6768-54a6-9368-1b0ab58ff4ca

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_PeterssonOn
import Theorems.Thm_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus
import Theorems.Thm_CuspForm_peterssonOn_add_smul_conj
import Theorems.Thm_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff
import Theorems.Thm_ModularForm_periodic_heckeU_comp_ofComplex
import Theorems.Thm_UpperHalfPlane_qCoeff_heckeU
import Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_conj_heckeEigenvalue_eq_of_hasNebentypus
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero"

set_option autoImplicit false

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter Function
open scoped ModularForm MatrixGroups ComplexConjugate

noncomputable section

namespace HeckeEigenvalueConj

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Phi

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

def phi (k : ℤ) (p : ℕ) (c : ℂ) (F : ℍ → ℂ) : ℍ → ℂ :=
  heckeU k p F + c • (F ∣[k] heckeDiagMatrix p)

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

end Phi

section Main

variable {M : ℕ} [NeZero M] {k : ℤ}

local notation "⟪" f ", " g "⟫" => CuspForm.peterssonOn (Gamma1 M) k f g

omit [NeZero M] in
theorem conj_dirichlet [NeZero M] (ε : DirichletCharacter ℂ M) (a : ZMod M) : conj (ε a) = ε⁻¹ a := by
  have := MulChar.star_apply' ε a
  rwa [RCLike.star_def] at this

theorem petersson_smul_left (f g : CuspForm (Γ₁ℝ M) k) (c : ℂ) :
    ⟪c • ⇑f, ⇑g⟫ = conj c * ⟪⇑f, ⇑g⟫ := by
  obtain ⟨-, h2, -⟩ := CuspForm.peterssonOn_add_smul_conj (Gamma1 M) k g f f c
  obtain ⟨-, -, h3⟩ := CuspForm.peterssonOn_add_smul_conj (Gamma1 M) k f g f c
  obtain ⟨-, -, h3'⟩ := CuspForm.peterssonOn_add_smul_conj (Gamma1 M) k (c • f) g f c

  have h3'' : conj ⟪⇑g, c • ⇑f⟫ = ⟪c • ⇑f, ⇑g⟫ := h3'
  rw [← h3'', h2, map_mul, h3]

theorem main (ε : DirichletCharacter ℂ M) (g : CuspForm (Γ₁ℝ M) k)
    (hg0 : g ≠ 0) (hg : CuspForm.HasNebentypus ε g) (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M)
    (lam : ℂ)
    (heig : ∀ n : ℕ, qCoeff (⇑g) (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff (⇑g) (n / p) else 0) =
      lam * qCoeff (⇑g) n) :
    conj lam = ε⁻¹ (p : ZMod M) * lam := by
  have hp0 : p ≠ 0 := hp.ne_zero

  have hT : heckeU k p ⇑g + ε (p : ZMod M) • (⇑g ∣[k] heckeDiagMatrix p) = lam • (⇑g : ℍ → ℂ) :=
    phi_eq_smul_of_qCoeff g hp0 (ε (p : ZMod M)) lam heig

  have hadj := CuspForm.peterssonOn_hecke_eq_conj_mul_of_hasNebentypus M k ε hp hpM g g hg hg
  rw [hT] at hadj
  obtain ⟨-, hlin, -⟩ := CuspForm.peterssonOn_add_smul_conj (Gamma1 M) k g g g lam
  obtain ⟨-, -, hpos⟩ := CuspForm.peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff (Gamma1 M) k g
  have hne : ⟪⇑g, ⇑g⟫ ≠ 0 := fun h0 => hg0 (hpos.1 h0)

  rw [petersson_smul_left, hlin, conj_dirichlet] at hadj
  have := mul_right_cancel₀ hne (hadj.trans (mul_assoc _ _ _).symm)
  exact this

end Main

end HeckeEigenvalueConj
p2m_reactivate "P2MW.S_CuspForm_conj_heckeEigenvalue_eq_of_hasNebentypus.HeckeEigenvalueConj"

end
p2m_reactivate "P2MW.S_CuspForm_conj_heckeEigenvalue_eq_of_hasNebentypus.HeckeEigenvalueConj"

open scoped MatrixGroups in
theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k)
    (hg0 : g ≠ 0) (hg : CuspForm.HasNebentypus ε g) (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M)
    (lam : ℂ)
    (heig : ∀ n : ℕ, ModularFormClass.qCoeff g (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
          (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
      lam * ModularFormClass.qCoeff g n) :
    starRingEnd ℂ lam = ε⁻¹ (p : ZMod M) * lam :=
  HeckeEigenvalueConj.main ε g hg0 hg p hp hpM lam heig

end S_CuspForm_conj_heckeEigenvalue_eq_of_hasNebentypus
end P2MW
export P2MW.S_CuspForm_conj_heckeEigenvalue_eq_of_hasNebentypus (solution)
