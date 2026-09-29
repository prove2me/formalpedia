-- Prove2me | solution 1 for CuspForm.IsNewform.eq_of_isNormalizedEigenform_forall_prime_notMem_qCoeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/45884129-5d8f-56d6-a88f-528e368e5bf3

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_Petersson
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Theorems.Thm_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul
import Theorems.Thm_CuspForm_IsNewform_finrank_iInf_eigenspace_dualMap_heckeTLin_eq_one
import Theorems.Thm_CuspForm_petersson_heckeTLin
import Theorems.Thm_CuspForm_petersson_self_eq_zero_iff
import Theorems.Thm_CuspForm_petersson_conj_symm
import Theorems.Thm_CuspForm_petersson_smul_left
import Theorems.Thm_CuspForm_petersson_add_left
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_eq_of_isNormalizedEigenform_forall_prime_notMem_qCoeff_eq
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false
open ModularFormClass

noncomputable section

namespace CuspForm p2m_export "CuspForm" "smul_apply coe_zero ext IsNewform IsNormalizedEigenform petersson finiteDimensional_Gamma0 IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul heckeTLin petersson_heckeTLin petersson_self_eq_zero_iff petersson_conj_symm petersson_smul_left petersson_add_left" end CuspForm
p2m_open_scoped "CuspForm" in

private theorem CuspForm.petersson_add_right {N : ℕ} {k : ℤ} [NeZero N]
    (f g₁ g₂ : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson f (g₁ + g₂) = CuspForm.petersson f g₁ + CuspForm.petersson f g₂ := by
  rw [← CuspForm.petersson_conj_symm, CuspForm.petersson_add_left, map_add,
    CuspForm.petersson_conj_symm, CuspForm.petersson_conj_symm]

p2m_open_scoped "CuspForm" in

private theorem CuspForm.petersson_smul_right {N : ℕ} {k : ℤ} [NeZero N]
    (c : ℂ) (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson f (c • g) = c * CuspForm.petersson f g := by
  rw [← CuspForm.petersson_conj_symm, CuspForm.petersson_smul_left, map_mul,
    RingHomCompTriple.comp_apply, RingHom.id_apply, CuspForm.petersson_conj_symm]

p2m_open_scoped "CuspForm" in
private theorem CuspForm.petersson_sub_right {N : ℕ} {k : ℤ} [NeZero N]
    (f g₁ g₂ : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson f (g₁ - g₂) = CuspForm.petersson f g₁ - CuspForm.petersson f g₂ := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ g₂, CuspForm.petersson_add_right,
    CuspForm.petersson_smul_right, neg_one_mul, ← sub_eq_add_neg]

p2m_open_scoped "CuspForm" in

private def CuspForm.peterssonLinR {N : ℕ} {k : ℤ} [NeZero N]
    (h : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] ℂ where
  toFun x := CuspForm.petersson h x
  map_add' := CuspForm.petersson_add_right h
  map_smul' c x := by simp [CuspForm.petersson_smul_right]

p2m_open_scoped "CuspForm" in
private theorem CuspForm.peterssonLinR_apply {N : ℕ} {k : ℤ} [NeZero N]
    (h x : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.peterssonLinR h x = CuspForm.petersson h x := rfl

p2m_open_scoped "CuspForm" in

private theorem CuspForm.qCoeff_conj_eq_self_of_isNormalizedEigenform {M : ℕ} [NeZero M]
    {v : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hv : v.IsNormalizedEigenform)
    (hv_ne : v ≠ 0) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    starRingEnd ℂ (qCoeff v ℓ) = qCoeff v ℓ := by
  have hvv : CuspForm.petersson v v ≠ 0 := by
    rwa [Ne, CuspForm.petersson_self_eq_zero_iff]
  have heig : CuspForm.heckeTLin 2 hℓ hℓM v = qCoeff v ℓ • v :=
    CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul M v hv ℓ hℓ hℓM
  have key : starRingEnd ℂ (qCoeff v ℓ) * CuspForm.petersson v v =
      qCoeff v ℓ * CuspForm.petersson v v := by
    calc starRingEnd ℂ (qCoeff v ℓ) * CuspForm.petersson v v
        = CuspForm.petersson (qCoeff v ℓ • v) v := (CuspForm.petersson_smul_left _ v v).symm
      _ = CuspForm.petersson (CuspForm.heckeTLin 2 hℓ hℓM v) v := by rw [heig]
      _ = CuspForm.petersson v (CuspForm.heckeTLin 2 hℓ hℓM v) := CuspForm.petersson_heckeTLin ..
      _ = CuspForm.petersson v (qCoeff v ℓ • v) := by rw [heig]
      _ = qCoeff v ℓ * CuspForm.petersson v v := CuspForm.petersson_smul_right _ v v
  exact mul_right_cancel₀ hvv key

theorem solution
    {M : ℕ} [NeZero M]
    {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hf : f.IsNormalizedEigenform)
    (S : Finset ℕ)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S →
      ModularFormClass.qCoeff f ℓ = ModularFormClass.qCoeff g ℓ) :
    f = g := by
  haveI : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2) :=
    CuspForm.finiteDimensional_Gamma0 M 2

  have hg_ne : g ≠ 0 := by
    intro hg0
    have h1 : qCoeff g 1 = 1 := hg.1.qCoeff_one
    rw [hg0, show ((0 : CuspForm (CongruenceSubgroup.Gamma0 M) 2) : UpperHalfPlane → ℂ) = 0
        from CuspForm.coe_zero] at h1
    simp only [qCoeff, UpperHalfPlane.qExpansion_zero, map_zero] at h1
    exact one_ne_zero h1.symm
  have hgg_ne : CuspForm.petersson g g ≠ 0 := by
    rwa [Ne, CuspForm.petersson_self_eq_zero_iff]

  set Edual : Submodule ℂ (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) :=
    ⨅ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ M ∧ ℓ ∉ S},
      Module.End.eigenspace (CuspForm.heckeTLin 2 ℓ.2.1 ℓ.2.2.1).dualMap (qCoeff g ℓ)
    with hEdual_def
  have hrank : Module.finrank ℂ Edual = 1 := by
    rw [hEdual_def]; exact hg.finrank_iInf_eigenspace_dualMap_heckeTLin_eq_one S

  have hφ_mem : ∀ v : CuspForm (CongruenceSubgroup.Gamma0 M) 2,
      (∀ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ M ∧ ℓ ∉ S},
        CuspForm.heckeTLin 2 ℓ.2.1 ℓ.2.2.1 v = qCoeff g ℓ • v) →
      CuspForm.peterssonLinR v ∈ Edual := by
    intro v hv
    rw [hEdual_def, Submodule.mem_iInf]
    intro ℓ
    rw [Module.End.mem_eigenspace_iff]
    ext x
    simp only [LinearMap.dualMap_apply, CuspForm.peterssonLinR_apply, LinearMap.smul_apply,
      smul_eq_mul]
    have haℓ_real : starRingEnd ℂ (qCoeff g ℓ) = qCoeff g ℓ :=
      CuspForm.qCoeff_conj_eq_self_of_isNormalizedEigenform hg.1 hg_ne ℓ.2.1 ℓ.2.2.1
    calc CuspForm.petersson v (CuspForm.heckeTLin 2 ℓ.2.1 ℓ.2.2.1 x)
        = CuspForm.petersson (CuspForm.heckeTLin 2 ℓ.2.1 ℓ.2.2.1 v) x :=
          (CuspForm.petersson_heckeTLin ..).symm
      _ = CuspForm.petersson (qCoeff g ℓ • v) x := by rw [hv ℓ]
      _ = starRingEnd ℂ (qCoeff g ℓ) * CuspForm.petersson v x :=
          CuspForm.petersson_smul_left _ v x
      _ = qCoeff g ℓ * CuspForm.petersson v x := by rw [haℓ_real]

  have hf_eig : ∀ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ M ∧ ℓ ∉ S},
      CuspForm.heckeTLin 2 ℓ.2.1 ℓ.2.2.1 f = qCoeff g ℓ • f := fun ℓ => by
    rw [← h ℓ ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2]
    exact CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul M f hf ℓ ℓ.2.1 ℓ.2.2.1
  have hg_eig : ∀ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ M ∧ ℓ ∉ S},
      CuspForm.heckeTLin 2 ℓ.2.1 ℓ.2.2.1 g = qCoeff g ℓ • g := fun ℓ =>
    CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul M g hg.1 ℓ ℓ.2.1 ℓ.2.2.1

  set c : ℂ := CuspForm.petersson g f / CuspForm.petersson g g with hc_def
  set w : CuspForm (CongruenceSubgroup.Gamma0 M) 2 := f - c • g with hw_def

  have hw_eig : ∀ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ M ∧ ℓ ∉ S},
      CuspForm.heckeTLin 2 ℓ.2.1 ℓ.2.2.1 w = qCoeff g ℓ • w := fun ℓ => by
    simp only [hw_def, map_sub, LinearMap.map_smul, hf_eig ℓ, hg_eig ℓ, smul_sub, smul_smul,
      mul_comm]

  have hgw : CuspForm.petersson g w = 0 := by
    rw [hw_def, CuspForm.petersson_sub_right, CuspForm.petersson_smul_right, hc_def,
      div_mul_cancel₀ _ hgg_ne, sub_self]

  have hφg_mem : CuspForm.peterssonLinR g ∈ Edual := hφ_mem g hg_eig
  have hφw_mem : CuspForm.peterssonLinR w ∈ Edual := hφ_mem w hw_eig
  have hφg_ne : (⟨CuspForm.peterssonLinR g, hφg_mem⟩ : Edual) ≠ 0 := by
    intro h0
    apply hgg_ne
    have := congrArg (fun ψ : Edual => (ψ : Module.Dual ℂ _) g) h0
    simpa [CuspForm.peterssonLinR_apply] using this

  obtain ⟨lam, hlam⟩ : ∃ lam : ℂ,
      (⟨CuspForm.peterssonLinR w, hφw_mem⟩ : Edual) =
        lam • ⟨CuspForm.peterssonLinR g, hφg_mem⟩ := by
    have hspan : Submodule.span ℂ {(⟨CuspForm.peterssonLinR g, hφg_mem⟩ : Edual)} = ⊤ := by
      have hr1 : Module.finrank ℂ (Submodule.span ℂ
          {(⟨CuspForm.peterssonLinR g, hφg_mem⟩ : Edual)}) = 1 :=
        finrank_span_singleton hφg_ne
      exact Submodule.eq_top_of_finrank_eq (hr1.trans hrank.symm)
    have hmem := hspan ▸ Submodule.mem_top (x := (⟨CuspForm.peterssonLinR w, hφw_mem⟩ : Edual))
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨lam, hlam⟩ := hmem
    exact ⟨lam, hlam.symm⟩

  have heval_g : CuspForm.petersson w g = lam * CuspForm.petersson g g := by
    have := congrArg (fun ψ : Edual => (ψ : Module.Dual ℂ _) g) hlam
    simpa [CuspForm.peterssonLinR_apply] using this

  have hwg : CuspForm.petersson w g = 0 := by
    rw [← CuspForm.petersson_conj_symm, hgw, map_zero]

  have hlam_zero : lam = 0 := by
    have := heval_g.symm.trans hwg
    exact (mul_eq_zero.mp this).resolve_right hgg_ne

  have hφw_zero : CuspForm.peterssonLinR w = 0 := by
    have := hlam
    rw [hlam_zero, zero_smul] at this
    exact Subtype.ext_iff.mp this
  have hww : CuspForm.petersson w w = 0 := by
    have := congrArg (fun ψ => ψ w) hφw_zero
    simpa [CuspForm.peterssonLinR_apply] using this
  have hw_zero : w = 0 := (CuspForm.petersson_self_eq_zero_iff w).mp hww

  have hfc : f = c • g := by
    have := hw_zero; rw [hw_def, sub_eq_zero] at this; exact this
  have hc_one : c = 1 := by
    have h1 : qCoeff f 1 = 1 := hf.qCoeff_one
    have hg1 : qCoeff g 1 = 1 := hg.1.qCoeff_one

    have hΓ : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
        (CongruenceSubgroup.Gamma0 M)).strictPeriods := by
      simp
    have hcoe : qCoeff f 1 = c * qCoeff g 1 := by
      have hcoe_fun : ((f : UpperHalfPlane → ℂ)) = c • (g : UpperHalfPlane → ℂ) := by
        rw [show (f : UpperHalfPlane → ℂ) = ((c • g : CuspForm _ _) : UpperHalfPlane → ℂ)
            from congrArg _ hfc]
        rfl
      unfold qCoeff
      rw [hcoe_fun, UpperHalfPlane.qExpansion_smul
        (ModularFormClass.analyticAt_cuspFunction_zero g one_pos hΓ) c]
      simp [smul_eq_mul]
    rw [h1, hg1, mul_one] at hcoe; exact hcoe.symm
  rw [hfc, hc_one, one_smul]

end

end S_CuspForm_IsNewform_eq_of_isNormalizedEigenform_forall_prime_notMem_qCoeff_eq
end P2MW
export P2MW.S_CuspForm_IsNewform_eq_of_isNormalizedEigenform_forall_prime_notMem_qCoeff_eq (solution)
