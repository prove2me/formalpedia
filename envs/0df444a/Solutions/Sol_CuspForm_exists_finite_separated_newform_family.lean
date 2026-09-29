-- Prove2me | solution 1 for CuspForm.exists_finite_separated_newform_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/8e895ea1-b036-55d3-b2ef-c4a8452d1cc5

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Theorems.Thm_CuspForm_span_rescaleLin_isNewform_eq_top
import Theorems.Thm_CuspForm_IsNewform_level_eq_and_qCoeff_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_finite_separated_newform_family
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups

namespace NewformFamily

abbrev S (N : ℕ) := CuspForm (CongruenceSubgroup.Gamma0 N) 2

theorem hΓ (M : ℕ) : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 M : Subgroup SL(2, ℤ)) :
    Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp

def oldNew (M : ℕ) [NeZero M] : Set (S M) :=
  {F | ∃ (R d : ℕ) (hdRM : d * R ∣ M) (g : S R), CuspForm.IsNewform g ∧
    F = FreyPackage.ModMCarrier.rescaleLin hdRM 2 g}

theorem exists_finset (M : ℕ) [NeZero M] :
    ∃ t : Finset (S M), ↑t ⊆ oldNew M ∧ Submodule.span ℂ (↑t : Set (S M)) = ⊤ := by
  haveI := CuspForm.finiteDimensional_Gamma0 M 2
  have htop : Submodule.span ℂ (oldNew M) = ⊤ := CuspForm.span_rescaleLin_isNewform_eq_top M
  have hfg : (Submodule.span ℂ (oldNew M)).FG := by rw [htop]; exact Module.Finite.fg_top
  obtain ⟨t, ht, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (oldNew M)).mp hfg
  exact ⟨t, ht, by rw [← hspan, htop]⟩

theorem main (M : ℕ) [NeZero M] :
    ∃ (ι : Type) (_ : Fintype ι) (N : ι → ℕ) (_ : ∀ i, N i ∣ M) (g : ∀ i, S (N i)),
      (∀ i, CuspForm.IsNewform (g i)) ∧
      Submodule.span ℂ {F : S M | ∃ (i : ι) (d : ℕ) (h : d * N i ∣ M),
        F = FreyPackage.ModMCarrier.rescaleLin h 2 (g i)} = ⊤ ∧
      (∀ i j, i ≠ j → ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ ℓ ∣ M ∧
        ModularFormClass.qCoeff (g i) ℓ ≠ ModularFormClass.qCoeff (g j) ℓ) := by
  classical
  obtain ⟨t, ht, hspan⟩ := exists_finset M
  have hdata : ∀ F ∈ t, ∃ (R d : ℕ) (hdRM : d * R ∣ M) (g : S R), CuspForm.IsNewform g ∧
      F = FreyPackage.ModMCarrier.rescaleLin hdRM 2 g := fun F hF => ht hF
  choose R d hdRM h hnew heq using hdata

  let I : Finset (Σ R : ℕ, S R) := t.attach.image fun x => ⟨R x.1 x.2, h x.1 x.2⟩
  refine ⟨↥I, inferInstance, fun i => i.1.1, fun i => ?_, fun i => i.1.2, fun i => ?_, ?_, ?_⟩
  ·
    show i.1.1 ∣ M
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp i.2
    rw [← hx]
    exact (Dvd.intro_left _ rfl).trans (hdRM x.1 x.2)
  ·
    show CuspForm.IsNewform i.1.2
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp i.2
    rw [← hx]
    exact hnew x.1 x.2
  ·
    refine top_le_iff.mp (hspan ▸ Submodule.span_le.mpr fun F hF => ?_)
    have hmem : (⟨R F hF, h F hF⟩ : Σ R : ℕ, S R) ∈ I :=
      Finset.mem_image.mpr ⟨⟨F, hF⟩, Finset.mem_attach _ _, rfl⟩
    exact Submodule.subset_span ⟨⟨_, hmem⟩, d F hF, hdRM F hF, heq F hF⟩
  ·
    rintro ⟨⟨A, gi⟩, hi⟩ ⟨⟨B, gj⟩, hj⟩ hij
    by_contra hno
    have hagree : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M →
        ModularFormClass.qCoeff gi ℓ = ModularFormClass.qCoeff gj ℓ :=
      fun ℓ hℓ hℓM => by_contra fun hne => hno ⟨ℓ, hℓ, hℓM, hne⟩
    have hgi : CuspForm.IsNewform gi := by
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hi
      rw [Sigma.mk.inj_iff] at hx
      obtain ⟨rfl, hx2⟩ := hx
      exact (eq_of_heq hx2) ▸ hnew x.1 x.2
    have hgj : CuspForm.IsNewform gj := by
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hj
      rw [Sigma.mk.inj_iff] at hx
      obtain ⟨rfl, hx2⟩ := hx
      exact (eq_of_heq hx2) ▸ hnew x.1 x.2
    have hA : A ∣ M := by
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hi
      rw [Sigma.mk.inj_iff] at hx
      exact hx.1 ▸ (Dvd.intro_left _ rfl).trans (hdRM x.1 x.2)
    have hB : B ∣ M := by
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hj
      rw [Sigma.mk.inj_iff] at hx
      exact hx.1 ▸ (Dvd.intro_left _ rfl).trans (hdRM x.1 x.2)
    obtain ⟨rfl, hall⟩ := hgi.level_eq_and_qCoeff_eq_of_forall_qCoeff_eq hgj hA hB hagree
    have hgg : gi = gj := ModularFormClass.eq_of_forall_qCoeff_eq (hΓ A) hall
    subst hgg
    exact hij rfl

end NewformFamily

theorem solution (M : ℕ) [NeZero M] :
    ∃ (ι : Type) (_ : Fintype ι) (N : ι → ℕ) (hN : ∀ i, N i ∣ M)
      (g : ∀ i, CuspForm (CongruenceSubgroup.Gamma0 (N i)) 2),
      (∀ i, CuspForm.IsNewform (g i)) ∧
      Submodule.span ℂ {F : CuspForm (CongruenceSubgroup.Gamma0 M) 2 |
        ∃ (i : ι) (d : ℕ) (h : d * N i ∣ M), F = FreyPackage.ModMCarrier.rescaleLin h 2 (g i)} = ⊤ ∧
      (∀ i j, i ≠ j → ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ ℓ ∣ M ∧
        ModularFormClass.qCoeff (g i) ℓ ≠ ModularFormClass.qCoeff (g j) ℓ) :=
  NewformFamily.main M

end

end S_CuspForm_exists_finite_separated_newform_family
end P2MW
export P2MW.S_CuspForm_exists_finite_separated_newform_family (solution)
