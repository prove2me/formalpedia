-- Prove2me | solution 1 for CuspForm.heckeTLin_mem_adjoin_heckeTLin_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/274a3c94-73e6-5c81-bc40-2c80225761bb

import Mathlib
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Theorems.Thm_CuspForm_heckeTLin_comm
import Theorems.Thm_CuspForm_span_rescaleLin_isNewform_eq_top
import Theorems.Thm_CuspForm_heckeTLin_rescaleLin
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin
import Theorems.Thm_CuspForm_IsNewform_level_eq_and_qCoeff_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeTLin_mem_adjoin_heckeTLin_of_finite
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open ModularFormClass
open scoped IsMulCommutative

namespace ESD3C3

variable {N : ℕ} [NeZero N] (S : Set ℕ)

abbrev I (N : ℕ) (S : Set ℕ) : Type := {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ S}

def T (ℓ : I N S) : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
  CuspForm.heckeTLin 2 ℓ.2.1 ℓ.2.2.1

theorem T_comm (ℓ ℓ' : I N S) : Commute (T S ℓ) (T S ℓ') :=
  CuspForm.heckeTLin_comm 2 ℓ.2.1 ℓ.2.2.1 ℓ'.2.1 ℓ'.2.2.1

theorem genSet_eq :
    {T' : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) |
        ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S ∧ T' = CuspForm.heckeTLin 2 hℓ hℓN} =
      Set.range (T (N := N) S) := by
  ext T'
  constructor
  · rintro ⟨ℓ, hℓ, hℓN, hℓS, rfl⟩
    exact ⟨⟨ℓ, hℓ, hℓN, hℓS⟩, rfl⟩
  · rintro ⟨⟨ℓ, hℓ, hℓN, hℓS⟩, rfl⟩
    exact ⟨ℓ, hℓ, hℓN, hℓS, rfl⟩

abbrev A₀ : Subalgebra ℂ (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) :=
  Algebra.adjoin ℂ (Set.range (T (N := N) S))

scoped instance : IsMulCommutative ↥(A₀ (N := N) S) :=
  Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨ℓ, rfl⟩ _ ⟨ℓ', rfl⟩
    exact T_comm S ℓ ℓ')

def Esp (μ : I N S → ℂ) : Submodule ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
  ⨅ ℓ, Module.End.eigenspace (T S ℓ) (μ ℓ)

theorem mem_Esp {μ : I N S → ℂ} {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} :
    f ∈ Esp S μ ↔ ∀ ℓ, T S ℓ f = μ ℓ • f := by
  simp [Esp, Submodule.mem_iInf]

theorem iSupIndep_Esp : iSupIndep (fun μ : I N S → ℂ => Esp S μ) := by
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (T (N := N) S)
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (T_comm S j i) φ)
  refine h.mono fun μ => ?_
  exact iInf_mono fun ℓ => Module.End.eigenspace_le_maxGenEigenspace

theorem exists_scalar (μ : I N S → ℂ) (x : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))
    (hx : x ∈ A₀ (N := N) S) : ∃ c : ℂ, ∀ f ∈ Esp S μ, x f = c • f := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨ℓ, rfl⟩ := hx
    exact ⟨μ ℓ, fun f hf => (mem_Esp S).mp hf ℓ⟩
  | algebraMap r => exact ⟨r, fun f _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, fun f hf => by rw [LinearMap.add_apply, hc f hf, hd f hf, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    refine ⟨c * d, fun f hf => ?_⟩
    rw [Module.End.mul_apply, hd f hf, map_smul, hc f hf, smul_smul, mul_comm]

abbrev P : Type := {μ : I N S → ℂ // Esp S μ ≠ ⊥}

scoped instance fintypeP : Fintype (P (N := N) S) := by
  haveI : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
    CuspForm.finiteDimensional_Gamma0 N 2
  exact (iSupIndep_Esp (N := N) S).fintypeNeBotOfFiniteDimensional

theorem exists_separator {μ μ' : I N S → ℂ} (h : μ ≠ μ') :
    ∃ p : ↥(A₀ (N := N) S), (∀ f ∈ Esp S μ, (p : Module.End ℂ _) f = f) ∧
      ∀ f ∈ Esp S μ', (p : Module.End ℂ _) f = 0 := by
  obtain ⟨ℓ, hℓ⟩ := Function.ne_iff.mp h
  have hne : μ ℓ - μ' ℓ ≠ 0 := sub_ne_zero.mpr hℓ
  refine ⟨(μ ℓ - μ' ℓ)⁻¹ • (⟨T S ℓ, Algebra.subset_adjoin ⟨ℓ, rfl⟩⟩ - algebraMap ℂ _ (μ' ℓ)), ?_, ?_⟩
  · intro f hf
    have h1 := (mem_Esp S).mp hf ℓ
    simp only [SetLike.val_smul, AddSubgroupClass.coe_sub, Subalgebra.coe_algebraMap,
      LinearMap.smul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply, h1]
    rw [← sub_smul, smul_smul, inv_mul_cancel₀ hne, one_smul]
  · intro f hf
    have h1 := (mem_Esp S).mp hf ℓ
    simp only [SetLike.val_smul, AddSubgroupClass.coe_sub, Subalgebra.coe_algebraMap,
      LinearMap.smul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply, h1, sub_self,
      smul_zero]

theorem exists_idempotent (μ : P (N := N) S) :
    ∃ e : ↥(A₀ (N := N) S), (∀ f ∈ Esp S μ.1, (e : Module.End ℂ _) f = f) ∧
      ∀ μ' : P (N := N) S, μ' ≠ μ → ∀ f ∈ Esp S μ'.1, (e : Module.End ℂ _) f = 0 := by
  classical

  have hsep : ∀ μ' : {μ' : P (N := N) S // μ' ≠ μ}, ∃ p : ↥(A₀ (N := N) S),
      (∀ f ∈ Esp S μ.1, (p : Module.End ℂ _) f = f) ∧
        ∀ f ∈ Esp S μ'.1.1, (p : Module.End ℂ _) f = 0 := by
    intro μ'
    refine exists_separator S (μ := μ.1) (μ' := μ'.1.1) ?_
    intro h
    exact μ'.2 (Subtype.ext h.symm)
  choose p hp1 hp0 using hsep
  refine ⟨∏ μ', p μ', ?_, ?_⟩
  ·
    intro f hf
    have key : ∀ s : Finset {μ' : P (N := N) S // μ' ≠ μ},
        ((∏ μ' ∈ s, p μ' : ↥(A₀ (N := N) S)) : Module.End ℂ _) f = f := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Subalgebra.coe_mul, Module.End.mul_apply, ih, hp1 a f hf]
    exact key Finset.univ
  · intro μ' hμ' f hf
    have hsplit : (∏ ν, p ν : ↥(A₀ (N := N) S)) =
        (∏ ν ∈ Finset.univ.erase ⟨μ', hμ'⟩, p ν) * p ⟨μ', hμ'⟩ :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm
    rw [hsplit, Subalgebra.coe_mul, Module.End.mul_apply, hp0 ⟨μ', hμ'⟩ f hf, map_zero]

theorem neZero_of_mul_dvd {R d : ℕ} (hdRN : d * R ∣ N) : NeZero R :=
  ⟨by rintro rfl; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd (by simpa using hdRN))⟩

def pk {R : ℕ} (g' : CuspForm (CongruenceSubgroup.Gamma0 R) 2) : I N S → ℂ := fun ℓ => qCoeff g' ℓ

theorem rescale_mem_Esp {R d : ℕ} (hdRN : d * R ∣ N)
    (g' : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (hg' : CuspForm.IsNewform g') :
    FreyPackage.ModMCarrier.rescaleLin hdRN 2 g' ∈ Esp S (pk (N := N) S g') := by
  haveI : NeZero R := neZero_of_mul_dvd hdRN
  rw [mem_Esp]
  intro ℓ
  have hℓR : ¬ (ℓ : ℕ) ∣ R := fun h => ℓ.2.2.1 (h.trans ((Dvd.intro_left d rfl).trans hdRN))
  have heig := ((CuspForm.isNormalizedEigenform_iff_heckeTLin g').1 hg'.1).2 ℓ ℓ.2.1
  rw [T, CuspForm.heckeTLin_rescaleLin hdRN ℓ.2.1 ℓ.2.2.1 hℓR g', heig.1 hℓR, map_smul]
  rfl

variable {ℓ₀ : ℕ} (hℓ₀ : ℓ₀.Prime) (hℓ₀N : ¬ ℓ₀ ∣ N)

theorem heckeTLin_rescale {R d : ℕ} (hdRN : d * R ∣ N)
    (g' : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (hg' : CuspForm.IsNewform g') :
    CuspForm.heckeTLin 2 hℓ₀ hℓ₀N (FreyPackage.ModMCarrier.rescaleLin hdRN 2 g') =
      qCoeff g' ℓ₀ • FreyPackage.ModMCarrier.rescaleLin hdRN 2 g' := by
  haveI : NeZero R := neZero_of_mul_dvd hdRN
  have hℓR : ¬ ℓ₀ ∣ R := fun h => hℓ₀N (h.trans ((Dvd.intro_left d rfl).trans hdRN))
  have heig := ((CuspForm.isNormalizedEigenform_iff_heckeTLin g').1 hg'.1).2 ℓ₀ hℓ₀
  rw [CuspForm.heckeTLin_rescaleLin hdRN hℓ₀ hℓ₀N hℓR g', heig.1 hℓR, map_smul]

variable (hSfin : S.Finite)

include hSfin in

theorem qCoeff_eq_of_pk_eq {R d R' d' : ℕ} (hdRN : d * R ∣ N) (hdRN' : d' * R' ∣ N)
    (g' : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (hg' : CuspForm.IsNewform g')
    (g'' : CuspForm (CongruenceSubgroup.Gamma0 R') 2) (hg'' : CuspForm.IsNewform g'')
    (hpk : pk (N := N) S g' = pk (N := N) S g'') (n : ℕ) : qCoeff g' n = qCoeff g'' n := by

  let Q : ℕ := ∏ q ∈ hSfin.toFinset, max q 1
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q _ => by
    exact Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le Nat.zero_lt_one (le_max_right q 1))
  haveI : NeZero (N * Q) := ⟨mul_ne_zero (NeZero.ne N) hQ⟩
  have hR : R ∣ N * Q := ((Dvd.intro_left d rfl).trans hdRN).trans (Dvd.intro _ rfl)
  have hR' : R' ∣ N * Q := ((Dvd.intro_left d' rfl).trans hdRN').trans (Dvd.intro _ rfl)
  have h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * Q → qCoeff g' ℓ = qCoeff g'' ℓ := by
    intro ℓ hℓ hℓNQ
    have hℓN : ¬ ℓ ∣ N := fun h => hℓNQ (h.mul_right Q)
    have hℓS : ℓ ∉ S := by
      intro hS
      apply hℓNQ
      have h1 : max ℓ 1 ∣ Q := Finset.dvd_prod_of_mem (fun q => max q 1) (hSfin.mem_toFinset.mpr hS)
      rw [max_eq_left hℓ.one_lt.le] at h1
      exact h1.mul_left N
    exact congrFun hpk ⟨ℓ, hℓ, hℓN, hℓS⟩
  exact (CuspForm.IsNewform.level_eq_and_qCoeff_eq_of_forall_qCoeff_eq hg' hg'' hR hR' h).2 n

def cval (μ : I N S → ℂ) : ℂ := by
  classical
  exact if h : ∃ (R d : ℕ) (_ : d * R ∣ N) (g' : CuspForm (CongruenceSubgroup.Gamma0 R) 2),
      CuspForm.IsNewform g' ∧ pk (N := N) S g' = μ then qCoeff h.choose_spec.choose_spec.choose_spec.choose ℓ₀
    else 0

include hSfin in
theorem cval_eq {R d : ℕ} (hdRN : d * R ∣ N) (g' : CuspForm (CongruenceSubgroup.Gamma0 R) 2)
    (hg' : CuspForm.IsNewform g') : cval (N := N) S (ℓ₀ := ℓ₀) (pk (N := N) S g') = qCoeff g' ℓ₀ := by
  classical
  have hex : ∃ (R' d' : ℕ) (_ : d' * R' ∣ N) (g'' : CuspForm (CongruenceSubgroup.Gamma0 R') 2),
      CuspForm.IsNewform g'' ∧ pk (N := N) S g'' = pk (N := N) S g' := ⟨R, d, hdRN, g', hg', rfl⟩
  rw [cval, dif_pos hex]
  obtain ⟨hg'', hpk⟩ := hex.choose_spec.choose_spec.choose_spec.choose_spec
  exact qCoeff_eq_of_pk_eq S hSfin hex.choose_spec.choose_spec.choose hdRN _ hg'' g' hg' hpk ℓ₀

include hSfin in
theorem heckeTLin_mem_A₀ : CuspForm.heckeTLin 2 hℓ₀ hℓ₀N ∈ A₀ (N := N) S := by
  classical

  choose e he1 he0 using exists_idempotent (N := N) S

  set X : ↥(A₀ (N := N) S) := ∑ μ : P (N := N) S, cval (N := N) S (ℓ₀ := ℓ₀) μ.1 • e μ with hX
  suffices h : CuspForm.heckeTLin 2 hℓ₀ hℓ₀N = (X : Module.End ℂ _) by
    rw [h]; exact X.2

  have hspan := CuspForm.span_rescaleLin_isNewform_eq_top N
  refine LinearMap.ext_on hspan ?_
  rintro F ⟨R, d, hdRN, g', hg', rfl⟩
  set μ₀ := pk (N := N) S g' with hμ₀
  have hFmem : FreyPackage.ModMCarrier.rescaleLin hdRN 2 g' ∈ Esp S μ₀ := rescale_mem_Esp S hdRN g' hg'

  have hXsum : (X : Module.End ℂ _) (FreyPackage.ModMCarrier.rescaleLin hdRN 2 g') =
      ∑ μ : P (N := N) S, cval (N := N) S (ℓ₀ := ℓ₀) μ.1 •
        (e μ : Module.End ℂ _) (FreyPackage.ModMCarrier.rescaleLin hdRN 2 g') := by
    rw [hX, AddSubmonoidClass.coe_finsetSum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Subalgebra.coe_smul, LinearMap.smul_apply]
  rw [heckeTLin_rescale hℓ₀ hℓ₀N hdRN g' hg', hXsum]
  by_cases hbot : Esp S μ₀ = ⊥
  ·
    have hF0 : FreyPackage.ModMCarrier.rescaleLin hdRN 2 g' = 0 := by
      rw [hbot] at hFmem
      exact (Submodule.mem_bot ℂ).mp hFmem
    simp [hF0]
  ·
    let μ₁ : P (N := N) S := ⟨μ₀, hbot⟩
    rw [Finset.sum_eq_single μ₁]
    · rw [he1 μ₁ _ hFmem]
      show qCoeff g' ℓ₀ • _ = cval (N := N) S (ℓ₀ := ℓ₀) (pk (N := N) S g') • _
      rw [cval_eq S hSfin hdRN g' hg']
    · intro μ _ hμ
      rw [he0 μ μ₁ (fun h => hμ h.symm) _ hFmem, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ μ₁) h

end ESD3C3
p2m_reactivate "P2MW.S_CuspForm_heckeTLin_mem_adjoin_heckeTLin_of_finite.ESD3C3"

theorem solution (N : ℕ) [NeZero N] (S : Set ℕ)
    (hSfin : S.Finite) {ℓ₀ : ℕ} (hℓ₀ : ℓ₀.Prime) (hℓ₀N : ¬ ℓ₀ ∣ N) :
    CuspForm.heckeTLin 2 hℓ₀ hℓ₀N ∈ Algebra.adjoin ℂ
      {T : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) |
        ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S ∧ T = CuspForm.heckeTLin 2 hℓ hℓN} := by
  rw [ESD3C3.genSet_eq S]
  exact ESD3C3.heckeTLin_mem_A₀ S hℓ₀ hℓ₀N hSfin

end
end S_CuspForm_heckeTLin_mem_adjoin_heckeTLin_of_finite
end P2MW
export P2MW.S_CuspForm_heckeTLin_mem_adjoin_heckeTLin_of_finite (solution)
