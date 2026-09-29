-- Prove2me | solution 1 for CuspForm.IsPrimitiveForm.heckeU_eigenvalue_eq_qCoeff_of_common_eigenvector_of_dvd_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/aa595c63-a352-5cf5-b01c-8cce1f401894

import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_qCoeff_heckeTLinOne
import Theorems.Thm_CuspForm_exists_hasNebentypus_of_qCoeff_hecke_eigen
import Theorems.Thm_CuspForm_exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen
import Theorems.Thm_CuspForm_IsPrimitiveForm_level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq
import Theorems.Thm_CuspForm_IsEigenformWith_dvd_and_qCoeff_eq_or_not_dvd_and_qCoeff_sq_sub_eq_zero_of_isPrimitiveForm_of_not_sq_dvd
import Theorems.Thm_CuspForm_qCoeff_zero_eq_zero_gamma1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsPrimitiveForm_heckeU_eigenvalue_eq_qCoeff_of_common_eigenvector_of_dvd_level
p2m_attr_erase "instance" "Ihara.instGroupIharaAmalgam FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false

noncomputable section

namespace OLDEIGEN

open Module Module.End Set

section QExp

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter Function
open scoped MatrixGroups ModularForm

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ M).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

theorem cusp_periodic (F : CuspForm (Γ₁ℝ M) k) : Periodic (⇑F ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex F (one_mem_strictPeriods M)

theorem cusp_holo (F : CuspForm (Γ₁ℝ M) k) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) := F.holo'

theorem cusp_bdd (F : CuspForm (Γ₁ℝ M) k) : IsBoundedAtImInfty (⇑F : ℍ → ℂ) := by
  haveI : Fact (IsCusp OnePoint.infty (Γ₁ℝ M)) :=
    ⟨(Γ₁ℝ M).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods M)⟩
  exact ModularFormClass.bdd_at_infty F

theorem cusp_ext_of_qCoeff {F G : CuspForm (Γ₁ℝ M) k} (h : ∀ n : ℕ, qCoeff (⇑F) n = qCoeff (⇑G) n) :
    F = G :=
  DFunLike.coe_injective (UpperHalfPlane.eq_of_forall_qCoeff_eq (cusp_periodic F) (cusp_holo F)
    (cusp_bdd F) (cusp_periodic G) (cusp_holo G) (cusp_bdd G) h)

theorem analyticAt_cuspFunction (F : CuspForm (Γ₁ℝ M) k) : AnalyticAt ℂ (cuspFunction 1 (⇑F)) 0 :=
  analyticAt_cuspFunction_zero one_pos (cusp_periodic F) (cusp_holo F) (cusp_bdd F)

theorem qCoeff_smul (c : ℂ) (F : CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    qCoeff (⇑(c • F)) n = c * qCoeff (⇑F) n := by
  rw [qCoeff, qCoeff, CuspForm.IsGLPos.coe_smul, qExpansion_smul (analyticAt_cuspFunction F) c, map_smul,
    smul_eq_mul]

theorem qCoeff_add (F G : CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    qCoeff (⇑(F + G)) n = qCoeff (⇑F) n + qCoeff (⇑G) n := by
  rw [qCoeff, qCoeff, qCoeff, CuspForm.coe_add,
    qExpansion_add (analyticAt_cuspFunction F) (analyticAt_cuspFunction G), map_add]

theorem qCoeff_zero' (n : ℕ) : qCoeff (⇑(0 : CuspForm (Γ₁ℝ M) k)) n = 0 := by
  rw [qCoeff, CuspForm.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero]

theorem qCoeff_sum {ι : Type} (s : Finset ι) (F : ι → CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    qCoeff (⇑(∑ i ∈ s, F i)) n = ∑ i ∈ s, qCoeff (⇑(F i)) n := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, qCoeff_zero']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, qCoeff_add, ih]

theorem ne_zero_of_qCoeff_one (F : CuspForm (Γ₁ℝ M) k) (h1 : qCoeff (⇑F) 1 = 1) : F ≠ 0 := by
  rintro rfl
  rw [qCoeff_zero'] at h1
  exact zero_ne_one h1

end QExp

section Cusp

open CongruenceSubgroup ModularForm ModularFormClass
open scoped MatrixGroups ModularForm ComplexConjugate

variable {M : ℕ} [NeZero M]

omit [NeZero M] in

theorem dirichlet_pow_totient (χ : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    χ (ℓ : ZMod M) ^ Nat.totient M = 1 := by
  rw [← ZMod.coe_unitOfCoprime ℓ hℓ, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient,
    Units.val_one, map_one]

theorem totient_ne_zero : Nat.totient M ≠ 0 := (Nat.totient_pos.2 (NeZero.pos M)).ne'

theorem dirichlet_ne_zero (χ : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    χ (ℓ : ZMod M) ≠ 0 := fun h0 => by
  have h := dirichlet_pow_totient χ hℓ
  rw [h0, zero_pow totient_ne_zero] at h
  exact zero_ne_one h

theorem conj_dirichlet (χ : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    conj (χ (ℓ : ZMod M)) = (χ (ℓ : ZMod M))⁻¹ :=
  (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one (dirichlet_pow_totient χ hℓ)
    totient_ne_zero)).symm

omit [NeZero M] in
theorem inv_apply_dirichlet (χ : DirichletCharacter ℂ M) (ℓ : ℕ) :
    χ⁻¹ (ℓ : ZMod M) = (χ (ℓ : ZMod M))⁻¹ :=
  MulChar.inv_apply_eq_inv' χ _

theorem dirichlet_ext {χ₁ χ₂ : DirichletCharacter ℂ M} (S : Finset ℕ)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → χ₁ (ℓ : ZMod M) = χ₂ (ℓ : ZMod M)) : χ₁ = χ₂ := by
  refine MulChar.ext fun u => ?_
  obtain ⟨ℓ, hℓgt, hℓp, hℓu⟩ := Nat.forall_exists_prime_gt_and_eq_mod (Units.isUnit u) (S.sup id)
  have hℓS : ℓ ∉ S := fun hmem => by
    have : ℓ ≤ S.sup id := Finset.le_sup (f := id) hmem
    omega
  have hcop : Nat.Coprime ℓ M := by
    have hu : IsUnit ((ℓ : ℕ) : ZMod M) := by rw [hℓu]; exact Units.isUnit u
    exact (ZMod.isUnit_iff_coprime ℓ M).1 hu
  have hℓM : ¬ ℓ ∣ M := fun hdvd => by
    have := Nat.Coprime.eq_one_of_dvd hcop hdvd
    exact hℓp.one_lt.ne' this
  rw [← hℓu]
  exact h ℓ hℓp hℓM hℓS

theorem hasNebentypus_smul {N : ℕ} {k : ℤ} {χ : DirichletCharacter ℂ N} {g : CuspForm (Gamma1 N) k}
    (hg : CuspForm.HasNebentypus χ g) (c : ℂ) : CuspForm.HasNebentypus χ (c • g) := by
  intro γ hγ τ
  have h := hg γ hγ τ
  simp only [CuspForm.IsGLPos.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [h]
  ring

theorem qCoeff_eq_zero_of_qCoeff_one_eq_zero {N : ℕ} {k : ℤ} (v : CuspForm (Gamma1 N) k)
    (t c u : ℕ → ℂ)
    (hT : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ∀ m : ℕ,
      qCoeff (⇑v) (ℓ * m) + c ℓ * (if ℓ ∣ m then qCoeff (⇑v) (m / ℓ) else 0) = t ℓ * qCoeff (⇑v) m)
    (hU : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ N → ∀ m : ℕ, qCoeff (⇑v) (ℓ * m) = u ℓ * qCoeff (⇑v) m)
    (h1 : qCoeff (⇑v) 1 = 0) : ∀ n : ℕ, 1 ≤ n → qCoeff (⇑v) n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge 1 n with hlt | hle
    · obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
      obtain ⟨m, rfl⟩ := hℓn
      have hm0 : m ≠ 0 := by rintro rfl; simp at hlt
      have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
      have hmn : m < ℓ * m := lt_mul_left (Nat.pos_of_ne_zero hm0) hℓ.one_lt
      by_cases hℓN : ℓ ∣ N
      · rw [hU ℓ hℓ hℓN m, ih m hmn hm1, mul_zero]
      · have h := hT ℓ hℓ hℓN m
        rw [ih m hmn hm1, mul_zero] at h
        by_cases hdm : ℓ ∣ m
        · rw [if_pos hdm] at h
          obtain ⟨r, rfl⟩ := hdm
          have hr0 : r ≠ 0 := by rintro rfl; simp at hm0
          have hdiv : ℓ * r / ℓ = r := Nat.mul_div_cancel_left r hℓ.pos
          have hrlt : r < ℓ * (ℓ * r) :=
            (lt_mul_left (Nat.pos_of_ne_zero hr0) hℓ.one_lt).trans hmn
          rw [hdiv, ih r hrlt (Nat.pos_of_ne_zero hr0), mul_zero, add_zero] at h
          exact h
        · rw [if_neg hdm, mul_zero, add_zero] at h
          exact h
    · have : n = 1 := le_antisymm hle hn
      subst this
      exact h1

theorem qCoeff_one_ne_zero_of_eigen {N : ℕ} {k : ℤ} (v : CuspForm (Gamma1 N) k) (hv0 : v ≠ 0)
    (t c u : ℕ → ℂ)
    (hT : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ∀ m : ℕ,
      qCoeff (⇑v) (ℓ * m) + c ℓ * (if ℓ ∣ m then qCoeff (⇑v) (m / ℓ) else 0) = t ℓ * qCoeff (⇑v) m)
    (hU : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ N → ∀ m : ℕ, qCoeff (⇑v) (ℓ * m) = u ℓ * qCoeff (⇑v) m) :
    qCoeff (⇑v) 1 ≠ 0 := by
  intro h1
  apply hv0
  refine cusp_ext_of_qCoeff fun n => ?_
  rw [qCoeff_zero']
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact CuspForm.qCoeff_zero_eq_zero_gamma1 v
  · exact qCoeff_eq_zero_of_qCoeff_one_eq_zero v t c u hT hU h1 n hn

theorem heckeU_eigenvalue_eq_qCoeff_of_common_eigenvector_of_dvd
    {N : ℕ} [NeZero N] (hMN : M ∣ N)
    {χ : DirichletCharacter ℂ M} {G : CuspForm (Gamma1 M) 2} (hG : CuspForm.IsPrimitiveForm χ G)
    (S : Finset ℕ) (v : CuspForm (Gamma1 N) 2) (hv0 : v ≠ 0)
    (t u δ : ℕ → ℂ)
    (hvT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), CuspForm.heckeTLinOne 2 hℓ hℓN v = t ℓ • v)
    (hvD : ∀ d : ℕ, Nat.Coprime d N → CuspForm.diamondLinOne N 2 d v = δ d • v)
    (hvU : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ N → ∀ n : ℕ, qCoeff (⇑v) (ℓ * n) = u ℓ * qCoeff (⇑v) n)
    (ht : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → t ℓ = qCoeff (⇑G) ℓ)
    (hδ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → δ ℓ = χ (ℓ : ZMod M))
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ N) :
    u q = qCoeff (⇑G) q := by
  classical
  have hqN : q ∣ N := dvd_trans hqM hMN

  have hrel : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ∀ m : ℕ,
      qCoeff (⇑v) (ℓ * m) + (ℓ * δ ℓ) * (if ℓ ∣ m then qCoeff (⇑v) (m / ℓ) else 0)
        = t ℓ * qCoeff (⇑v) m := by
    intro ℓ hℓ hℓN m
    have h := congrArg (fun F : CuspForm (Gamma1 N) 2 => qCoeff (⇑F) m) (hvT ℓ hℓ hℓN)
    rw [CuspForm.qCoeff_heckeTLinOne 2 hℓ hℓN v m, hvD ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓN),
      qCoeff_smul, qCoeff_smul] at h
    rw [← h]
    have e : ((2 : ℤ) - 1) = 1 := by norm_num
    rw [e, zpow_one]
    split_ifs <;> ring

  obtain ⟨χv, hχv, hχval⟩ := CuspForm.exists_hasNebentypus_of_qCoeff_hecke_eigen N 2 v hv0
    (fun ℓ => ℓ * δ ℓ) (fun ℓ hℓ hℓN => ⟨t ℓ, fun m => hrel ℓ hℓ hℓN m⟩)
  have hχvℓ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → χv (ℓ : ZMod N) = δ ℓ := by
    intro ℓ hℓ hℓN
    have h := hχval ℓ hℓ hℓN
    have e : ((2 : ℤ) - 1) = 1 := by norm_num
    rw [e, zpow_one, mul_comm] at h
    exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hℓ.ne_zero) h

  set a₁ := qCoeff (⇑v) 1 with ha₁
  have ha₁0 : a₁ ≠ 0 := qCoeff_one_ne_zero_of_eigen v hv0 t (fun ℓ => ℓ * δ ℓ) u hrel hvU
  have haℓ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → qCoeff (⇑v) ℓ = t ℓ * a₁ := by
    intro ℓ hℓ hℓN
    have h := hrel ℓ hℓ hℓN 1
    have hnd : ¬ ℓ ∣ 1 := fun hd => hℓ.one_lt.ne' (Nat.dvd_one.1 hd)
    rw [mul_one, if_neg hnd, mul_zero, add_zero] at h
    exact h
  let w : CuspForm (Gamma1 N) 2 := a₁⁻¹ • v
  have hw : ∀ n, qCoeff (⇑w) n = a₁⁻¹ * qCoeff (⇑v) n := fun n => qCoeff_smul _ _ _
  have hw1 : qCoeff (⇑w) 1 = 1 := by rw [hw, ← ha₁, inv_mul_cancel₀ ha₁0]
  have hwℓ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → qCoeff (⇑w) ℓ = t ℓ := by
    intro ℓ hℓ hℓN
    rw [hw, haℓ ℓ hℓ hℓN, mul_comm, mul_assoc, mul_inv_cancel₀ ha₁0, mul_one]
  have hwU : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ N → qCoeff (⇑w) ℓ = u ℓ := by
    intro ℓ hℓ hℓN
    rw [hw, ← mul_one ℓ, hvU ℓ hℓ hℓN 1, mul_one, ← ha₁, mul_comm, mul_assoc, mul_inv_cancel₀ ha₁0,
      mul_one]
  have hwT : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ∀ n : ℕ,
      qCoeff (⇑w) (ℓ * n) + χv (ℓ : ZMod N) * (ℓ : ℂ) ^ ((2 : ℤ) - 1) *
          (if ℓ ∣ n then qCoeff (⇑w) (n / ℓ) else 0) =
        t ℓ * qCoeff (⇑w) n := by
    intro ℓ hℓ hℓN n
    have h := hrel ℓ hℓ hℓN n
    have hc : χv (ℓ : ZMod N) * (ℓ : ℂ) ^ ((2 : ℤ) - 1) = ℓ * δ ℓ := hχval ℓ hℓ hℓN
    rw [hc, hw (ℓ * n), hw n]
    split_ifs at h ⊢ with hd
    · rw [hw (n / ℓ)]
      linear_combination a₁⁻¹ * h
    · linear_combination a₁⁻¹ * h
  have hwE : CuspForm.IsEigenformWith χv w := by
    refine ⟨hw1, fun ℓ hℓ hℓN n => ?_, fun ℓ hℓ hℓN n => ?_, hasNebentypus_smul hχv _⟩
    · rw [hwℓ ℓ hℓ hℓN]
      exact hwT ℓ hℓ hℓN n
    · rw [hwU ℓ hℓ hℓN, hw, hw, hvU ℓ hℓ hℓN n]
      ring
  have hw0 : w ≠ 0 := ne_zero_of_qCoeff_one w hw1

  obtain ⟨M₁, _, ε₁, G₁, hM₁N, hG₁, hpk⟩ :=
    CuspForm.exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen N 2 χv w hw0 hwE.hasNebentypus t hwT

  have hSM : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S ∪ N.primeFactors → ¬ ℓ ∣ N ∧ ℓ ∉ S := by
    intro ℓ hℓ hℓS
    rw [Finset.mem_union, not_or] at hℓS
    refine ⟨fun hd => hℓS.2 ?_, hℓS.1⟩
    exact Nat.mem_primeFactors.2 ⟨hℓ, hd, NeZero.ne N⟩
  obtain ⟨hM₁M, hGG⟩ := hG₁.level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq hG (S ∪ N.primeFactors)
    (fun ℓ hℓ hℓS => by
      obtain ⟨hℓN, hℓS'⟩ := hSM ℓ hℓ hℓS
      rw [(hpk ℓ hℓ hℓN).1, ht ℓ hℓ hℓN hℓS'])
    (fun ℓ hℓ hℓS => by
      obtain ⟨hℓN, hℓS'⟩ := hSM ℓ hℓ hℓS
      rw [(hpk ℓ hℓ hℓN).2, hχvℓ ℓ hℓ hℓN, hδ ℓ hℓ hℓN hℓS'])

  have hε₁ : DirichletCharacter.changeLevel hM₁N ε₁ = χv := by
    refine dirichlet_ext (M := N) ∅ fun ℓ hℓ hℓN _ => ?_
    have hcop : Nat.Coprime ℓ N := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓN
    rw [← ZMod.coe_unitOfCoprime ℓ hcop, DirichletCharacter.changeLevel_eq_cast_of_dvd, ZMod.coe_unitOfCoprime,
      ZMod.cast_natCast hM₁N, (hpk ℓ hℓ hℓN).2]
  have hstab := hwE.dvd_and_qCoeff_eq_or_not_dvd_and_qCoeff_sq_sub_eq_zero_of_isPrimitiveForm_of_not_sq_dvd
    hG₁ hM₁N hε₁ (fun ℓ hℓ hℓN => by rw [(hpk ℓ hℓ hℓN).1, hwℓ ℓ hℓ hℓN]) q hq hqN hq2
  have hqM₁ : q ∣ M₁ := by rw [hM₁M]; exact hqM
  rcases hstab with ⟨-, hwq⟩ | ⟨hnd, -⟩
  · rw [← hwU q hq hqN, hwq, hGG]
  · exact absurd hqM₁ hnd

end Cusp

end OLDEIGEN

end

theorem solution
    {M : ℕ} [NeZero M] {N : ℕ} [NeZero N] (hMN : M ∣ N)
    {χ : DirichletCharacter ℂ M} {G : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hG : CuspForm.IsPrimitiveForm χ G)
    (S : Finset ℕ) (v : CuspForm (CongruenceSubgroup.Gamma1 N) 2) (hv0 : v ≠ 0)
    (t u δ : ℕ → ℂ)
    (hvT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), CuspForm.heckeTLinOne 2 hℓ hℓN v = t ℓ • v)
    (hvD : ∀ d : ℕ, Nat.Coprime d N → CuspForm.diamondLinOne N 2 d v = δ d • v)
    (hvU : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ N → ∀ n : ℕ,
      ModularFormClass.qCoeff v (ℓ * n) = u ℓ * ModularFormClass.qCoeff v n)
    (ht : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → t ℓ = ModularFormClass.qCoeff G ℓ)
    (hδ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → δ ℓ = χ (ℓ : ZMod M))
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ N) :
    u q = ModularFormClass.qCoeff G q :=
  OLDEIGEN.heckeU_eigenvalue_eq_qCoeff_of_common_eigenvector_of_dvd hMN hG S v hv0 t u δ hvT hvD hvU ht hδ hq hqM hq2

end S_CuspForm_IsPrimitiveForm_heckeU_eigenvalue_eq_qCoeff_of_common_eigenvector_of_dvd_level
end P2MW
export P2MW.S_CuspForm_IsPrimitiveForm_heckeU_eigenvalue_eq_qCoeff_of_common_eigenvector_of_dvd_level (solution)
