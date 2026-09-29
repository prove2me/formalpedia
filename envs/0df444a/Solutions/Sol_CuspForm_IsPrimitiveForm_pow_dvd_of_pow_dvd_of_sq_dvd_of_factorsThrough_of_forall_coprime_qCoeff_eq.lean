-- Prove2me | solution 1 for CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/850e78a0-b37c-5d0f-a661-a7991c5d7bdb

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_CuspForm_HasNebentypus_qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash
import Theorems.Thm_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd
import Theorems.Thm_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd
import Theorems.Thm_CuspForm_IsPrimitiveForm_qCoeff_eq_zero_of_dvd_div
import Theorems.Thm_CuspForm_exists_degeneracy_gamma1_hasNebentypus
import Theorems.Thm_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough
import Theorems.Thm_CuspForm_norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsPrimitiveForm_pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

namespace LiCaseOne

open CongruenceSubgroup ModularForm ModularFormClass Matrix.SpecialLinearGroup
p2m_open "UpperHalfPlane~I"
open scoped MatrixGroups ModularForm ComplexConjugate

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section QCoeff

variable {L : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (L : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ L).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem periodic (f : CuspForm (Γ₁ℝ L) k) : Function.Periodic (⇑f ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods L)

theorem bdd (f : CuspForm (Γ₁ℝ L) k) : IsBoundedAtImInfty (⇑f) := by
  haveI : Fact (IsCusp OnePoint.infty (Γ₁ℝ L)) :=
    ⟨(Γ₁ℝ L).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods L)⟩
  exact ModularFormClass.bdd_at_infty f

theorem analytic (f : CuspForm (Γ₁ℝ L) k) : AnalyticAt ℂ (cuspFunction 1 (⇑f)) 0 :=
  analyticAt_cuspFunction_zero one_pos (periodic f) f.holo' (bdd f)

theorem qCoeff_zero_fun (n : ℕ) : qCoeff (0 : ℍ → ℂ) n = 0 := by
  rw [qCoeff, UpperHalfPlane.qExpansion_zero, map_zero]

theorem qCoeff_zero (n : ℕ) : qCoeff (⇑(0 : CuspForm (Γ₁ℝ L) k)) n = 0 := by
  rw [CuspForm.coe_zero, qCoeff_zero_fun]

theorem qCoeff_smul (c : ℂ) (f : CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(c • f)) n = c * qCoeff (⇑f) n := by
  rw [qCoeff, qCoeff, CuspForm.IsGLPos.coe_smul, qExpansion_smul (analytic f), map_smul,
    smul_eq_mul]

theorem qCoeff_sub (f g : CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(f - g)) n = qCoeff (⇑f) n - qCoeff (⇑g) n := by
  rw [qCoeff, qCoeff, qCoeff, CuspForm.coe_sub, qExpansion_sub (analytic f) (analytic g), map_sub]

theorem qCoeff_add (f g : CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(f + g)) n = qCoeff (⇑f) n + qCoeff (⇑g) n := by
  rw [qCoeff, qCoeff, qCoeff, CuspForm.coe_add, qExpansion_add (analytic f) (analytic g), map_add]

end QCoeff

section Neb

variable {M : ℕ} {k : ℤ}

theorem hasNebentypus_zero (ε : DirichletCharacter ℂ M) :
    CuspForm.HasNebentypus ε (0 : CuspForm (Γ₁ℝ M) k) := by
  intro γ _ τ; simp

theorem hasNebentypus_add {ε : DirichletCharacter ℂ M} {f g : CuspForm (Γ₁ℝ M) k}
    (hf : CuspForm.HasNebentypus ε f) (hg : CuspForm.HasNebentypus ε g) :
    CuspForm.HasNebentypus ε (f + g) := by
  intro γ hγ τ
  rw [CuspForm.add_apply, CuspForm.add_apply, hf γ hγ τ, hg γ hγ τ]; ring

theorem hasNebentypus_sub {ε : DirichletCharacter ℂ M} {f g : CuspForm (Γ₁ℝ M) k}
    (hf : CuspForm.HasNebentypus ε f) (hg : CuspForm.HasNebentypus ε g) :
    CuspForm.HasNebentypus ε (f - g) := by
  intro γ hγ τ
  rw [CuspForm.sub_apply, CuspForm.sub_apply, hf γ hγ τ, hg γ hγ τ]; ring

theorem hasNebentypus_smul {ε : DirichletCharacter ℂ M} {f : CuspForm (Γ₁ℝ M) k}
    (hf : CuspForm.HasNebentypus ε f) (c : ℂ) : CuspForm.HasNebentypus ε (c • f) := by
  intro γ hγ τ
  rw [CuspForm.IsGLPos.smul_apply, CuspForm.IsGLPos.smul_apply, smul_eq_mul, smul_eq_mul,
    hf γ hγ τ]; ring

end Neb

section Beta

variable {k : ℤ}

theorem coe_beta (m : ℤ) :
    ((ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -m, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.coe_T_zpow, ModularGroup.coe_S, Matrix.SpecialLinearGroup.coe_inv,
    ModularGroup.coe_S]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem beta_apply (m : ℤ) (i j : Fin 2) :
    (ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) i j = !![1, 0; -m, 1] i j := by
  rw [← coe_beta]

theorem beta_add (m m' : ℤ) :
    (ModularGroup.S * ModularGroup.T ^ (m + m') * ModularGroup.S⁻¹ : SL(2, ℤ))
      = (ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹)
        * (ModularGroup.S * ModularGroup.T ^ m' * ModularGroup.S⁻¹) := by
  rw [_root_.zpow_add]; group

theorem beta_mem_Gamma1 (L : ℕ) (r : ℤ) :
    (ModularGroup.S * ModularGroup.T ^ ((L : ℤ) * r) * ModularGroup.S⁻¹ : SL(2, ℤ)) ∈ Gamma1 L := by
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [beta_apply]

theorem coe_beta_smul (m : ℤ) (τ : ℍ) :
    (((ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) • τ : ℍ) : ℂ)
      = (τ : ℂ) / (1 - (m : ℂ) * (τ : ℂ)) := by
  rw [UpperHalfPlane.specialLinearGroup_apply]
  simp only [beta_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_one, Complex.ofReal_one, one_mul,
    Int.cast_zero, Complex.ofReal_zero, add_zero, Int.cast_neg, Complex.ofReal_neg,
    Complex.ofReal_intCast]
  ring_nf

theorem slash_beta_apply (k : ℤ) (G : ℍ → ℂ) (m : ℤ) (τ : ℍ) :
    (G ∣[k] (ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
      = G ((ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) • τ)
          * (1 - (m : ℂ) * (τ : ℂ)) ^ (-k) := by
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_apply, beta_apply, beta_apply]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.cast_neg, Int.cast_one]
  ring_nf

theorem one_sub_ne_zero (m : ℤ) (τ : ℍ) : (1 - (m : ℂ) * (τ : ℂ)) ≠ 0 := by
  have h := denom_ne_zero (ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) τ
  rw [ModularGroup.denom_apply, beta_apply, beta_apply] at h
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.cast_neg, Int.cast_one] at h
  intro h0; apply h; linear_combination h0

theorem slash_beta_add_level {P : ℕ} (F : CuspForm (Γ₁ℝ P) k) (m r : ℤ) :
    (⇑F : ℍ → ℂ) ∣[k] (ModularGroup.S * ModularGroup.T ^ (m + (P : ℤ) * r) * ModularGroup.S⁻¹ :
        SL(2, ℤ))
      = (⇑F : ℍ → ℂ) ∣[k] (ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) := by
  rw [add_comm, beta_add]
  show (⇑F : ℍ → ℂ) ∣[k] (mapGL ℝ ((ModularGroup.S * ModularGroup.T ^ ((P : ℤ) * r) *
      ModularGroup.S⁻¹) * (ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹)) :
        GL (Fin 2) ℝ)
    = (⇑F : ℍ → ℂ) ∣[k] (mapGL ℝ (ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹) :
        GL (Fin 2) ℝ)
  rw [map_mul, SlashAction.slash_mul]
  congr 1
  exact SlashInvariantFormClass.slash_action_eq F _
    (Subgroup.mem_map.mpr ⟨_, beta_mem_Gamma1 P r, rfl⟩)

theorem slash_beta_level {P : ℕ} (F : CuspForm (Γ₁ℝ P) k) (r : ℤ) :
    (⇑F : ℍ → ℂ) ∣[k] (ModularGroup.S * ModularGroup.T ^ ((P : ℤ) * r) * ModularGroup.S⁻¹ :
        SL(2, ℤ)) = ⇑F := by
  show (⇑F : ℍ → ℂ) ∣[k] (mapGL ℝ (ModularGroup.S * ModularGroup.T ^ ((P : ℤ) * r) *
      ModularGroup.S⁻¹) : GL (Fin 2) ℝ) = ⇑F
  exact SlashInvariantFormClass.slash_action_eq F _
    (Subgroup.mem_map.mpr ⟨_, beta_mem_Gamma1 P r, rfl⟩)

end Beta

theorem sum_range_reindex {α : Type*} [AddCommMonoid α] {q : ℕ} (hq : q.Prime) (f : ℕ → α)
    (hper : ∀ y r : ℕ, f (y + q * r) = f y) {u : ℕ} (hu : ¬ q ∣ u) :
    ∑ j ∈ Finset.range q, f (j * u) = ∑ x ∈ Finset.range q, f x := by
  have hcop : Nat.Coprime u q := (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hu)
  obtain ⟨v, -, hv⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hq.one_lt
  have hqpos : 0 < q := hq.pos
  have hmod : ∀ j : ℕ, f (j * u) = f (j * u % q) := by
    intro j
    conv_lhs => rw [← Nat.mod_add_div (j * u) q]
    exact hper _ _
  simp_rw [hmod]
  refine Finset.sum_nbij' (fun j => j * u % q) (fun x => x * v % q) (fun j _ => ?_) (fun x _ => ?_)
    (fun j hj => ?_) (fun x hx => ?_) (fun j _ => rfl)
  · exact Finset.mem_range.mpr (Nat.mod_lt _ hqpos)
  · exact Finset.mem_range.mpr (Nat.mod_lt _ hqpos)
  · have hj' : j < q := Finset.mem_range.mp hj
    calc j * u % q * v % q = j * (u * v) % q := by
            rw [Nat.mul_mod (j * u % q) v, Nat.mod_mod, ← Nat.mul_mod, mul_assoc]
      _ = j % q := by rw [Nat.mul_mod, hv, mul_one, Nat.mod_mod]
      _ = j := Nat.mod_eq_of_lt hj'
  · have hx' : x < q := Finset.mem_range.mp hx
    calc x * v % q * u % q = x * (u * v) % q := by
            rw [Nat.mul_mod (x * v % q) u, Nat.mod_mod, ← Nat.mul_mod, mul_assoc, mul_comm v u]
      _ = x % q := by rw [Nat.mul_mod, hv, mul_one, Nat.mod_mod]
      _ = x := Nat.mod_eq_of_lt hx'

theorem changeLevel_apply_natCast {M M' : ℕ} [NeZero M] (h : M' ∣ M)
    (χ : DirichletCharacter ℂ M') {p : ℕ} (hp : Nat.Coprime p M) :
    DirichletCharacter.changeLevel h χ (p : ZMod M) = χ (p : ZMod M') := by
  have hu : IsUnit (p : ZMod M) := (ZMod.isUnit_iff_coprime p M).mpr hp
  rw [← hu.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd χ h, hu.unit_spec,
    ZMod.cast_natCast h]

theorem changeLevel_eq_of_forall_coprime {M₁ M₂ N : ℕ} [NeZero N] (h1 : M₁ ∣ N) (h2 : M₂ ∣ N)
    (ε₁ : DirichletCharacter ℂ M₁) (ε₂ : DirichletCharacter ℂ M₂)
    (hε : ∀ n : ℕ, Nat.Coprime n M₁ → Nat.Coprime n M₂ → ε₁ (n : ZMod M₁) = ε₂ (n : ZMod M₂)) :
    DirichletCharacter.changeLevel h1 ε₁ = DirichletCharacter.changeLevel h2 ε₂ := by
  apply MulChar.ext
  intro a
  have hcop : Nat.Coprime (a : ZMod N).val N := ZMod.val_coe_unit_coprime a
  have han : ((((a : ZMod N).val : ℕ)) : ZMod N) = a := ZMod.natCast_zmod_val _
  rw [← han, changeLevel_apply_natCast h1 ε₁ hcop, changeLevel_apply_natCast h2 ε₂ hcop]
  exact hε _ (hcop.coprime_dvd_right h1) (hcop.coprime_dvd_right h2)

section Main

variable {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂] {k : ℤ}
    {ε₁ : DirichletCharacter ℂ M₁} {ε₂ : DirichletCharacter ℂ M₂}
    {g₁ : CuspForm (Γ₁ℝ M₁) k} {g₂ : CuspForm (Γ₁ℝ M₂) k}

theorem coe_heckeDiagMatrix_beta_smul {d : ℕ} (hd : d ≠ 0) (m : ℤ) (τ : ℍ) :
    ((heckeDiagMatrix d •
        ((ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) • τ) : ℍ) : ℂ)
      = (d : ℂ) * (τ : ℂ) / (1 - (m : ℂ) * (τ : ℂ)) := by
  rw [coe_heckeDiagMatrix_smul hd, coe_beta_smul]; ring

theorem heckeMatrix_smul_heckeDiagMatrix_smul {q : ℕ} (hq : q ≠ 0) (τ : ℍ) :
    heckeMatrix q 0 • (heckeDiagMatrix q • τ) = τ := by
  apply UpperHalfPlane.ext
  rw [coe_heckeMatrix_smul hq, coe_heckeDiagMatrix_smul hq]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  push_cast; field_simp; ring

theorem heckeDiagMatrix_one_smul (τ : ℍ) : heckeDiagMatrix 1 • τ = τ := by
  apply UpperHalfPlane.ext
  rw [coe_heckeDiagMatrix_smul one_ne_zero]
  push_cast; ring

theorem slash_beta_comp_apply (F : ℍ → ℂ) {d : ℕ} (hd : d ≠ 0) (m m' : ℤ)
    (hmm' : (m' : ℂ) * (d : ℂ) = (m : ℂ)) (τ : ℍ) :
    ((fun σ : ℍ => F (heckeDiagMatrix d • σ)) ∣[k]
        (ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
      = (F ∣[k] (ModularGroup.S * ModularGroup.T ^ m' * ModularGroup.S⁻¹ : SL(2, ℤ)))
          (heckeDiagMatrix d • τ) := by
  rw [slash_beta_apply, slash_beta_apply, coe_heckeDiagMatrix_smul hd]
  have hpt : heckeDiagMatrix d •
      ((ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) • τ)
        = (ModularGroup.S * ModularGroup.T ^ m' * ModularGroup.S⁻¹ : SL(2, ℤ)) •
            (heckeDiagMatrix d • τ) := by
    apply UpperHalfPlane.ext
    rw [coe_heckeDiagMatrix_beta_smul hd, coe_beta_smul, coe_heckeDiagMatrix_smul hd]
    have h1 := one_sub_ne_zero m τ
    have h2 : (1 - (m' : ℂ) * ((d : ℂ) * (τ : ℂ))) ≠ 0 := by
      rw [← mul_assoc, hmm']; exact h1
    field_simp
    rw [← hmm']; ring
  rw [hpt]
  congr 1
  rw [← mul_assoc, hmm']

theorem main
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂)
    (ha : ∀ n : ℕ, Nat.Coprime n M₁ → Nat.Coprime n M₂ → qCoeff g₁ n = qCoeff g₂ n)
    (hε : ∀ n : ℕ, Nat.Coprime n M₁ → Nat.Coprime n M₂ → ε₁ (n : ZMod M₁) = ε₂ (n : ZMod M₂))
    {q : ℕ} (hq : q.Prime) (hqM : q ^ 2 ∣ M₁) (hε₁ : ε₁.FactorsThrough (M₁ / q))
    (j : ℕ) (hj : q ^ j ∣ M₁) : q ^ j ∣ M₂ := by
  classical
  by_contra hjM₂

  have hM₁0 : M₁ ≠ 0 := NeZero.ne M₁
  have hM₂0 : M₂ ≠ 0 := NeZero.ne M₂
  have hq0 : q ≠ 0 := hq.ne_zero
  have hq1 : 1 < q := hq.one_lt
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hqM₁ : q ∣ M₁ := (dvd_pow_self q two_ne_zero).trans hqM
  have hqM₁q : q ∣ M₁ / q := Nat.dvd_div_of_mul_dvd (by rw [← pow_two]; exact hqM)

  set m : ℕ := M₁.factorization q with hmdef
  set e : ℕ := M₂.factorization q with hedef
  set A : ℕ := M₁ / q ^ m with hAdef
  set B : ℕ := M₂ / q ^ e with hBdef
  have hM₁A : q ^ m * A = M₁ := Nat.ordProj_mul_ordCompl_eq_self M₁ q
  have hM₂B : q ^ e * B = M₂ := Nat.ordProj_mul_ordCompl_eq_self M₂ q
  have hqA : Nat.Coprime q A := Nat.coprime_ordCompl hq hM₁0
  have hqB : Nat.Coprime q B := Nat.coprime_ordCompl hq hM₂0
  have hej : e < j := by
    by_contra hle
    push Not at hle
    exact hjM₂ ((hq.pow_dvd_iff_le_factorization hM₂0).mpr hle)
  have hjm : j ≤ m := (hq.pow_dvd_iff_le_factorization hM₁0).mp hj
  have hem : e + 1 ≤ m := by omega

  set L : ℕ := Nat.lcm M₁ M₂ with hLdef
  have hL0 : L ≠ 0 := Nat.lcm_ne_zero hM₁0 hM₂0
  have hM₁L : M₁ ∣ L := Nat.dvd_lcm_left M₁ M₂
  have hM₂L : M₂ ∣ L := Nat.dvd_lcm_right M₁ M₂
  have hqL : q ∣ L := hqM₁.trans hM₁L
  set t : ℕ := L / q with htdef
  have hLqt : q * t = L := Nat.mul_div_cancel' hqL
  have ht0 : t ≠ 0 := by intro h; apply hL0; rw [← hLqt, h, mul_zero]
  haveI : NeZero t := ⟨ht0⟩
  haveI : NeZero (q * t) := ⟨by rw [hLqt]; exact hL0⟩
  have hqt : q ∣ t := by
    apply Nat.dvd_div_of_mul_dvd
    rw [← pow_two]; exact hqM.trans hM₁L
  have hM₁N : M₁ ∣ q * t := by rw [hLqt]; exact hM₁L
  have hM₂N : M₂ ∣ q * t := by rw [hLqt]; exact hM₂L

  have hqM₂N : q * M₂ ∣ q * t := by
    rw [hLqt, ← hM₂B, ← mul_assoc, ← pow_succ']
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_left _ hqB) ?_ ?_
    · exact ((pow_dvd_pow q (by omega : e + 1 ≤ j)).trans hj).trans hM₁L
    · exact (Dvd.intro_left _ hM₂B).trans hM₂L
  have hM₂t : M₂ ∣ t := Nat.dvd_of_mul_dvd_mul_left hq.pos hqM₂N

  have hLdvd : L ∣ q ^ m * (A * B) := by
    refine Nat.lcm_dvd ?_ ?_
    · rw [← hM₁A, ← mul_assoc]; exact Dvd.intro _ rfl
    · rw [← hM₂B]
      calc q ^ e * B ∣ q ^ m * B := mul_dvd_mul_right (pow_dvd_pow q (by omega)) B
        _ ∣ q ^ m * (A * B) := mul_dvd_mul_left _ (Dvd.intro_left A rfl)
  have hnot : ¬ q ^ (m + 1) ∣ q * t := by
    rw [hLqt]
    intro h
    have h' : q ^ m * q ∣ q ^ m * (A * B) := by rw [← pow_succ]; exact h.trans hLdvd
    have h'' : q ∣ A * B := Nat.dvd_of_mul_dvd_mul_left (pow_pos hq.pos m) h'
    rcases (Nat.Prime.dvd_mul hq).mp h'' with hA' | hB'
    · exact (Nat.Prime.coprime_iff_not_dvd hq).mp hqA hA'
    · exact (Nat.Prime.coprime_iff_not_dvd hq).mp hqB hB'

  set P : ℕ := M₁ * M₂ with hPdef
  have hP0 : P ≠ 0 := mul_ne_zero hM₁0 hM₂0
  set K : ℕ := P / q ^ P.factorization q with hKdef
  have hK0 : K ≠ 0 := (Nat.ordCompl_pos q hP0).ne'
  have hqK : Nat.Coprime q K := Nat.coprime_ordCompl hq hP0
  have hPK : q ^ P.factorization q * K = P := Nat.ordProj_mul_ordCompl_eq_self P q
  have hKcop : ∀ n : ℕ, Nat.Coprime n K → ¬ q ∣ n → Nat.Coprime n M₁ ∧ Nat.Coprime n M₂ := by
    intro n hnK hqn
    have hnq : Nat.Coprime n q := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqn)
    have hnP : Nat.Coprime n P := by
      rw [← hPK]; exact Nat.Coprime.mul_right (hnq.pow_right _) hnK
    exact ⟨hnP.coprime_dvd_right (Dvd.intro _ rfl), hnP.coprime_dvd_right (Dvd.intro_left _ rfl)⟩

  set εt : DirichletCharacter ℂ t := DirichletCharacter.changeLevel hM₂t ε₂ with hεtdef
  set εN : DirichletCharacter ℂ (q * t) :=
    DirichletCharacter.changeLevel (dvd_mul_left t q) εt with hεNdef
  have hεN₂ : DirichletCharacter.changeLevel hM₂N ε₂ = εN := by
    rw [hεNdef, hεtdef, ← DirichletCharacter.changeLevel_trans]
  have hεN₁ : DirichletCharacter.changeLevel hM₁N ε₁ = εN := by
    rw [← hεN₂]; exact changeLevel_eq_of_forall_coprime hM₁N hM₂N ε₁ ε₂ hε

  have haq₁ : qCoeff g₁ q = 0 := by
    obtain ⟨hdvd, χ, hχ⟩ := hε₁
    have h₁' : CuspForm.IsPrimitiveForm
        (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hqM₁) χ) g₁ := by
      rw [hχ] at h₁; exact h₁
    exact CuspForm.IsPrimitiveForm.qCoeff_eq_zero_of_dvd_div M₁ k hq hqM₁ hqM₁q χ g₁ h₁'

  set b : ℂ := qCoeff g₂ q with hbdef
  set c₂ : ℂ := if q ∣ M₂ then 0 else ε₂ (q : ZMod M₂) * (q : ℂ) ^ (k - 1) with hc₂def
  have hrel₂ : ∀ n : ℕ, qCoeff g₂ (q * n)
      = b * qCoeff g₂ n - c₂ * (if q ∣ n then qCoeff g₂ (n / q) else 0) := by
    intro n
    by_cases hqM₂ : q ∣ M₂
    · rw [hc₂def, if_pos hqM₂, zero_mul, sub_zero]
      exact h₂.isEigenformWith.hecke_of_dvd hq hqM₂ n
    · rw [hc₂def, if_neg hqM₂]
      linear_combination h₂.isEigenformWith.hecke_of_not_dvd hq hqM₂ n
  have hrel₁ : ∀ n : ℕ, qCoeff g₁ (q * n) = 0 := fun n => by
    rw [h₁.isEigenformWith.hecke_of_dvd hq hqM₁ n, haq₁, zero_mul]

  obtain ⟨G₁, hG₁fun, hG₁coef, hG₁neb⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
    (k := k) (N := q * t) (d := 1) (by rw [mul_one]; exact hM₁N) g₁
  obtain ⟨G₂, hG₂fun, hG₂coef, hG₂neb⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
    (k := k) (N := q * t) (d := 1) (by rw [mul_one]; exact hM₂N) g₂
  obtain ⟨G₂t, hG₂tfun, hG₂tcoef, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
    (k := k) (N := t) (d := 1) (by rw [mul_one]; exact hM₂t) g₂
  obtain ⟨X, hXfun, hXcoef, hXneb⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
    (k := k) (N := q * t) (d := q) (by rw [mul_comm]; exact hqM₂N) g₂
  have hG₁val : ∀ τ, G₁ τ = g₁ τ := fun τ => by rw [hG₁fun, heckeDiagMatrix_one_smul]
  have hG₂val : ∀ τ, G₂ τ = g₂ τ := fun τ => by rw [hG₂fun, heckeDiagMatrix_one_smul]
  have hG₂tval : ∀ τ, G₂t τ = g₂ τ := fun τ => by rw [hG₂tfun, heckeDiagMatrix_one_smul]
  have hG₁c : ∀ n, qCoeff G₁ n = qCoeff g₁ n := fun n => by
    rw [hG₁coef, if_pos (one_dvd n), Nat.div_one]
  have hG₂c : ∀ n, qCoeff G₂ n = qCoeff g₂ n := fun n => by
    rw [hG₂coef, if_pos (one_dvd n), Nat.div_one]
  have hG₂tc : ∀ n, qCoeff G₂t n = qCoeff g₂ n := fun n => by
    rw [hG₂tcoef, if_pos (one_dvd n), Nat.div_one]

  obtain ⟨Y, hYcoef, hYfun, hYneb⟩ : ∃ Y : CuspForm (Γ₁ℝ (q * t)) k,
      (∀ n : ℕ, qCoeff Y n = c₂ * (if q ^ 2 ∣ n then qCoeff g₂ (n / q ^ 2) else 0)) ∧
      (∀ τ : ℍ, Y τ = c₂ * g₂ (heckeDiagMatrix (q ^ 2) • τ)) ∧
      CuspForm.HasNebentypus εN Y := by
    by_cases hqM₂ : q ∣ M₂
    · refine ⟨0, fun n => ?_, fun τ => ?_, hasNebentypus_zero εN⟩
      · rw [qCoeff_zero, hc₂def, if_pos hqM₂, zero_mul]
      · rw [CuspForm.zero_apply, hc₂def, if_pos hqM₂, zero_mul]
    · have hq2M₂N : M₂ * q ^ 2 ∣ q * t := by
        rw [mul_comm]
        refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ hM₂N
        · exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqM₂)
        · rw [hLqt]; exact hqM.trans hM₁L
      obtain ⟨X2, hX2fun, hX2coef, hX2neb⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
        (k := k) (N := q * t) (d := q ^ 2) hq2M₂N g₂
      refine ⟨c₂ • X2, fun n => ?_, fun τ => ?_, ?_⟩
      · rw [qCoeff_smul, hX2coef]
      · rw [CuspForm.IsGLPos.smul_apply, smul_eq_mul, hX2fun]
      · have := hasNebentypus_smul (hX2neb ε₂ h₂.isEigenformWith.hasNebentypus) c₂
        rwa [show DirichletCharacter.changeLevel (dvd_of_mul_right_dvd hq2M₂N) ε₂ = εN from hεN₂]
          at this

  set E : CuspForm (Γ₁ℝ (q * t)) k := G₁ - G₂ + b • X - Y with hEdef
  have hEneb : CuspForm.HasNebentypus εN E := by
    have h1 : CuspForm.HasNebentypus εN G₁ := by
      have := hG₁neb ε₁ h₁.isEigenformWith.hasNebentypus
      rwa [show DirichletCharacter.changeLevel _ ε₁ = εN from hεN₁] at this
    have h2 : CuspForm.HasNebentypus εN G₂ := by
      have := hG₂neb ε₂ h₂.isEigenformWith.hasNebentypus
      rwa [show DirichletCharacter.changeLevel _ ε₂ = εN from hεN₂] at this
    have h3 : CuspForm.HasNebentypus εN X := by
      have := hXneb ε₂ h₂.isEigenformWith.hasNebentypus
      rwa [show DirichletCharacter.changeLevel _ ε₂ = εN from hεN₂] at this
    exact hasNebentypus_sub (hasNebentypus_add (hasNebentypus_sub h1 h2) (hasNebentypus_smul h3 b)) hYneb
  have hEcoef : ∀ n : ℕ, qCoeff E n = if q ∣ n then 0 else qCoeff g₁ n - qCoeff g₂ n := by
    intro n
    rw [hEdef, qCoeff_sub, qCoeff_add, qCoeff_sub, qCoeff_smul, hG₁c, hG₂c, hXcoef, hYcoef]
    by_cases hqn : q ∣ n
    · obtain ⟨n₁, rfl⟩ := hqn
      rw [if_pos (Dvd.intro n₁ rfl), if_pos (Dvd.intro n₁ rfl), hrel₁, hrel₂,
        Nat.mul_div_cancel_left n₁ hq.pos]
      have hiff : (q ^ 2 ∣ q * n₁ ↔ q ∣ n₁) := by
        rw [pow_two]; exact Nat.mul_dvd_mul_iff_left hq.pos
      by_cases hqn₁ : q ∣ n₁
      · rw [if_pos hqn₁, if_pos (hiff.mpr hqn₁)]
        obtain ⟨n₂, rfl⟩ := hqn₁
        rw [Nat.mul_div_cancel_left n₂ hq.pos, pow_two, ← mul_assoc,
          Nat.mul_div_cancel_left n₂ (mul_pos hq.pos hq.pos)]
        ring
      · rw [if_neg hqn₁, if_neg (fun h => hqn₁ (hiff.mp h))]
        ring
    · rw [if_neg hqn, if_neg hqn, if_neg (fun h => hqn ((dvd_pow_self q two_ne_zero).trans h))]
      ring
  have hEzero : ∀ n : ℕ, Nat.Coprime n K → qCoeff E n = 0 := by
    intro n hn
    rw [hEcoef]
    by_cases hqn : q ∣ n
    · rw [if_pos hqn]
    · rw [if_neg hqn]
      obtain ⟨hn₁, hn₂⟩ := hKcop n hn hqn
      rw [ha n hn₁ hn₂, sub_self]

  have hM₁qt : M₁ / q ∣ t := by
    have : M₁ / q * q ∣ t * q := by
      rw [Nat.div_mul_cancel hqM₁, mul_comm t q]; exact hM₁N
    exact Nat.dvd_of_mul_dvd_mul_right hq.pos this
  obtain ⟨u₁, hu₁⟩ := hM₁qt
  set D₁ : ℕ := M₁ / q with hD₁def
  have hD₁q : D₁ * q = M₁ := Nat.div_mul_cancel hqM₁
  have hqu₁ : ¬ q ∣ u₁ := by
    intro h
    apply hnot
    have hM₁t : M₁ ∣ t := by
      obtain ⟨w, hw⟩ := h
      exact ⟨w, by rw [hu₁, hw, ← mul_assoc, Nat.div_mul_cancel hqM₁]⟩
    calc q ^ (m + 1) = q * q ^ m := by ring
      _ ∣ q * M₁ := mul_dvd_mul_left q (Nat.ordProj_dvd M₁ q)
      _ ∣ q * t := mul_dvd_mul_left q hM₁t
  have hTa : ∀ τ : ℍ, ∑ i ∈ Finset.range q,
      ((⇑G₁ : ℍ → ℂ) ∣[k]
        (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ = 0 := by
    intro τ
    have hG₁eq : (⇑G₁ : ℍ → ℂ) = ⇑g₁ := funext hG₁val
    rw [hG₁eq]
    have hper : ∀ y r : ℕ,
        ((⇑g₁ : ℍ → ℂ) ∣[k] (ModularGroup.S * ModularGroup.T ^ (((y + q * r : ℕ) : ℤ) * (D₁ : ℕ)) *
          ModularGroup.S⁻¹ : SL(2, ℤ))) τ
        = ((⇑g₁ : ℍ → ℂ) ∣[k] (ModularGroup.S * ModularGroup.T ^ ((y : ℤ) * (D₁ : ℕ)) *
          ModularGroup.S⁻¹ : SL(2, ℤ))) τ := by
      intro y r
      have : (((y + q * r : ℕ) : ℤ) * (D₁ : ℕ) : ℤ) = (y : ℤ) * (D₁ : ℕ) + (M₁ : ℤ) * r := by
        rw [← hD₁q]; push_cast; ring
      rw [this, slash_beta_add_level]
    have hstep : ∀ i : ℕ, ((i : ℤ) * t : ℤ) = ((i * u₁ : ℕ) : ℤ) * (D₁ : ℕ) := by
      intro i; rw [hu₁]; push_cast; ring
    simp_rw [hstep]
    rw [sum_range_reindex hq (fun x => ((⇑g₁ : ℍ → ℂ) ∣[k] (ModularGroup.S *
      ModularGroup.T ^ ((x : ℤ) * (D₁ : ℕ)) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ) hper hqu₁,
      CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd M₁ k ε₁ g₁ h₁ hq
        hqM₁ τ, haq₁, map_zero, mul_zero, zero_mul]

  have hTb : ∀ τ : ℍ, ∑ i ∈ Finset.range q,
      ((⇑G₂ : ℍ → ℂ) ∣[k]
        (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
        = (q : ℂ) * G₂t τ := by
    intro τ
    have hG₂eq : (⇑G₂ : ℍ → ℂ) = ⇑g₂ := funext hG₂val
    obtain ⟨w, hw⟩ := hM₂t
    have hterm : ∀ i : ℕ, (⇑g₂ : ℍ → ℂ) ∣[k]
        (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ)) = ⇑g₂ := by
      intro i
      have : ((i : ℤ) * t : ℤ) = (M₂ : ℤ) * (i * w) := by rw [hw]; push_cast; ring
      rw [this, slash_beta_level]
    rw [hG₂eq]
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hG₂tval]

  obtain ⟨ΦX, hΦXfun, hΦX1⟩ : ∃ ΦX : CuspForm (Γ₁ℝ t) k,
      (∀ τ : ℍ, ΦX τ = ∑ i ∈ Finset.range q, ((⇑X : ℍ → ℂ) ∣[k]
        (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ) ∧
      (qCoeff ΦX 1 = 0 ∨ (qCoeff ΦX 1 = (q : ℂ) ^ (1 - k) * conj b ∧ q ∣ M₂)) := by
    by_cases hA : M₂ * q ∣ t
    ·
      obtain ⟨Xt, hXtfun, hXtcoef, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
        (k := k) (N := t) (d := q) hA g₂
      have hXeq : (⇑X : ℍ → ℂ) = ⇑Xt := funext fun τ => by rw [hXfun, hXtfun]
      obtain ⟨w, hw⟩ := hA
      refine ⟨(q : ℂ) • Xt, fun τ => ?_, Or.inl ?_⟩
      · rw [hXeq]
        have hterm : ∀ i : ℕ, (⇑Xt : ℍ → ℂ) ∣[k]
            (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))
              = ⇑Xt := by
          intro i
          have : ((i : ℤ) * t : ℤ) = (t : ℤ) * i := by ring
          rw [this, slash_beta_level]
        simp_rw [hterm]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, CuspForm.IsGLPos.smul_apply,
          smul_eq_mul]
      · rw [qCoeff_smul, hXtcoef, if_neg (fun h => hq1.ne' (Nat.dvd_one.mp h)), mul_zero]
    ·
      obtain ⟨u, hu⟩ := hM₂t
      have hqu : ¬ q ∣ u := by
        rintro ⟨w, hw⟩; apply hA; exact ⟨w, by rw [hu, hw]; ring⟩
      have hqM₂ : q ∣ M₂ := by
        rcases (Nat.Prime.dvd_mul hq).mp (hu ▸ hqt) with h | h
        · exact h
        · exact (hqu h).elim
      refine ⟨((q : ℂ) ^ (1 - k) * conj b) • G₂t, fun τ => ?_, Or.inr ⟨?_, hqM₂⟩⟩
      · rw [CuspForm.IsGLPos.smul_apply, smul_eq_mul, hG₂tval]
        have hXeq : (⇑X : ℍ → ℂ) = fun σ => g₂ (heckeDiagMatrix q • σ) := funext hXfun
        rw [hXeq]

        set D₂ : ℕ := M₂ / q with hD₂def
        have hD₂q : D₂ * q = M₂ := Nat.div_mul_cancel hqM₂
        have htD : t = q * (u * D₂) := by
          rw [hu, ← hD₂q]; ring
        have hterm : ∀ i : ℕ,
            ((fun σ : ℍ => g₂ (heckeDiagMatrix q • σ)) ∣[k]
              (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
            = ((⇑g₂ : ℍ → ℂ) ∣[k] (ModularGroup.S *
                ModularGroup.T ^ (((i * u : ℕ) : ℤ) * (D₂ : ℕ)) * ModularGroup.S⁻¹ :
                  SL(2, ℤ))) (heckeDiagMatrix q • τ) := by
          intro i
          refine slash_beta_comp_apply (k := k) (⇑g₂) hq0 _ _ ?_ τ
          rw [htD]; push_cast; ring
        simp_rw [hterm]
        have hper : ∀ y r : ℕ,
            ((⇑g₂ : ℍ → ℂ) ∣[k] (ModularGroup.S *
              ModularGroup.T ^ (((y + q * r : ℕ) : ℤ) * (D₂ : ℕ)) * ModularGroup.S⁻¹ :
                SL(2, ℤ))) (heckeDiagMatrix q • τ)
            = ((⇑g₂ : ℍ → ℂ) ∣[k] (ModularGroup.S * ModularGroup.T ^ ((y : ℤ) * (D₂ : ℕ)) *
              ModularGroup.S⁻¹ : SL(2, ℤ))) (heckeDiagMatrix q • τ) := by
          intro y r
          have : (((y + q * r : ℕ) : ℤ) * (D₂ : ℕ) : ℤ)
              = (y : ℤ) * (D₂ : ℕ) + (M₂ : ℤ) * r := by
            rw [← hD₂q]; push_cast; ring
          rw [this, slash_beta_add_level]
        rw [sum_range_reindex hq (fun x => ((⇑g₂ : ℍ → ℂ) ∣[k] (ModularGroup.S *
          ModularGroup.T ^ ((x : ℤ) * (D₂ : ℕ)) * ModularGroup.S⁻¹ : SL(2, ℤ)))
            (heckeDiagMatrix q • τ)) hper hqu,
          CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd M₂ k ε₂ g₂ h₂
            hq hqM₂, heckeMatrix_smul_heckeDiagMatrix_smul hq0]
      · rw [qCoeff_smul, hG₂tc, h₂.isEigenformWith.qCoeff_one, mul_one]

  obtain ⟨ΦY, hΦYfun, hΦY1⟩ : ∃ ΦY : CuspForm (Γ₁ℝ t) k,
      (∀ τ : ℍ, ΦY τ = ∑ i ∈ Finset.range q, ((⇑Y : ℍ → ℂ) ∣[k]
        (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ) ∧
      (qCoeff ΦY 1 = 0 ∨ (qCoeff ΦY 1 = -(q : ℂ)⁻¹ ∧ ¬ q ∣ M₂)) := by
    by_cases hqM₂ : q ∣ M₂
    · refine ⟨0, fun τ => ?_, Or.inl (qCoeff_zero 1)⟩
      have hY0 : (⇑Y : ℍ → ℂ) = 0 := funext fun τ => by
        rw [hYfun, hc₂def, if_pos hqM₂, zero_mul]; rfl
      rw [hY0, CuspForm.zero_apply]
      simp [SlashAction.zero_slash]
    · have hc₂ : c₂ = ε₂ (q : ZMod M₂) * (q : ℂ) ^ (k - 1) := by rw [hc₂def, if_neg hqM₂]
      by_cases hB : M₂ * q ^ 2 ∣ t
      · obtain ⟨X2t, hX2tfun, hX2tcoef, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
          (k := k) (N := t) (d := q ^ 2) hB g₂
        have hYeq : (⇑Y : ℍ → ℂ) = ⇑(c₂ • X2t) := funext fun τ => by
          rw [hYfun, CuspForm.IsGLPos.smul_apply, smul_eq_mul, hX2tfun]
        obtain ⟨w, hw⟩ := hB
        refine ⟨(q : ℂ) • (c₂ • X2t), fun τ => ?_, Or.inl ?_⟩
        · rw [hYeq]
          have hterm : ∀ i : ℕ, (⇑(c₂ • X2t) : ℍ → ℂ) ∣[k]
              (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))
                = ⇑(c₂ • X2t) := by
            intro i
            have : ((i : ℤ) * t : ℤ) = (t : ℤ) * i := by ring
            rw [this, slash_beta_level]
          simp_rw [hterm]
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, CuspForm.IsGLPos.smul_apply,
            smul_eq_mul]
        · rw [qCoeff_smul, qCoeff_smul, hX2tcoef, if_neg, mul_zero, mul_zero]
          intro h
          exact hq1.ne' (Nat.dvd_one.mp ((dvd_pow_self q two_ne_zero).trans h))
      ·
        have hqM₂t : q * M₂ ∣ t :=
          Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqM₂) hqt hM₂t
        obtain ⟨u, hu⟩ := hqM₂t
        have hqu : ¬ q ∣ u := by
          rintro ⟨w, hw⟩; apply hB; exact ⟨w, by rw [hu, hw]; ring⟩
        obtain ⟨Xt, hXtfun, hXtcoef, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
          (k := k) (N := t) (d := q) ⟨u, by rw [hu]; ring⟩ g₂
        haveI : NeZero (q * M₂) := ⟨mul_ne_zero hq0 hM₂0⟩
        obtain ⟨XqM, hXqMfun, -, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
          (k := k) (N := q * M₂) (d := q) ⟨1, by ring⟩ g₂
        refine ⟨c₂ • (((q : ℂ) ^ (1 - k) * conj b) • Xt
            - (conj (ε₂ (q : ZMod M₂)) * (q : ℂ) ^ (-k)) • G₂t), fun τ => ?_, Or.inr ⟨?_, hqM₂⟩⟩
        · rw [CuspForm.IsGLPos.smul_apply, smul_eq_mul, CuspForm.sub_apply,
            CuspForm.IsGLPos.smul_apply, CuspForm.IsGLPos.smul_apply, smul_eq_mul, smul_eq_mul,
            hXtfun, hG₂tval]
          have hYeq : (⇑Y : ℍ → ℂ) = c₂ • fun σ => g₂ (heckeDiagMatrix (q ^ 2) • σ) := by
            funext σ; rw [hYfun, Pi.smul_apply, smul_eq_mul]
          rw [hYeq]
          have hsm : ∀ i : ℕ, ((c₂ • fun σ : ℍ => g₂ (heckeDiagMatrix (q ^ 2) • σ)) ∣[k]
              (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
              = c₂ * ((fun σ : ℍ => g₂ (heckeDiagMatrix (q ^ 2) • σ)) ∣[k]
                (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ := by
            intro i; rw [ModularForm.SL_smul_slash]; rfl
          simp_rw [hsm]
          rw [← Finset.mul_sum]
          congr 1

          have hq20 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq0
          have hpt : ∀ σ : ℍ, heckeDiagMatrix (q ^ 2) • σ = heckeDiagMatrix q • (heckeDiagMatrix q • σ) := by
            intro σ; apply UpperHalfPlane.ext
            rw [coe_heckeDiagMatrix_smul hq20, coe_heckeDiagMatrix_smul hq0,
              coe_heckeDiagMatrix_smul hq0]; push_cast; ring
          have hterm : ∀ i : ℕ,
              ((fun σ : ℍ => g₂ (heckeDiagMatrix (q ^ 2) • σ)) ∣[k]
                (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
              = ((fun σ : ℍ => g₂ (heckeDiagMatrix q • σ)) ∣[k] (ModularGroup.S *
                  ModularGroup.T ^ (((i * u : ℕ) : ℤ) * M₂) * ModularGroup.S⁻¹ :
                    SL(2, ℤ))) (heckeDiagMatrix q • τ) := by
            intro i
            have h := slash_beta_comp_apply (k := k) (fun σ : ℍ => g₂ (heckeDiagMatrix q • σ)) hq0
              ((i : ℤ) * t) (((i * u : ℕ) : ℤ) * M₂) (by rw [hu]; push_cast; ring) τ
            simp only [hpt] at h ⊢
            exact h
          simp_rw [hterm]
          have hXqMeq : (fun σ : ℍ => g₂ (heckeDiagMatrix q • σ)) = ⇑XqM := (funext hXqMfun).symm
          have hper : ∀ y r : ℕ,
              ((fun σ : ℍ => g₂ (heckeDiagMatrix q • σ)) ∣[k] (ModularGroup.S *
                ModularGroup.T ^ (((y + q * r : ℕ) : ℤ) * M₂) * ModularGroup.S⁻¹ :
                  SL(2, ℤ))) (heckeDiagMatrix q • τ)
              = ((fun σ : ℍ => g₂ (heckeDiagMatrix q • σ)) ∣[k] (ModularGroup.S *
                ModularGroup.T ^ ((y : ℤ) * M₂) * ModularGroup.S⁻¹ : SL(2, ℤ)))
                  (heckeDiagMatrix q • τ) := by
            intro y r
            have : (((y + q * r : ℕ) : ℤ) * M₂ : ℤ) = (y : ℤ) * M₂ + ((q * M₂ : ℕ) : ℤ) * r := by
              push_cast; ring
            rw [this, hXqMeq, slash_beta_add_level]
          rw [sum_range_reindex hq (fun x => ((fun σ : ℍ => g₂ (heckeDiagMatrix q • σ)) ∣[k]
            (ModularGroup.S * ModularGroup.T ^ ((x : ℤ) * M₂) * ModularGroup.S⁻¹ : SL(2, ℤ)))
              (heckeDiagMatrix q • τ)) hper hqu,
            CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd
              M₂ k ε₂ g₂ h₂ hq hqM₂, heckeMatrix_smul_heckeDiagMatrix_smul hq0]
        · rw [qCoeff_smul, qCoeff_sub, qCoeff_smul, qCoeff_smul, hXtcoef, hG₂tc,
            if_neg (fun h => hq1.ne' (Nat.dvd_one.mp h)), h₂.isEigenformWith.qCoeff_one, hc₂]
          have hunit : ε₂ (q : ZMod M₂) * conj (ε₂ (q : ZMod M₂)) = 1 := by
            have hu : IsUnit (q : ZMod M₂) :=
              (ZMod.isUnit_iff_coprime q M₂).mpr ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqM₂)
            have hn : ‖ε₂ (q : ZMod M₂)‖ = 1 := by
              rw [← hu.unit_spec]; exact ε₂.unit_norm_eq_one hu.unit
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; norm_num
          have hzp : (q : ℂ) ^ (k - 1) * (q : ℂ) ^ (-k) = (q : ℂ)⁻¹ := by
            rw [← zpow_add₀ hqC, show (k - 1 + -k : ℤ) = -1 by ring, zpow_neg_one]
          rw [mul_zero, zero_sub]
          calc ε₂ (q : ZMod M₂) * (q : ℂ) ^ (k - 1) *
                -((starRingEnd ℂ) (ε₂ (q : ZMod M₂)) * (q : ℂ) ^ (-k) * 1)
              = -(ε₂ (q : ZMod M₂) * (starRingEnd ℂ) (ε₂ (q : ZMod M₂))) *
                  ((q : ℂ) ^ (k - 1) * (q : ℂ) ^ (-k)) := by ring
            _ = -(q : ℂ)⁻¹ := by rw [hunit, hzp]; ring

  set Φ : CuspForm (Γ₁ℝ t) k := b • ΦX - (q : ℂ) • G₂t - ΦY with hΦdef
  have hΦfun : ∀ τ : ℍ, Φ τ = ∑ i ∈ Finset.range q, ((⇑E : ℍ → ℂ) ∣[k]
      (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ := by
    intro τ
    rw [hΦdef, CuspForm.sub_apply, CuspForm.sub_apply, CuspForm.IsGLPos.smul_apply,
      CuspForm.IsGLPos.smul_apply, smul_eq_mul, smul_eq_mul, hΦXfun, hΦYfun, ← hTb τ,
      hEdef]
    have hcoe : (⇑(G₁ - G₂ + b • X - Y) : ℍ → ℂ) = ⇑G₁ - ⇑G₂ + b • ⇑X - ⇑Y := by
      rw [CuspForm.coe_sub, CuspForm.coe_add, CuspForm.coe_sub, CuspForm.IsGLPos.coe_smul]
    rw [hcoe]
    simp only [SlashAction.add_slash, sub_eq_add_neg, SlashAction.neg_slash,
      ModularForm.SL_smul_slash, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
    rw [← Finset.sum_apply, ← Finset.sum_apply, ← Finset.sum_apply, ← Finset.sum_apply]
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_apply, Finset.sum_apply, hTa τ]
    ring
  have hΦ1 : qCoeff Φ 1 = b * qCoeff ΦX 1 - q - qCoeff ΦY 1 := by
    rw [hΦdef, qCoeff_sub, qCoeff_sub, qCoeff_smul, qCoeff_smul, hG₂tc,
      h₂.isEigenformWith.qCoeff_one, mul_one]

  have hΦ1ne : qCoeff Φ 1 ≠ 0 := by
    rw [hΦ1]
    have hqR : (1 : ℝ) < q := by exact_mod_cast hq1
    rcases hΦX1 with hX0 | ⟨hX1, hqM₂⟩
    · rw [hX0, mul_zero, zero_sub]
      rcases hΦY1 with hY0 | ⟨hY1, -⟩
      · rw [hY0, sub_zero, neg_ne_zero]; exact hqC
      · rw [hY1]
        intro h
        have h' : (q : ℂ)⁻¹ = q := by linear_combination h
        have : (q : ℂ) * q = 1 := by
          nth_rewrite 2 [← h']; exact mul_inv_cancel₀ hqC
        have h2 : (q : ℝ) * q = 1 := by exact_mod_cast this
        nlinarith
    ·
      have hY0 : qCoeff ΦY 1 = 0 := by
        rcases hΦY1 with h | ⟨-, h⟩
        · exact h
        · exact (h hqM₂).elim
      rw [hY0, sub_zero, hX1]
      have hbb : b * conj b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hg₂0 : g₂ ≠ 0 := by
        intro h0
        have h1 := h₂.isEigenformWith.qCoeff_one
        rw [h0, CuspForm.coe_zero, qCoeff_zero_fun] at h1
        exact zero_ne_one h1
      by_cases hfac : ε₂.FactorsThrough (M₂ / q)
      · obtain ⟨hdvd, χ, hχ⟩ := hfac
        have h₂' : CuspForm.IsPrimitiveForm
            (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hqM₂) χ) g₂ := by
          rw [hχ] at h₂; exact h₂
        by_cases hq2 : q ∣ M₂ / q
        ·
          have hb0 : b = 0 :=
            CuspForm.IsPrimitiveForm.qCoeff_eq_zero_of_dvd_div M₂ k hq hqM₂ hq2 χ g₂ h₂'
          rw [hb0, zero_mul, zero_sub, neg_ne_zero]; exact hqC
        ·
          have hq2' : ¬ q ^ 2 ∣ M₂ := by
            intro h; apply hq2
            exact Nat.dvd_div_of_mul_dvd (by rw [← pow_two]; exact h)
          have hnorm := CuspForm.norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd M₂ k hq hqM₂
            hq2' χ g₂ h₂'
          have hval : b * ((q : ℂ) ^ (1 - k) * conj b) = (q : ℂ)⁻¹ := by
            rw [mul_left_comm, hbb, hnorm]
            push_cast
            rw [← zpow_add₀ hqC, show (1 - k + (k - 2) : ℤ) = -1 by ring, zpow_neg_one]
          rw [hval]
          intro h
          have h' : (q : ℂ)⁻¹ = q := by linear_combination h
          have : (q : ℂ) * q = 1 := by
            nth_rewrite 2 [← h']; exact mul_inv_cancel₀ hqC
          have h2 : (q : ℝ) * q = 1 := by exact_mod_cast this
          nlinarith
      ·
        have hnorm := CuspForm.norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough M₂ k ε₂ hq
          hqM₂ hfac g₂ hg₂0 h₂.isEigenformWith.hasNebentypus b
          (h₂.isEigenformWith.hecke_of_dvd hq hqM₂)
        have hval : b * ((q : ℂ) ^ (1 - k) * conj b) = 1 := by
          rw [mul_left_comm, hbb, hnorm]
          push_cast
          rw [← zpow_add₀ hqC, show (1 - k + (k - 1) : ℤ) = 0 by ring, zpow_zero]
        rw [hval]
        intro h
        have : (q : ℂ) = 1 := by linear_combination -h
        have h2 : (q : ℕ) = 1 := by exact_mod_cast this
        exact hq1.ne' h2

  have hΦ0 : qCoeff Φ 1 = 0 :=
    CuspForm.HasNebentypus.qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash hq0 hqt εt E hEneb
      hK0 (Nat.coprime_comm.mp hqK) hEzero Φ hΦfun 1 (Nat.coprime_one_left K)
  exact hΦ1ne hΦ0

end Main

end LiCaseOne

end

theorem solution
    {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂] {k : ℤ}
    {ε₁ : DirichletCharacter ℂ M₁} {ε₂ : DirichletCharacter ℂ M₂}
    {g₁ : CuspForm (CongruenceSubgroup.Gamma1 M₁) k}
    {g₂ : CuspForm (CongruenceSubgroup.Gamma1 M₂) k}
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂)
    (ha : ∀ n : ℕ, Nat.Coprime n M₁ → Nat.Coprime n M₂ →
      ModularFormClass.qCoeff g₁ n = ModularFormClass.qCoeff g₂ n)
    (hε : ∀ n : ℕ, Nat.Coprime n M₁ → Nat.Coprime n M₂ → ε₁ (n : ZMod M₁) = ε₂ (n : ZMod M₂))
    {q : ℕ} (hq : q.Prime) (hqM : q ^ 2 ∣ M₁) (hε₁ : ε₁.FactorsThrough (M₁ / q))
    (j : ℕ) (hj : q ^ j ∣ M₁) : q ^ j ∣ M₂ :=
  LiCaseOne.main h₁ h₂ ha hε hq hqM hε₁ j hj

end S_CuspForm_IsPrimitiveForm_pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq
end P2MW
export P2MW.S_CuspForm_IsPrimitiveForm_pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq (solution)
