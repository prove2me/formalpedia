-- Prove2me | solution 1 for CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/85c26c4a-ca0a-5805-9602-77755939602a

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_CuspForm_exists_basis_gamma1_qCoeff_mem_range_ratCast
import Theorems.Thm_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast

set_option autoImplicit false

open CongruenceSubgroup ModularForm UpperHalfPlane
open scoped ModularForm UpperHalfPlane MatrixGroups

noncomputable section

namespace DeligneSerre271

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {N : ℕ} {k : ℤ}

theorem conj_mem_Gamma1 {γ x : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (hx : x ∈ Gamma1 N) :
    γ * x * γ⁻¹ ∈ Gamma1 N := by
  have hx0 : x ∈ Gamma0 N := Gamma1_in_Gamma0 N hx
  have hx' : (⟨x, hx0⟩ : Gamma0 N) ∈ Gamma1' N := by
    rw [Gamma1_to_Gamma0_mem]
    exact (Gamma1_mem N x).1 hx
  haveI : (Gamma1' N).Normal := MonoidHom.normal_ker _
  have hc : (⟨γ, hγ⟩ : Gamma0 N) * ⟨x, hx0⟩ * (⟨γ, hγ⟩ : Gamma0 N)⁻¹ ∈ Gamma1' N :=
    Subgroup.Normal.conj_mem inferInstance _ hx' _
  rw [Gamma1_to_Gamma0_mem] at hc
  exact (Gamma1_mem N _).2 hc

theorem mem_coe_Gamma1_iff (x : GL (Fin 2) ℝ) :
    x ∈ (Γ₁ℝ N) ↔ ∃ γ : SL(2, ℤ), γ ∈ Gamma1 N ∧ (Matrix.SpecialLinearGroup.mapGL ℝ γ) = x :=
  Subgroup.mem_map

open ConjAct Pointwise in

theorem toConjAct_inv_smul_coe_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ • (Γ₁ℝ N) = (Γ₁ℝ N) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, ConjAct.toConjAct_smul]
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := (mem_coe_Gamma1_iff _).1 h
    have hx : x = Matrix.SpecialLinearGroup.mapGL ℝ γ⁻¹ * Matrix.SpecialLinearGroup.mapGL ℝ y
        * Matrix.SpecialLinearGroup.mapGL ℝ γ := by
      rw [hyx, map_inv]; group
    have hmem := conj_mem_Gamma1 (Subgroup.inv_mem _ hγ) hy
    rw [inv_inv] at hmem
    rw [hx, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ hmem
  · intro h
    obtain ⟨y, hy, rfl⟩ := (mem_coe_Gamma1_iff _).1 h
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ (conj_mem_Gamma1 hγ hy)

def slashMF {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (F : ModularForm (Γ₁ℝ N) k) : ModularForm (Γ₁ℝ N) k :=
  (ModularForm.translate F (Matrix.SpecialLinearGroup.mapGL ℝ γ)).copy
    ((⇑F : ℍ → ℂ) ∣[k] γ) rfl (toConjAct_inv_smul_coe_Gamma1 hγ).symm

@[scoped simp] theorem coe_slashMF {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (F : ModularForm (Γ₁ℝ N) k) :
    ⇑(slashMF hγ F) = (⇑F : ℍ → ℂ) ∣[k] γ := rfl

theorem one_mem_strictPeriods (N : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ N).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

theorem exists_int_clearing [NeZero N] (F : ModularForm (Γ₁ℝ N) k)
    (hF : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 (⇑F)).coeff n = (r : ℂ))
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ m : ℕ,
      (D : ℂ) * ModularFormClass.qCoeff ((⇑F : ℍ → ℂ) ∣[k] γ) m ∈ Set.range ((↑) : ℤ → ℂ) := by

  have hrat : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 (⇑(slashMF hγ F))).coeff n = (r : ℂ) := fun n =>
    ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0 N F hF γ hγ n

  obtain ⟨D, p, hD0, hp⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion N (slashMF hγ F) hrat
  refine ⟨D, hD0, fun m => ⟨PowerSeries.coeff m p, ?_⟩⟩
  have h1 := ModularCurve.IsIntegralQExp.coeff hp m
  rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N) (D : ℂ) (slashMF hγ F),
    map_smul, smul_eq_mul] at h1
  rw [h1]
  rfl

theorem exists_int_clearing_forall [NeZero N] (F : ModularForm (Γ₁ℝ N) k)
    (hF : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 (⇑F)).coeff n = (r : ℂ)) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → ∀ m : ℕ,
      (D : ℂ) * ModularFormClass.qCoeff ((⇑F : ℍ → ℂ) ∣[k] γ) m ∈ Set.range ((↑) : ℤ → ℂ) := by
  classical

  let Q := Quotient (QuotientGroup.rightRel (Gamma1 N))
  haveI : Finite Q :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel (Gamma1 N)).symm
  letI : Fintype Q := Fintype.ofFinite Q

  have hcoset : ∀ q : Q, ∃ D : ℤ, D ≠ 0 ∧ (q.out ∈ Gamma0 N → ∀ m : ℕ,
      (D : ℂ) * ModularFormClass.qCoeff ((⇑F : ℍ → ℂ) ∣[k] q.out) m ∈ Set.range ((↑) : ℤ → ℂ)) := by
    intro q
    by_cases hq : q.out ∈ Gamma0 N
    · obtain ⟨D, hD0, hD⟩ := exists_int_clearing F hF hq
      exact ⟨D, hD0, fun _ => hD⟩
    · exact ⟨1, one_ne_zero, fun h => (hq h).elim⟩
  choose Dq hDq0 hDq using hcoset
  refine ⟨∏ q : Q, Dq q, Finset.prod_ne_zero_iff.2 fun q _ => hDq0 q, fun γ hγ m => ?_⟩

  let q : Q := Quotient.mk'' γ
  have hrel : QuotientGroup.rightRel (Gamma1 N) q.out γ := Quotient.mk_out' γ
  rw [QuotientGroup.rightRel_apply] at hrel

  have hout_eq : q.out = (γ * q.out⁻¹)⁻¹ * γ := by group
  have hout_mem : q.out ∈ Gamma0 N := by
    rw [hout_eq]
    exact mul_mem (inv_mem (Gamma1_in_Gamma0 N hrel)) hγ

  have hslash : (⇑F : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ q.out)
      = (⇑F : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) := by
    have hinv : (⇑F : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (γ * q.out⁻¹)⁻¹) = ⇑F :=
      SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ (inv_mem hrel))
    conv_lhs => rw [hout_eq]
    rw [map_mul, SlashAction.slash_mul, hinv]
  have hslashSL : (⇑F : ℍ → ℂ) ∣[k] q.out = (⇑F : ℍ → ℂ) ∣[k] γ := hslash

  obtain ⟨a, ha⟩ := hDq q hout_mem m
  rw [hslashSL] at ha
  have hprod : (∏ q' : Q, Dq q') = Dq q * ∏ q' ∈ Finset.univ.erase q, Dq q' :=
    (Finset.mul_prod_erase Finset.univ Dq (Finset.mem_univ q)).symm
  refine ⟨(∏ q' ∈ Finset.univ.erase q, Dq q') * a, ?_⟩
  rw [hprod]
  push_cast
  rw [mul_comm ((Dq q : ℤ) : ℂ), mul_assoc, ha]

theorem main (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (Γ₁ℝ N) k)),
      ∀ (i : Fin n) (γ : SL(2, ℤ)), γ ∈ Gamma0 N → ∀ m : ℕ,
        ModularFormClass.qCoeff ((⇑(b i) : ℍ → ℂ) ∣[k] γ) m ∈ Set.range ((↑) : ℤ → ℂ) := by

  obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast N k

  have key : ∀ i : Fin n, ∃ D : ℤ, D ≠ 0 ∧ ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → ∀ m : ℕ,
      (D : ℂ) * ModularFormClass.qCoeff ((⇑(b i) : ℍ → ℂ) ∣[k] γ) m ∈ Set.range ((↑) : ℤ → ℂ) := by
    intro i
    have hF : ∀ n : ℕ, ∃ r : ℚ,
        (qExpansion 1 (⇑((b i : CuspForm (Γ₁ℝ N) k) : ModularForm (Γ₁ℝ N) k))).coeff n = (r : ℂ) := by
      intro n
      obtain ⟨r, hr⟩ := hb i n
      exact ⟨r, hr.symm⟩
    exact exists_int_clearing_forall ((b i : CuspForm (Γ₁ℝ N) k) : ModularForm (Γ₁ℝ N) k) hF
  choose D hD0 hD using key

  refine ⟨n, b.unitsSMul fun i => Units.mk0 ((D i : ℤ) : ℂ) (Int.cast_ne_zero.2 (hD0 i)), ?_⟩
  intro i γ hγ m
  rw [Module.Basis.unitsSMul_apply, Units.smul_mk0, CuspForm.IsGLPos.coe_smul,
    ModularForm.SL_smul_slash]

  have hlin : ModularFormClass.qCoeff (((D i : ℤ) : ℂ) • ((⇑(b i) : ℍ → ℂ) ∣[k] γ)) m
      = ((D i : ℤ) : ℂ) * ModularFormClass.qCoeff ((⇑(b i) : ℍ → ℂ) ∣[k] γ) m := by
    have h := ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N) ((D i : ℤ) : ℂ)
      (slashMF hγ ((b i : CuspForm (Γ₁ℝ N) k) : ModularForm (Γ₁ℝ N) k))
    change qExpansion 1 (((D i : ℤ) : ℂ) • ((⇑(b i) : ℍ → ℂ) ∣[k] γ))
      = ((D i : ℤ) : ℂ) • qExpansion 1 ((⇑(b i) : ℍ → ℂ) ∣[k] γ) at h
    change (qExpansion 1 _).coeff m = _ * (qExpansion 1 _).coeff m
    rw [h, map_smul, smul_eq_mul]
  rw [hlin]
  exact hD i γ hγ m

end DeligneSerre271
p2m_reactivate "P2MW.S_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast.DeligneSerre271"

end
p2m_reactivate "P2MW.S_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast.DeligneSerre271"

open CongruenceSubgroup ModularForm
open scoped ModularForm UpperHalfPlane MatrixGroups

theorem solution
    (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (Gamma1 N) k)),
      ∀ (i : Fin n) (γ : SL(2, ℤ)), γ ∈ Gamma0 N → ∀ m : ℕ,
        ModularFormClass.qCoeff ((⇑(b i) : ℍ → ℂ) ∣[k] γ) m ∈ Set.range ((↑) : ℤ → ℂ) :=
  DeligneSerre271.main N k

end S_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast
end P2MW
export P2MW.S_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast (solution)
