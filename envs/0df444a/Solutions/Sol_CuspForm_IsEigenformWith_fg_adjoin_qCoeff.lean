-- Prove2me | solution 1 for CuspForm.IsEigenformWith.fg_adjoin_qCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/acf41563-b2e9-5037-a0b1-52266cf86372

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_CuspForm_exists_basis_gamma1_two_qCoeff_mem_range_intCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsEigenformWith_fg_adjoin_qCoeff
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv"
p2m_attr_erase "simp" "ModularCurve.intSeriesC_one ModularCurve.JOne.torsionGaloisRep_apply ModularCurve.coe_restrictForm ModularCurve.intSeriesC_zero ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring"

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularFormClass
open scoped MatrixGroups ModularForm

namespace CuspForm
p2m_export "CuspForm" "IsGLPos.coe_smul coe_smul coe_add IsEigenformWith exists_basis_gamma1_two_qCoeff_mem_range_intCast"
namespace IsEigenformWith
p2m_export "CuspForm.IsEigenformWith" "qCoeff_one hecke_of_not_dvd hecke_of_dvd"
namespace FgAdjoin
p2m_open "CuspForm.IsEigenformWith CuspForm"

variable {M : ℕ}

theorem one_mem_strictPeriods :
    (1 : ℝ) ∈ ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem qCoeff_zero (f : CuspForm (Gamma1 M) 2) : qCoeff f 0 = 0 := by
  unfold qCoeff
  exact CuspFormClass.qExpansion_coeff_zero f one_pos one_mem_strictPeriods

theorem qCoeff_add (f g : CuspForm (Gamma1 M) 2) (m : ℕ) :
    qCoeff (⇑(f + g)) m = qCoeff f m + qCoeff g m := by
  unfold qCoeff
  rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods f g]
  simp

theorem qCoeff_smul (c : ℂ) (f : CuspForm (Gamma1 M) 2) (m : ℕ) :
    qCoeff (⇑(c • f)) m = c * qCoeff f m := by
  unfold qCoeff
  rw [CuspForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods c f]
  simp

theorem qCoeff_zero_form (m : ℕ) : qCoeff (⇑(0 : CuspForm (Gamma1 M) 2)) m = 0 := by
  have h := qCoeff_smul (0 : ℂ) (0 : CuspForm (Gamma1 M) 2) m
  simpa using h

theorem qCoeff_sum {ι : Type*} (s : Finset ι) (F : ι → CuspForm (Gamma1 M) 2) (m : ℕ) :
    qCoeff (⇑(∑ i ∈ s, F i)) m = ∑ i ∈ s, qCoeff (F i) m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using qCoeff_zero_form (M := M) m
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, qCoeff_add, ih]

theorem qCoeff_mem_span_repr {n : ℕ} (b : Module.Basis (Fin n) ℂ (CuspForm (Gamma1 M) 2))
    (hb : ∀ (i : Fin n) (m : ℕ), qCoeff (b i) m ∈ Set.range ((↑) : ℤ → ℂ))
    (h : CuspForm (Gamma1 M) 2) (m : ℕ) :
    qCoeff h m ∈ Submodule.span ℤ (Set.range fun i : Fin n => b.repr h i) := by
  have hsum : h = ∑ i, b.repr h i • b i := (b.sum_repr h).symm
  have hcoef : qCoeff h m = ∑ i, b.repr h i * qCoeff (b i) m := by
    conv_lhs => rw [hsum]
    rw [qCoeff_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [qCoeff_smul]
  rw [hcoef]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨z, hz⟩ := hb i m
  rw [← hz, mul_comm, ← zsmul_eq_mul]
  exact Submodule.smul_mem _ z (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_fg_forall_qCoeff_mem [NeZero M] (h : CuspForm (Gamma1 M) 2) :
    ∃ N : Submodule ℤ ℂ, N.FG ∧ ∀ m : ℕ, qCoeff h m ∈ N := by
  obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_gamma1_two_qCoeff_mem_range_intCast M
  exact ⟨Submodule.span ℤ (Set.range fun i : Fin n => b.repr h i),
    Submodule.fg_span (Set.finite_range _), fun m => qCoeff_mem_span_repr b hb h m⟩

theorem isIntegral_dirichlet [NeZero M] (ε : DirichletCharacter ℂ M) (x : ZMod M) :
    IsIntegral ℤ (ε x) := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    have hpow : (ε (u : ZMod M)) ^ orderOf u = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
    have hpos : 0 < orderOf u := orderOf_pos u
    exact IsIntegral.of_pow hpos (by rw [hpow]; exact isIntegral_one)
  · rw [MulChar.map_nonunit ε hx]
    exact isIntegral_zero

def charAlg (ε : DirichletCharacter ℂ M) : Subalgebra ℤ ℂ :=
  Algebra.adjoin ℤ (Set.range fun u : (ZMod M)ˣ => ε (u : ZMod M))

theorem charAlg_fg [NeZero M] (ε : DirichletCharacter ℂ M) :
    (Subalgebra.toSubmodule (charAlg ε)).FG := by
  refine fg_adjoin_of_finite (Set.finite_range _) ?_
  rintro _ ⟨u, rfl⟩
  exact isIntegral_dirichlet ε u

theorem apply_mem_charAlg (ε : DirichletCharacter ℂ M) (x : ZMod M) : ε x ∈ charAlg ε := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    exact Algebra.subset_adjoin ⟨u, rfl⟩
  · rw [MulChar.map_nonunit ε hx]
    exact Subalgebra.zero_mem _

def multiplier (P : Submodule ℤ ℂ) : Subalgebra ℤ ℂ where
  carrier := {x | ∀ y ∈ P, x * y ∈ P}
  mul_mem' {x x'} hx hx' y hy := by
    rw [mul_assoc]
    exact hx _ (hx' y hy)
  one_mem' y hy := by simpa using hy
  add_mem' {x x'} hx hx' y hy := by
    rw [add_mul]
    exact P.add_mem (hx y hy) (hx' y hy)
  zero_mem' y hy := by simp
  algebraMap_mem' z y hy := by
    rw [show (algebraMap ℤ ℂ z) * y = z • y by simp [zsmul_eq_mul]]
    exact P.smul_mem z hy

theorem mem_multiplier {P : Submodule ℤ ℂ} {x : ℂ} :
    x ∈ multiplier P ↔ ∀ y ∈ P, x * y ∈ P := Iff.rfl

section Main

variable {ε : DirichletCharacter ℂ M} {h : CuspForm (Gamma1 M) 2}

def coeffSpan (h : CuspForm (Gamma1 M) 2) : Submodule ℤ ℂ :=
  Submodule.span ℤ (insert 1 (Set.range fun m : ℕ => qCoeff h m))

theorem one_mem_coeffSpan : (1 : ℂ) ∈ coeffSpan h :=
  Submodule.subset_span (Set.mem_insert _ _)

theorem qCoeff_mem_coeffSpan (m : ℕ) : qCoeff h m ∈ coeffSpan h :=
  Submodule.subset_span (Set.mem_insert_of_mem _ ⟨m, rfl⟩)

def bigSpan (ε : DirichletCharacter ℂ M) (h : CuspForm (Gamma1 M) 2) : Submodule ℤ ℂ :=
  Subalgebra.toSubmodule (charAlg ε) * coeffSpan h

theorem mul_mem_bigSpan {z q : ℂ} (hz : z ∈ charAlg ε) (hq : q ∈ coeffSpan h) :
    z * q ∈ bigSpan ε h :=
  Submodule.mul_mem_mul hz hq

theorem coeffSpan_le_bigSpan : coeffSpan h ≤ bigSpan ε h := by
  intro q hq
  simpa using mul_mem_bigSpan (Subalgebra.one_mem (charAlg ε)) hq

theorem one_mem_bigSpan : (1 : ℂ) ∈ bigSpan ε h :=
  coeffSpan_le_bigSpan one_mem_coeffSpan

theorem charAlg_le_multiplier : charAlg ε ≤ multiplier (bigSpan ε h) := by
  intro z hz y hy
  refine Submodule.mul_induction_on hy ?_ ?_
  · intro z' hz' q hq
    rw [← mul_assoc]
    exact mul_mem_bigSpan (Subalgebra.mul_mem _ hz hz') hq
  · intro x y hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy

theorem mem_multiplier_of_forall_coeffSpan {x : ℂ}
    (hx : ∀ q ∈ coeffSpan h, x * q ∈ bigSpan ε h) : x ∈ multiplier (bigSpan ε h) := by
  intro y hy
  refine Submodule.mul_induction_on hy ?_ ?_
  · intro z hz q hq
    rw [mul_left_comm]
    exact charAlg_le_multiplier hz _ (hx q hq)
  · intro a b ha hb
    rw [mul_add]
    exact Submodule.add_mem _ ha hb

theorem mem_multiplier_of_forall_qCoeff {x : ℂ} (hx1 : x ∈ bigSpan ε h)
    (hx : ∀ j : ℕ, x * qCoeff h j ∈ bigSpan ε h) : x ∈ multiplier (bigSpan ε h) := by
  refine mem_multiplier_of_forall_coeffSpan fun q hq => ?_
  induction hq using Submodule.span_induction with
  | mem q hq =>
      rcases hq with rfl | ⟨j, rfl⟩
      · simpa using hx1
      · exact hx j
  | zero => simp
  | add a b _ _ ha hb =>
      rw [mul_add]
      exact Submodule.add_mem _ ha hb
  | smul z a _ ha =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ z ha

theorem qCoeff_prime_mem_multiplier (hh : IsEigenformWith ε h) {p : ℕ} (hp : p.Prime) :
    qCoeff h p ∈ multiplier (bigSpan ε h) := by
  refine mem_multiplier_of_forall_qCoeff (coeffSpan_le_bigSpan (qCoeff_mem_coeffSpan p)) ?_
  intro j
  by_cases hpM : p ∣ M
  · rw [← hh.hecke_of_dvd hp hpM j]
    exact coeffSpan_le_bigSpan (qCoeff_mem_coeffSpan _)
  · have hrel := hh.hecke_of_not_dvd hp hpM j
    have hz : ((2 : ℤ) - 1) = 1 := by norm_num
    rw [hz, zpow_one] at hrel
    rw [← hrel]
    refine Submodule.add_mem _ (coeffSpan_le_bigSpan (qCoeff_mem_coeffSpan _)) ?_
    split_ifs with hpj
    · rw [mul_assoc]
      refine mul_mem_bigSpan (apply_mem_charAlg ε _) ?_
      rw [show (p : ℂ) * qCoeff h (j / p) = (p : ℤ) • qCoeff h (j / p) by simp [zsmul_eq_mul]]
      exact Submodule.smul_mem _ _ (qCoeff_mem_coeffSpan _)
    · simp

theorem qCoeff_mem_multiplier (hh : IsEigenformWith ε h) (m : ℕ) :
    qCoeff h m ∈ multiplier (bigSpan ε h) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · rw [qCoeff_zero]
        exact Subalgebra.zero_mem _
      · rw [hh.qCoeff_one]
        exact Subalgebra.one_mem _
    · obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
      obtain ⟨m', rfl⟩ := hpm
      have hm'pos : 0 < m' := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
      have hm'lt : m' < p * m' := by
        have := hp.two_le
        nlinarith
      have hS_p := qCoeff_prime_mem_multiplier hh hp
      have hS_m' := ih m' hm'lt
      by_cases hpM : p ∣ M
      · rw [hh.hecke_of_dvd hp hpM m']
        exact Subalgebra.mul_mem _ hS_p hS_m'
      · have hrel := hh.hecke_of_not_dvd hp hpM m'
        have hz : ((2 : ℤ) - 1) = 1 := by norm_num
        rw [hz, zpow_one] at hrel
        have heq : qCoeff h (p * m') = qCoeff h p * qCoeff h m' -
            ε (p : ZMod M) * (p : ℂ) * (if p ∣ m' then qCoeff h (m' / p) else 0) := by
          rw [← hrel]; ring
        rw [heq]
        refine Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hS_p hS_m') ?_
        refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ ?_) ?_
        · exact charAlg_le_multiplier (apply_mem_charAlg ε _)
        · exact_mod_cast Subalgebra.natCast_mem (multiplier (bigSpan ε h)) p
        · split_ifs with hpm'
          · refine ih (m' / p) (lt_of_le_of_lt (Nat.div_le_self _ _) hm'lt)
          · exact Subalgebra.zero_mem _

theorem adjoin_le_bigSpan (hh : IsEigenformWith ε h) :
    Subalgebra.toSubmodule (Algebra.adjoin ℤ
      ((Set.range fun n : ℕ => qCoeff h n) ∪ Set.range fun u : (ZMod M)ˣ => ε (u : ZMod M))) ≤
      bigSpan ε h := by
  have hle : Algebra.adjoin ℤ
      ((Set.range fun n : ℕ => qCoeff h n) ∪ Set.range fun u : (ZMod M)ˣ => ε (u : ZMod M)) ≤
      multiplier (bigSpan ε h) := by
    refine Algebra.adjoin_le ?_
    rintro x (⟨n, rfl⟩ | ⟨u, rfl⟩)
    · exact qCoeff_mem_multiplier hh n
    · exact charAlg_le_multiplier (apply_mem_charAlg ε _)
  intro x hx
  have hxS : x ∈ multiplier (bigSpan ε h) := hle hx
  simpa using hxS 1 one_mem_bigSpan

theorem exists_fg_bigSpan_le [NeZero M] (h : CuspForm (Gamma1 M) 2) :
    ∃ P : Submodule ℤ ℂ, P.FG ∧ bigSpan ε h ≤ P := by
  obtain ⟨N, hN, hmem⟩ := exists_fg_forall_qCoeff_mem h
  refine ⟨Subalgebra.toSubmodule (charAlg ε) * (Submodule.span ℤ {1} ⊔ N),
    (charAlg_fg ε).mul ((Submodule.fg_span (Set.finite_singleton _)).sup hN), ?_⟩
  refine Submodule.mul_le.2 fun z hz q hq => Submodule.mul_mem_mul hz ?_
  have : coeffSpan h ≤ Submodule.span ℤ {1} ⊔ N := by
    refine Submodule.span_le.2 ?_
    rintro x (rfl | ⟨m, rfl⟩)
    · exact Submodule.mem_sup_left (Submodule.subset_span rfl)
    · exact Submodule.mem_sup_right (hmem m)
  exact this hq

theorem main [NeZero M] (hh : IsEigenformWith ε h) :
    (Subalgebra.toSubmodule (Algebra.adjoin ℤ
      ((Set.range fun n : ℕ => qCoeff h n) ∪ Set.range fun u : (ZMod M)ˣ => ε (u : ZMod M)))).FG := by
  obtain ⟨P, hP, hle⟩ := exists_fg_bigSpan_le (ε := ε) h
  have hle' := (adjoin_le_bigSpan hh).trans hle
  haveI : IsNoetherian ℤ P := isNoetherian_of_fg_of_noetherian _ hP
  haveI := isNoetherian_of_le hle'
  exact Module.Finite.iff_fg.1 inferInstance

end Main

end CuspForm.IsEigenformWith.FgAdjoin

end

theorem solution
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M}
    {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2} (hh : CuspForm.IsEigenformWith ε h) :
    (Subalgebra.toSubmodule (Algebra.adjoin ℤ
      ((Set.range fun n : ℕ => ModularFormClass.qCoeff h n) ∪
        Set.range fun u : (ZMod M)ˣ => ε (u : ZMod M)))).FG :=
  CuspForm.IsEigenformWith.FgAdjoin.main hh

end S_CuspForm_IsEigenformWith_fg_adjoin_qCoeff
end P2MW
export P2MW.S_CuspForm_IsEigenformWith_fg_adjoin_qCoeff (solution)
