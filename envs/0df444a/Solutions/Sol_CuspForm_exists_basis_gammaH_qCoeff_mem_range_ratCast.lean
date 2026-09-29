-- Prove2me | solution 1 for CuspForm.exists_basis_gammaH_qCoeff_mem_range_ratCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/54242008-6a3c-558b-8b82-ad1ffef357ee

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_exists_basis_gamma1_qCoeff_mem_range_ratCast
import Theorems.Thm_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_basis_gammaH_qCoeff_mem_range_ratCast
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv"
p2m_attr_erase "simp" "ModularCurve.intSeriesC_one ModularCurve.JOne.torsionGaloisRep_apply ModularCurve.coe_restrictForm ModularCurve.intSeriesC_zero ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring"

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularForm UpperHalfPlane SlashInvariantForm
open scoped ModularForm UpperHalfPlane MatrixGroups

namespace GammaHRationalBasis

variable {N : ℕ} {H : Subgroup (ZMod N)ˣ} {k : ℤ}

local notation "ΓH" => CohCarrier.GammaH N H
local notation "ΓHℝ" => ((CohCarrier.GammaH N H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₁ℝ" => ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Groups

variable (N H)

theorem translation_mem_GammaH : ModularGroup.T ∈ ΓH := by
  rw [CohCarrier.mem_GammaH_iff]
  have hT0 : ModularGroup.T ∈ Gamma0 N := by
    rw [Gamma0_mem]
    simp [ModularGroup.T]
  refine ⟨hT0, ?_⟩
  have : CohCarrier.gamma0Units N ⟨ModularGroup.T, hT0⟩ = 1 := by
    ext
    simp [CohCarrier.gamma0Units, Gamma0Map, ModularGroup.T]
  rw [this]
  exact one_mem H

theorem Gamma1_le_GammaH : Gamma1 N ≤ ΓH := by
  intro A hA
  rw [Gamma1_mem] at hA
  obtain ⟨_, h11, h10⟩ := hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA0 : A ∈ Gamma0 N := Gamma0_mem.mpr h10
  refine ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units N ⟨A, hA0⟩ = 1 := by
    ext
    simp only [CohCarrier.gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one, Gamma0Map]
    exact h11
  rw [this]
  exact one_mem H

scoped instance finiteIndex_GammaH [NeZero N] : (ΓH).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH N H)

omit H in

theorem coe_le_SL (Γ : Subgroup SL(2, ℤ)) :
    (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
  rw [MonoidHom.range_eq_map]
  exact Subgroup.map_mono le_top

theorem coeG1_le : (Γ₁ℝ) ≤ ΓHℝ := Subgroup.map_mono (Gamma1_le_GammaH N H)

theorem GammaH_le_Gamma0' : (ΓH) ≤ Gamma0 N := CohCarrier.GammaH_le_Gamma0 H

scoped instance isFiniteRelIndex_G1_GH [NeZero N] : (Γ₁ℝ).IsFiniteRelIndex ΓHℝ :=
  Subgroup.isFiniteRelIndex_of_le_right (Γ₁ℝ) (coe_le_SL (ΓH))

theorem one_mem_strictPeriods_GH : (1 : ℝ) ∈ (ΓHℝ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH N H)]
  exact AddSubgroup.mem_zmultiples _

omit H in
theorem one_mem_strictPeriods_G1 : (1 : ℝ) ∈ (Γ₁ℝ).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

end Groups

section Translates

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
    x ∈ (Γ₁ℝ) ↔ ∃ γ : SL(2, ℤ), γ ∈ Gamma1 N ∧ (Matrix.SpecialLinearGroup.mapGL ℝ γ) = x :=
  Subgroup.mem_map

open ConjAct Pointwise in

theorem toConjAct_inv_smul_coe_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ • (Γ₁ℝ) = (Γ₁ℝ) := by
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

def slashMF {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (F : ModularForm (Γ₁ℝ) k) : ModularForm (Γ₁ℝ) k :=
  (ModularForm.translate F (Matrix.SpecialLinearGroup.mapGL ℝ γ)).copy
    ((⇑F : ℍ → ℂ) ∣[k] γ) rfl (toConjAct_inv_smul_coe_Gamma1 hγ).symm

@[scoped simp] theorem coe_slashMF {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (F : ModularForm (Γ₁ℝ) k) :
    ⇑(slashMF hγ F) = (⇑F : ℍ → ℂ) ∣[k] γ := rfl

end Translates

section Restrict

def restrictCusp {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (f : CuspForm Γ k) :
    CuspForm Γ' k where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (h hA)
  holo' := f.holo'
  zero_at_cusps' hc := f.zero_at_cusps' (hc.mono h)

@[scoped simp] theorem coe_restrictCusp {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (f : CuspForm Γ k) :
    (⇑(restrictCusp h f) : ℍ → ℂ) = f :=
  rfl

def toG1 (F : CuspForm (ΓHℝ) k) : CuspForm (Γ₁ℝ) k := restrictCusp (coeG1_le N H) F

@[scoped simp] theorem coe_toG1 (F : CuspForm (ΓHℝ) k) : (⇑(toG1 F) : ℍ → ℂ) = F := rfl

omit N H in

theorem CuspForm_coe_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {ι : Type*} (s : Finset ι)
    (F : ι → CuspForm Γ k) : (⇑(∑ i ∈ s, F i) : ℍ → ℂ) = ∑ i ∈ s, (⇑(F i) : ℍ → ℂ) :=
  map_sum (FunLike.coeAddMonoidHom (CuspForm Γ k) ℍ ℂ) F s

omit N H in

theorem ModularForm_coe_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {ι : Type*} (s : Finset ι)
    (F : ι → ModularForm Γ k) : (⇑(∑ i ∈ s, F i) : ℍ → ℂ) = ∑ i ∈ s, (⇑(F i) : ℍ → ℂ) :=
  map_sum (FunLike.coeAddMonoidHom (ModularForm Γ k) ℍ ℂ) F s

end Restrict

section Trace

variable [NeZero N]

local notation "𝒬" => (↥(ΓHℝ)) ⧸ (Subgroup.subgroupOf (Γ₁ℝ) (ΓHℝ))

local instance : Fintype 𝒬 := Fintype.ofFinite _

def rep (r : ↥(ΓHℝ)) : SL(2, ℤ) := ((Subgroup.mem_map.mp r.2).choose)⁻¹

omit [NeZero N] in
theorem rep_inv_mem (r : ↥(ΓHℝ)) : (rep (N := N) (H := H) r)⁻¹ ∈ ΓH := by
  rw [rep, inv_inv]
  exact (Subgroup.mem_map.mp r.2).choose_spec.1

omit [NeZero N] in
theorem rep_mem (r : ↥(ΓHℝ)) : rep (N := N) (H := H) r ∈ ΓH := by
  simpa using Subgroup.inv_mem _ (rep_inv_mem r)

omit [NeZero N] in
theorem mapGL_rep (r : ↥(ΓHℝ)) :
    Matrix.SpecialLinearGroup.mapGL ℝ (rep (N := N) (H := H) r) = (r : GL (Fin 2) ℝ)⁻¹ := by
  rw [rep, map_inv, (Subgroup.mem_map.mp r.2).choose_spec.2]

omit [NeZero N] in

theorem quotientFunc_mk_eq (x : CuspForm (Γ₁ℝ) k) (r : ↥(ΓHℝ)) :
    quotientFunc x (⟦r⟧ : 𝒬) = (⇑x : ℍ → ℂ) ∣[k] (rep (N := N) (H := H) r) := by
  rw [quotientFunc_mk, ModularForm.SL_slash, ← mapGL_rep]
  rfl

def R (q : 𝒬) : SL(2, ℤ) := rep (N := N) (H := H) q.out

omit [NeZero N] in
theorem R_mem (q : 𝒬) : R (N := N) (H := H) q ∈ ΓH := rep_mem _

omit [NeZero N] in
theorem R_mem_Gamma0 (q : 𝒬) : R (N := N) (H := H) q ∈ Gamma0 N :=
  GammaH_le_Gamma0' N H (R_mem q)

variable (H) in

def trC (x : CuspForm (Γ₁ℝ) k) : CuspForm (ΓHℝ) k := CuspForm.trace (ΓHℝ) x

theorem coe_trC_eq_coe_trace (x : CuspForm (Γ₁ℝ) k) :
    (⇑(trC H x) : ℍ → ℂ) = ⇑(ModularForm.trace (ΓHℝ) x) := rfl

theorem coe_trC (x : CuspForm (Γ₁ℝ) k) :
    (⇑(trC H x) : ℍ → ℂ) = ∑ q : 𝒬, (⇑x : ℍ → ℂ) ∣[k] (R (N := N) (H := H) q) := by
  rw [coe_trC_eq_coe_trace, ModularForm.coe_trace]
  refine Finset.sum_congr rfl fun q _ => ?_
  conv_lhs => rw [← Quotient.out_eq q]
  exact quotientFunc_mk_eq x q.out

theorem coe_trC_sum_smul {ι : Type*} (s : Finset ι) (a : ι → ℂ) (b : ι → CuspForm (Γ₁ℝ) k) :
    (⇑(trC H (∑ i ∈ s, a i • b i)) : ℍ → ℂ) = ∑ i ∈ s, a i • (⇑(trC H (b i)) : ℍ → ℂ) := by
  rw [coe_trC]
  have hcoe : (⇑(∑ i ∈ s, a i • b i : CuspForm (Γ₁ℝ) k) : ℍ → ℂ) =
      ∑ i ∈ s, a i • (⇑(b i) : ℍ → ℂ) := by
    rw [CuspForm_coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [CuspForm.IsGLPos.coe_smul]
  simp_rw [hcoe, SlashAction.sum_slash, ModularForm.SL_smul_slash, coe_trC, Finset.smul_sum]
  exact Finset.sum_comm

theorem coe_trC_toG1 (F : CuspForm (ΓHℝ) k) :
    (⇑(trC H (toG1 F)) : ℍ → ℂ) = (Nat.card 𝒬 : ℂ) • (⇑F : ℍ → ℂ) := by
  rw [coe_trC]
  have : ∀ q : 𝒬, (⇑(toG1 F) : ℍ → ℂ) ∣[k] (R (N := N) (H := H) q) = ⇑F := by
    intro q
    rw [coe_toG1, ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ (R_mem q))
  simp_rw [this, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    Nat.card_eq_fintype_card]

theorem card_Q_ne_zero : (Nat.card 𝒬 : ℂ) ≠ 0 := by
  have : 0 < Nat.card 𝒬 := Nat.card_pos
  exact_mod_cast this.ne'

theorem qExpansion_trC (x : CuspForm (Γ₁ℝ) k) :
    qExpansion 1 (⇑(trC H x) : ℍ → ℂ) =
      ∑ q : 𝒬, qExpansion 1 ((⇑x : ℍ → ℂ) ∣[k] (R (N := N) (H := H) q)) := by

  let M : 𝒬 → ModularForm (Γ₁ℝ) k := fun q => slashMF (R_mem_Gamma0 q) (x : ModularForm (Γ₁ℝ) k)
  have hM : ∀ q, (⇑(M q) : ℍ → ℂ) = (⇑x : ℍ → ℂ) ∣[k] (R (N := N) (H := H) q) := fun q => rfl
  have hsum : (⇑(trC H x) : ℍ → ℂ) = ⇑(∑ q : 𝒬, M q) := by
    rw [coe_trC, ModularForm_coe_sum]
    exact Finset.sum_congr rfl fun q _ => (hM q).symm
  rw [hsum]
  change ModularForm.qExpansionAddHom one_pos (one_mem_strictPeriods_G1 N) k (∑ q : 𝒬, M q) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun q _ => by rw [← hM q]; rfl

theorem trC_rational (x : CuspForm (Γ₁ℝ) k)
    (hx : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 (⇑x : ℍ → ℂ)).coeff n = (r : ℂ)) (n : ℕ) :
    ∃ r : ℚ, (qExpansion 1 (⇑(trC H x) : ℍ → ℂ)).coeff n = (r : ℂ) := by
  have hq : ∀ q : 𝒬, ∃ r : ℚ,
      (qExpansion 1 ((⇑x : ℍ → ℂ) ∣[k] (R (N := N) (H := H) q))).coeff n = (r : ℂ) := fun q =>
    ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0 N (x : ModularForm (Γ₁ℝ) k) hx
      (R q) (R_mem_Gamma0 q) n
  choose r hr using hq
  refine ⟨∑ q : 𝒬, r q, ?_⟩
  rw [qExpansion_trC, map_sum]
  push_cast
  exact Finset.sum_congr rfl fun q _ => hr q

theorem qCoeff_trC_mem_range (x : CuspForm (Γ₁ℝ) k)
    (hx : ∀ m : ℕ, ModularFormClass.qCoeff (⇑x : ℍ → ℂ) m ∈ Set.range ((↑) : ℚ → ℂ)) (m : ℕ) :
    ModularFormClass.qCoeff (⇑(trC H x) : ℍ → ℂ) m ∈ Set.range ((↑) : ℚ → ℂ) := by
  have hx' : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 (⇑x : ℍ → ℂ)).coeff n = (r : ℂ) := by
    intro n
    obtain ⟨r, hr⟩ := hx n
    exact ⟨r, hr.symm⟩
  obtain ⟨r, hr⟩ := trC_rational x hx' m
  exact ⟨r, hr.symm⟩

theorem mem_span_trC {n : ℕ} (b : Module.Basis (Fin n) ℂ (CuspForm (Γ₁ℝ) k))
    (F : CuspForm (ΓHℝ) k) :
    F ∈ Submodule.span ℂ (Set.range fun i : Fin n => trC H (b i)) := by
  classical
  set c : ℂ := (Nat.card 𝒬 : ℂ) with hc
  have hc0 : c ≠ 0 := card_Q_ne_zero
  have hrepr : toG1 F = ∑ i, (b.repr (toG1 F) i) • b i := (b.sum_repr (toG1 F)).symm

  have htr : c • (⇑F : ℍ → ℂ) = ∑ i, (b.repr (toG1 F) i) • (⇑(trC H (b i)) : ℍ → ℂ) := by
    conv_lhs => rw [← coe_trC_toG1, hrepr, coe_trC_sum_smul]

  have hF : F = ∑ i, (c⁻¹ * b.repr (toG1 F) i) • trC H (b i) := by
    refine DFunLike.ext' ?_
    rw [CuspForm_coe_sum]
    calc (⇑F : ℍ → ℂ) = c⁻¹ • (c • (⇑F : ℍ → ℂ)) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • ∑ i, (b.repr (toG1 F) i) • (⇑(trC H (b i)) : ℍ → ℂ) := by rw [htr]
      _ = ∑ i, (⇑((c⁻¹ * b.repr (toG1 F) i) • trC H (b i)) : ℍ → ℂ) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [CuspForm.IsGLPos.coe_smul, smul_smul]
  rw [hF]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

variable (N H k) in

theorem main :
    ∃ (n : ℕ) (B : Module.Basis (Fin n) ℂ (CuspForm (ΓHℝ) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (B i) m ∈ Set.range ((↑) : ℚ → ℂ) := by
  classical

  obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast N k

  let v : Fin n → CuspForm (ΓHℝ) k := fun i => trC H (b i)
  have hv : ∀ (i : Fin n) (m : ℕ),
      ModularFormClass.qCoeff (⇑(v i) : ℍ → ℂ) m ∈ Set.range ((↑) : ℚ → ℂ) := fun i m =>
    qCoeff_trC_mem_range (b i) (hb i) m
  have hspan : ⊤ ≤ Submodule.span ℂ (Set.range v) := fun F _ => mem_span_trC b F

  obtain ⟨t, ht_sub, ht_span, ht_ind⟩ := exists_linearIndependent ℂ (Set.range v)
  have ht_fin : t.Finite := (Set.finite_range v).subset ht_sub
  letI : Fintype t := ht_fin.fintype
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : t → CuspForm (ΓHℝ) k)) := by
    rw [Subtype.range_coe, ht_span]
    exact hspan
  let B : Module.Basis t ℂ (CuspForm (ΓHℝ) k) := Module.Basis.mk ht_ind htop
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  refine ⟨Fintype.card t, B.reindex e, fun i m => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
  obtain ⟨j, hj⟩ := ht_sub (e.symm i).2
  rw [← hj]
  exact hv j m

end Trace

end GammaHRationalBasis
p2m_reactivate "P2MW.S_CuspForm_exists_basis_gammaH_qCoeff_mem_range_ratCast.GammaHRationalBasis"

end
p2m_reactivate "P2MW.S_CuspForm_exists_basis_gammaH_qCoeff_mem_range_ratCast.GammaHRationalBasis"

theorem solution (N : ℕ) [NeZero N]
    (H : Subgroup (ZMod N)ˣ) (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ
      (CuspForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ Set.range ((↑) : ℚ → ℂ) :=
  GammaHRationalBasis.main N H k

end S_CuspForm_exists_basis_gammaH_qCoeff_mem_range_ratCast
end P2MW
export P2MW.S_CuspForm_exists_basis_gammaH_qCoeff_mem_range_ratCast (solution)
