-- Prove2me | solution 1 for CohCarrier.mem_parabolicHoms_of_mem_cornerSubmodule_H1_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d1a29773-0e73-5964-a3a1-05d1cf82c358

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one
import Theorems.Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_mem_parabolicHoms_of_mem_cornerSubmodule_H1_of_notMem
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups IsMulCommutative

namespace CohCarrier
p2m_export "CohCarrier" "Gen heckeTL heckeTL_apply diamondL opFamily hdata Gen.T GammaH H1 conjUpperMat GammaHUpper dvd_of_mem_GammaHUpper conjL heckeT conjHom diamondRaw heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one"
namespace CornerParabolic
p2m_open "CohCarrier"

section Stable

variable (M : ℕ) (Hs : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] {A : Type*} [AddCommGroup A]

theorem heckeT_apply_eq_sum (φ : H1 M Hs A) (u : ↥(GammaH M Hs))
    [Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers u)
      (↥(GammaH M Hs) ⧸ GammaHUpper M Hs ℓ)))] :
    heckeT M Hs ℓ A φ (Additive.ofMul u) =
      ∑ O : Quotient (MulAction.orbitRel (Subgroup.zpowers u)
          (↥(GammaH M Hs) ⧸ GammaHUpper M Hs ℓ)),
        φ (Additive.ofMul (conjL M Hs ℓ
          ⟨O.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) O.out * O.out.out,
            QuotientGroup.out_conj_pow_minimalPeriod_mem _ u O.out⟩)) := by
  change Multiplicative.toAdd (MonoidHom.transfer
    ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M Hs ℓ)) u) = _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  rfl

theorem trace_conjUpperMat (X : SL(2, ℤ)) (hX : (ℓ : ℤ) ∣ X 0 1) :
    ((conjUpperMat ℓ X hX : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      ((X : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [conjUpperMat]

theorem trace_sq_conj_pow (γ r : SL(2, ℤ)) (m : ℕ)
    (hγ : (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    (((r⁻¹ * γ ^ m * r : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4 := by
  obtain ⟨ε, δ, h, hε, rfl⟩ := ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four γ hγ
  have hu : ∀ n : ℕ, ((r⁻¹ * (δ * ModularGroup.T ^ h * δ⁻¹) ^ n * r : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    intro n
    rw [conj_pow, ← zpow_natCast, ← _root_.zpow_mul,
      show r⁻¹ * (δ * ModularGroup.T ^ (h * (n : ℤ)) * δ⁻¹) * r =
        (r⁻¹ * δ) * (ModularGroup.T ^ (h * (n : ℤ)) * (r⁻¹ * δ)⁻¹) by group,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
      show ModularGroup.T ^ (h * (n : ℤ)) * (r⁻¹ * δ)⁻¹ * (r⁻¹ * δ) = ModularGroup.T ^ (h * (n : ℤ)) by group,
      ModularGroup.coe_T_zpow, Matrix.trace_fin_two_of]
    ring
  rcases hε with rfl | rfl
  · rw [one_mul, hu]; norm_num
  · rw [neg_one_mul, neg_pow]
    rcases neg_one_pow_eq_or SL(2, ℤ) m with h1 | h1
    · rw [h1, one_mul, hu]; norm_num
    · rw [h1, neg_one_mul, mul_neg, neg_mul, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg,
        neg_sq, hu]
      norm_num

theorem heckeT_isParabolicHom (φ : H1 M Hs A)
    (hφ : ModularCurve.Period.IsParabolicHom (GammaH M Hs) φ) :
    ModularCurve.Period.IsParabolicHom (GammaH M Hs) (heckeT M Hs ℓ A φ) := by
  classical
  intro γ hγ
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers γ)
      (↥(GammaH M Hs) ⧸ GammaHUpper M Hs ℓ))) := Fintype.ofFinite _
  rw [heckeT_apply_eq_sum]
  refine Finset.sum_eq_zero fun O _ => hφ _ ?_
  set x : ↥(GammaHUpper M Hs ℓ) := ⟨O.out.out⁻¹ * γ ^ Function.minimalPeriod (γ • ·) O.out * O.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem _ γ O.out⟩ with hxdef
  have hx : ((conjL M Hs ℓ x : ↥(GammaH M Hs)) : SL(2, ℤ)) =
      conjUpperMat ℓ ((x : ↥(GammaH M Hs)) : SL(2, ℤ)) (dvd_of_mem_GammaHUpper M Hs ℓ x) := rfl
  rw [hx, trace_conjUpperMat, hxdef]
  show ((((O.out.out⁻¹ * γ ^ Function.minimalPeriod (γ • ·) O.out * O.out.out : ↥(GammaH M Hs)) :
    SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
  exact trace_sq_conj_pow _ _ _ hγ

theorem diamondRaw_isParabolicHom (σ : Gamma0 M) (φ : H1 M Hs A)
    (hφ : ModularCurve.Period.IsParabolicHom (GammaH M Hs) φ) :
    ModularCurve.Period.IsParabolicHom (GammaH M Hs) (diamondRaw M Hs A σ φ) := by
  intro γ hγ
  show φ (Additive.ofMul (conjHom M Hs σ γ)) = 0
  refine hφ _ ?_
  show ((((σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ : SL(2, ℤ)) :
    Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
    show (σ : SL(2, ℤ))⁻¹ * ((σ : SL(2, ℤ)) * (γ : SL(2, ℤ))) = γ by group]
  exact hγ

end Stable

section Corner

variable (N : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
  (hcomm : ∀ g h : Gen N S, opFamily N ⊤ S 𝒪 g * opFamily N ⊤ S 𝒪 h = opFamily N ⊤ S 𝒪 h * opFamily N ⊤ S 𝒪 g)
  (θbar : Gen N S → k)

abbrev Par : Submodule 𝒪 (H1 N ⊤ 𝒪) := ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪

theorem opFamily_mem_Par (g : Gen N S) (v : H1 N ⊤ 𝒪) (hv : v ∈ Par N 𝒪) :
    opFamily N ⊤ S 𝒪 g v ∈ Par N 𝒪 := by
  rw [ModularCurve.Period.mem_parabolicHoms_iff] at hv ⊢
  cases g with
  | T ℓ hℓ hℓS hℓM =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    show ModularCurve.Period.IsParabolicHom _ (heckeTL N ⊤ 𝒪 ℓ v)
    rw [heckeTL_apply]
    exact heckeT_isParabolicHom N ⊤ ℓ v hv
  | U q hq hqM =>
    haveI : NeZero q := ⟨hq.ne_zero⟩
    show ModularCurve.Period.IsParabolicHom _ (heckeTL N ⊤ 𝒪 q v)
    rw [heckeTL_apply]
    exact heckeT_isParabolicHom N ⊤ q v hv
  | dia d =>
    show ModularCurve.Period.IsParabolicHom _ (diamondL N ⊤ 𝒪 d v)
    exact diamondRaw_isParabolicHom N ⊤ _ v hv

theorem opSubalgebra_mem_Par (b : ↥(hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra)
    (v : H1 N ⊤ 𝒪) (hv : v ∈ Par N 𝒪) : b • v ∈ Par N 𝒪 := by
  show (b : Module.End 𝒪 (H1 N ⊤ 𝒪)) v ∈ Par N 𝒪
  obtain ⟨x, hx⟩ := b
  simp only
  induction hx using Algebra.adjoin_induction generalizing v with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact opFamily_mem_Par N S 𝒪 g v hv
  | algebraMap r =>
    rw [Module.algebraMap_end_apply]
    exact (Par N 𝒪).smul_mem r hv
  | add x y _ _ hx hy =>
    rw [LinearMap.add_apply]
    exact (Par N 𝒪).add_mem (hx v hv) (hy v hv)
  | mul x y _ _ hx hy =>
    rw [Module.End.mul_apply]
    exact hx _ (hy v hv)

variable (Sp : IharaLemma.IdempotentSplitting ↥(hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra) (i₀ : Fin Sp.n)

theorem corner_le_Par (x : ↥(hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra) (hx : x ∉ Sp.𝔪 i₀)
    (hxP : ∀ v : H1 N ⊤ 𝒪, x • v ∈ Par N 𝒪) (φ : H1 N ⊤ 𝒪)
    (hφ : φ ∈ IharaLemma.cornerSubmodule (M := H1 N ⊤ 𝒪) (Sp.e i₀)) : φ ∈ Par N 𝒪 := by
  obtain ⟨t, ht⟩ := IharaLemma.exists_mul_mul_eq_of_notMem (Sp.idem i₀) (Sp.𝔪 i₀)
    (Sp.mem_of_isMaximal_of_ne i₀) hx
  obtain ⟨v, rfl⟩ := hφ
  change Sp.e i₀ • v ∈ Par N 𝒪
  rw [← ht, mul_smul, mul_smul]
  exact opSubalgebra_mem_Par N S 𝒪 k hcomm θbar t _ (hxP _)

end Corner

end CohCarrier.CornerParabolic

open _root_.CohCarrier _root_.P2MW.S_CohCarrier_mem_parabolicHoms_of_mem_cornerSubmodule_H1_of_notMem.CohCarrier CohCarrier.CornerParabolic in
open scoped IsMulCommutative in
theorem solution
    (N : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
    (hcomm : ∀ g h : CohCarrier.Gen N S,
      CohCarrier.opFamily N ⊤ S 𝒪 g * CohCarrier.opFamily N ⊤ S 𝒪 h =
        CohCarrier.opFamily N ⊤ S 𝒪 h * CohCarrier.opFamily N ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen N S → k)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N)
    (hℓ1 : ∀ t : ℕ, t * t ∣ N → ℓ ≡ 1 [MOD t])
    (hnot : (⟨(CohCarrier.hdata N ⊤ S 𝒪 k hcomm θbar).op (CohCarrier.Gen.T ℓ hℓ hℓS hℓN),
              Algebra.subset_adjoin (Set.mem_range_self _)⟩ -
            ((ℓ : ↥(CohCarrier.hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra) + 1)) ∉ Sp.𝔪 i₀)
    (φ : CohCarrier.H1 N ⊤ 𝒪)
    (hφ : φ ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)) :
    φ ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪 := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine corner_le_Par N S 𝒪 k hcomm θbar Sp i₀ _ hnot (fun v => ?_) φ hφ
  have key := CohCarrier.heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one N 𝒪 v ℓ hℓ hℓN hℓ1
  rw [ModularCurve.Period.mem_parabolicHoms_iff] at key
  set xB : ↥(CohCarrier.hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra :=
    (⟨(CohCarrier.hdata N ⊤ S 𝒪 k hcomm θbar).op (CohCarrier.Gen.T ℓ hℓ hℓS hℓN),
        Algebra.subset_adjoin (Set.mem_range_self _)⟩ -
      ((ℓ : ↥(CohCarrier.hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra) + 1)) with hxB
  have hcoe : (xB : Module.End 𝒪 (CohCarrier.H1 N ⊤ 𝒪)) =
      CohCarrier.heckeTL N ⊤ 𝒪 ℓ - ((ℓ : Module.End 𝒪 (CohCarrier.H1 N ⊤ 𝒪)) + 1) := rfl
  have hxv : xB • v = CohCarrier.heckeT N ⊤ ℓ 𝒪 v - (ℓ + 1) • v := by
    change (xB : Module.End 𝒪 (CohCarrier.H1 N ⊤ 𝒪)) v = _
    rw [hcoe, LinearMap.sub_apply, LinearMap.add_apply, Module.End.natCast_apply, Module.End.one_apply,
      CohCarrier.heckeTL_apply, succ_nsmul]
  change _ ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪
  rw [hxv, ModularCurve.Period.mem_parabolicHoms_iff]
  exact key

end S_CohCarrier_mem_parabolicHoms_of_mem_cornerSubmodule_H1_of_notMem
end P2MW
export P2MW.S_CohCarrier_mem_parabolicHoms_of_mem_cornerSubmodule_H1_of_notMem (solution)
