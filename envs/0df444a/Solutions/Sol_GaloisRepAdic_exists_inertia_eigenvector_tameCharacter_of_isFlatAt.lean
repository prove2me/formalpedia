-- Prove2me | solution 1 for GaloisRepAdic.exists_inertia_eigenvector_tameCharacter_of_isFlatAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/fe4df0fa-f88c-5efb-a358-1902b1f4dcf0

import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_HopfAlgebra_exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat
import Theorems.Thm_ValuationSubring_tameCharacter_conj_of_isFrobeniusAt
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Theorems.Thm_ValuationSubring_conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul
import Theorems.Thm_ValuationSubring_tameCharacter_pow_left
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Ring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_exists_inertia_eigenvector_tameCharacter_of_isFlatAt
p2m_attr_erase "instance" "instIsScalarTowerTensorProduct_definitions AlgebraicClosure.Rat.isGalois CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr"
p2m_attr_erase "simp" "ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj ExtCitation.LocalLevel.coe_smul_OO"

set_option autoImplicit false

open scoped Pointwise

open IsLocalRing Polynomial TensorProduct

section L0

variable {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
variable {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A)
variable (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)

local notation "κ" => IsLocalRing.ResidueField A
local notation "k" => IsLocalRing.ResidueField P
local notation "𝔪" => IsLocalRing.maximalIdeal A

include hP in
private theorem L03a_natCast_mem_maximal : (p : ↥P) ∈ IsLocalRing.maximalIdeal ↥P := by
  have h : ((p : ↥P) : AlgebraicClosure ℚ) ∈ P.nonunits := by simp at hP ⊢; exact hP
  exact P.coe_mem_nonunits_iff.mp h

private theorem L03b_isAlgClosed_residue_P : IsAlgClosed k :=
  P.isAlgClosed_residueField

include hp hP in
private theorem L03c_charP_residue_P : CharP k p := by
  rw [CharP.charP_iff_prime_eq_zero hp]
  have : ((p : ℕ) : k) = IsLocalRing.residue ↥P ((p : ℕ) : ↥P) := by simp
  rw [this]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (L03a_natCast_mem_maximal P hP)

include hp hpA in
private theorem L04a_charP_kappa : CharP κ p := by
  have hp0 : (p : κ) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A)]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hpA
  rw [← CharP.ringChar_of_prime_eq_zero hp hp0]; exact ringChar.charP _

include hp hpA hP in
private noncomputable def L04_psiK (hfin : Finite κ) : κ →+* k := by
  letI : Fact p.Prime := ⟨hp⟩
  letI := L04a_charP_kappa (A := A) hp hpA
  letI := L03c_charP_residue_P hp P hP
  letI := ZMod.algebra κ p
  letI := ZMod.algebra k p
  haveI : Module.Finite (ZMod p) κ := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (ZMod p) κ := Algebra.IsAlgebraic.of_finite _ _
  letI : IsAlgClosed k := L03b_isAlgClosed_residue_P P
  exact (IsAlgClosed.lift (R := ZMod p) (M := k) : κ →ₐ[ZMod p] k).toRingHom

private noncomputable def L02_qEquiv :
    (ρ.V ⧸ ((𝔪) • (⊤ : Submodule A ρ.V))) ≃ₗ[A] (κ) ⊗[A] ρ.V :=
  (TensorProduct.quotTensorEquivQuotSMul ρ.V (𝔪)).symm

private theorem L02_qEquiv_equivariant
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ.V ⧸ ((𝔪) • (⊤ : Submodule A ρ.V))) :
    L02_qEquiv ρ (ρ.levelAction 𝔪 σ v) = (ρ.ρ σ).baseChange κ (L02_qEquiv ρ v) := by
  induction v using Submodule.Quotient.induction_on with
  | H x =>

    show L02_qEquiv ρ (Submodule.mapQ _ _ (ρ.ρ σ) _ (Submodule.Quotient.mk x))
       = (ρ.ρ σ).baseChange κ (L02_qEquiv ρ (Submodule.Quotient.mk x))
    rw [Submodule.mapQ_apply]
    show (TensorProduct.quotTensorEquivQuotSMul ρ.V 𝔪).symm (Submodule.Quotient.mk (ρ.ρ σ x))
       = (ρ.ρ σ).baseChange κ ((TensorProduct.quotTensorEquivQuotSMul ρ.V 𝔪).symm
            (Submodule.Quotient.mk x))
    rw [TensorProduct.quotTensorEquivQuotSMul_symm_mk, TensorProduct.quotTensorEquivQuotSMul_symm_mk]
    exact (LinearMap.baseChange_tmul (A := κ) (ρ.ρ σ) (1 : κ) x).symm

section PackageRaw

variable (ψk : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField P)

variable {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
variable (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
    (ρ.V ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A ρ.V))))

private noncomputable def L0_F :
    WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →
      (ρ.residual.baseChangeAlong ψk).V :=
  letI : Algebra κ k := ψk.toAlgebra
  fun x => (1 : k) ⊗ₜ[κ] (L02_qEquiv ρ (e x))

private theorem L0_hFmul
    (hemul : ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      e (f * g) = e f + e g)
    (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :
    L0_F ρ P ψk e (f * g) = L0_F ρ P ψk e f + L0_F ρ P ψk e g := by
  letI : Algebra κ k := ψk.toAlgebra
  show (1 : k) ⊗ₜ[κ] (L02_qEquiv ρ (e (f * g)))
     = (1 : k) ⊗ₜ[κ] (L02_qEquiv ρ (e f)) + (1 : k) ⊗ₜ[κ] (L02_qEquiv ρ (e g))
  rw [hemul, map_add, TensorProduct.tmul_add]

private theorem L0_hFequiv
    (heequiv : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → e g = ρ.levelAction (IsLocalRing.maximalIdeal A) σ (e f))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ))
    (hgsf : ∀ h : H, g h = σ (f h)) :
    L0_F ρ P ψk e g = (ρ.residual.baseChangeAlong ψk).ρ σ (L0_F ρ P ψk e f) := by
  letI : Algebra κ k := ψk.toAlgebra
  show (1 : k) ⊗ₜ[κ] (L02_qEquiv ρ (e g))
     = (ρ.residual.ρ σ).baseChange k ((1 : k) ⊗ₜ[κ] (L02_qEquiv ρ (e f)))
  rw [heequiv σ f g hgsf, L02_qEquiv_equivariant ρ σ, LinearMap.baseChange_tmul]
  rfl

section hMp

include hpA in
private theorem L0_nsmul_eq_zero_quot
    (v : ρ.V ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A ρ.V))) :
    (p : ℕ) • v = 0 := by
  rw [← Nat.cast_smul_eq_nsmul A p v]
  induction v using Submodule.Quotient.induction_on with
  | H x =>
    show (p : A) • Submodule.Quotient.mk x = (0 : ρ.V ⧸ (IsLocalRing.maximalIdeal A • ⊤))
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hpA Submodule.mem_top

private theorem L0_e_one_eq_zero
    (hemul : ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      e (f * g) = e f + e g) : e 1 = 0 :=
  add_left_cancel (a := e 1) (show e 1 + e 1 = e 1 + 0 by rw [add_zero, ← hemul 1 1, one_mul])

private theorem L0_e_pow
    (hemul : ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      e (f * g) = e f + e g)
    (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) (n : ℕ) :
    e (f ^ n) = n • e f := by
  induction n with
  | zero => rw [pow_zero, L0_e_one_eq_zero ρ e hemul, zero_smul]
  | succ n ih => rw [pow_succ, hemul, ih, succ_nsmul]

include hpA in
private theorem L0_hMp
    (hemul : ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      e (f * g) = e f + e g)
    (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) : f ^ p = 1 :=
  e.injective (by
    rw [L0_e_pow ρ e hemul, L0_e_one_eq_zero ρ e hemul, L0_nsmul_eq_zero_quot ρ hpA])

end hMp

private theorem L0_hFne : ∃ x, L0_F ρ P ψk e x ≠ 0 := by
  letI : Algebra κ k := ψk.toAlgebra
  letI : IsAlgClosed k := L03b_isAlgClosed_residue_P P

  haveI : Nontrivial ρ.residual.V := by
    rw [← Module.finrank_pos_iff (R := κ), ρ.residual.finrank_eq]; decide
  obtain ⟨v0, hv0⟩ := exists_ne (0 : ρ.residual.V)

  haveI : FaithfulSMul κ k :=
    (faithfulSMul_iff_algebraMap_injective κ k).mpr ψk.injective
  haveI : Module.Flat κ ρ.residual.V := by infer_instance
  have hinj : Function.Injective (TensorProduct.mk κ k ρ.residual.V 1) :=
    Module.Flat.tensorProduct_mk_injective κ ρ.residual.V k
  refine ⟨e.symm ((L02_qEquiv ρ).symm v0), fun hF => hv0 ?_⟩
  simp only [L0_F, Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hF
  have := hinj (show TensorProduct.mk κ k ρ.residual.V 1 v0 = TensorProduct.mk κ k ρ.residual.V 1 0
    by rw [map_zero]; exact hF)
  simpa using this

end PackageRaw

end L0

section Dim2Glue

open Module Submodule

variable {k : Type} [Field k] {W : Type} [AddCommGroup W] [Module k W]

private theorem L0_dim2_linearIndependent {w w' : W} (hw : w ≠ 0)
    (hnc : ¬∃ x : k, w' = x • w) : LinearIndependent k ![w, w'] :=
  (LinearIndependent.pair_iff' hw).mpr (fun a ha => hnc ⟨a, ha.symm⟩)

private theorem L0_dim2_li {w w' : W} (hw : w ≠ 0) (hnc : ¬∃ x : k, w' = x • w)
    (x y : k) (h : x • w + y • w' = 0) : x = 0 ∧ y = 0 :=
  LinearIndependent.pair_iff.mp (L0_dim2_linearIndependent hw hnc) x y h

private theorem L0_dim2_span (hrank : finrank k W = 2)
    {w w' : W} (hw : w ≠ 0) (hnc : ¬∃ x : k, w' = x • w) (v : W) :
    ∃ x y : k, v = x • w + y • w' := by
  have hli := L0_dim2_linearIndependent hw hnc
  have hcard : Fintype.card (Fin 2) = finrank k W := by
    rw [Fintype.card_fin, hrank]
  have htop : span k (Set.range ![w, w']) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank hcard
  rw [Matrix.range_cons_cons_empty] at htop
  obtain ⟨a, b, hab⟩ := mem_span_pair.mp (htop ▸ Submodule.mem_top : v ∈ span k {w, w'})
  exact ⟨a, b, hab.symm⟩

end Dim2Glue

namespace RaynL2

private theorem pred_mul_geom_add_one {x : ℕ} (hx : 1 ≤ x) (s : ℕ) :
    (x - 1) * (∑ j ∈ Finset.range s, x ^ j) + 1 = x ^ s := by
  obtain ⟨q, rfl⟩ : ∃ q, x = q + 1 := ⟨x - 1, by omega⟩
  have hq : q + 1 - 1 = q := by omega
  rw [hq]
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ]
    calc q * ((∑ j ∈ Finset.range s, (q + 1) ^ j) + (q + 1) ^ s) + 1
        = (q * (∑ j ∈ Finset.range s, (q + 1) ^ j) + 1) + q * (q + 1) ^ s := by ring
      _ = (q + 1) ^ s + q * (q + 1) ^ s := by rw [ih]
      _ = (q + 1) ^ (s + 1) := by rw [pow_succ]; ring

private theorem digitSum_le_repunit {p s : ℕ} (D : Finset ℕ) (hD : ∀ j ∈ D, j < s) :
    (∑ j ∈ D, p ^ j) ≤ ∑ j ∈ Finset.range s, p ^ j :=
  Finset.sum_le_sum_of_subset (fun j hj => Finset.mem_range.mpr (hD j hj))

private theorem geom_sum_mod_of_dvd {p x t : ℕ} (hp : 2 ≤ p) (hx : p ∣ x) (ht : 1 ≤ t) :
    (∑ i ∈ Finset.range t, x ^ i) % p = 1 := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have hdvd : p ∣ ∑ i ∈ Finset.range t, x ^ (i + 1) :=
    Finset.dvd_sum fun i _ => hx.trans (dvd_pow_self x (Nat.succ_ne_zero i))
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, pow_zero, Nat.add_comm, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

private theorem digitSum_mod_p {p : ℕ} (hp : 2 ≤ p) (D : Finset ℕ) :
    (∑ j ∈ D, p ^ j) % p = 0 ∨ (∑ j ∈ D, p ^ j) % p = 1 := by
  by_cases h0 : 0 ∈ D
  · right
    rw [← Finset.add_sum_erase _ _ h0, pow_zero]
    have hdvd : p ∣ ∑ j ∈ D.erase 0, p ^ j :=
      Finset.dvd_sum fun j hj => dvd_pow_self p (Finset.ne_of_mem_erase hj)
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  · left
    have hdvd : p ∣ ∑ j ∈ D, p ^ j :=
      Finset.dvd_sum fun j hj => dvd_pow_self p (fun h => h0 (h ▸ hj))
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, Nat.mul_mod_right]

private theorem repunit_two_mul_eq (p t : ℕ) :
    ∑ j ∈ Finset.range (2 * t), p ^ j = (p + 1) * ∑ i ∈ Finset.range t, (p ^ 2) ^ i := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hstep : 2 * (t + 1) = 2 * t + 1 + 1 := by omega
    rw [hstep, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ,
      Nat.mul_add]
    have h1 : p ^ (2 * t) = (p ^ 2) ^ t := by rw [← pow_mul]
    have h2 : p ^ (2 * t + 1) = (p ^ 2) ^ t * p := by
      rw [← pow_mul, ← pow_succ]
    rw [h1, h2]; ring

private theorem sq_pow_mod_p_add_one {p : ℕ} (hp : 2 ≤ p) (t : ℕ) :
    ((p ^ 2) ^ t) % (p + 1) = 1 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  induction t with
  | zero => rw [pow_zero]; exact Nat.mod_eq_of_lt (by omega)
  | succ t ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    have hsq : (q + 2) ^ 2 = 1 + (q + 3) * (q + 1) := by ring
    rw [hsq, Nat.add_mul_mod_self_left]
    have h1 : (1 : ℕ) % (q + 2 + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1, Nat.one_mul, h1]

private theorem repunit_mod_p_add_one_of_odd {p s : ℕ} (hp : 2 ≤ p) (hs : s % 2 = 1) :
    (∑ j ∈ Finset.range s, p ^ j) % (p + 1) = 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
  rw [Finset.sum_range_succ, repunit_two_mul_eq p t]
  have h1 : p ^ (2 * t) = (p ^ 2) ^ t := by rw [← pow_mul]
  rw [h1, Nat.add_comm, Nat.add_mul_mod_self_left]
  exact sq_pow_mod_p_add_one hp t

private theorem digitSum_eq_zero_or_repunit_of_odd {p s : ℕ} (hp : 2 ≤ p) (hs : s % 2 = 1)
    (D : Finset ℕ) (hD : ∀ j ∈ D, j < s)
    (hcong : (p ^ 2 - 1) * (∑ j ∈ D, p ^ j) % (p ^ s - 1) = 0) :
    (∑ j ∈ D, p ^ j) = 0 ∨ (∑ j ∈ D, p ^ j) = ∑ j ∈ Finset.range s, p ^ j := by
  set n := ∑ j ∈ D, p ^ j with hn
  set R := ∑ j ∈ Finset.range s, p ^ j with hRdef
  have hgeom : (p - 1) * R + 1 = p ^ s := pred_mul_geom_add_one (by omega) s
  have hgeom2 : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
    have h1 : (q + 2) ^ 2 = q * q + 4 * q + 4 := by ring
    have h2 : (q + 2 - 1) * (q + 2 + 1) = q * q + 4 * q + 3 := by
      have : q + 2 - 1 = q + 1 := by omega
      rw [this]; ring
    omega
  have hdvd : (p ^ s - 1) ∣ (p ^ 2 - 1) * n := Nat.dvd_of_mod_eq_zero hcong
  have hps : p ^ s - 1 = (p - 1) * R := by omega
  rw [hps, hgeom2, Nat.mul_assoc] at hdvd
  have hdvd2 : R ∣ (p + 1) * n :=
    (Nat.mul_dvd_mul_iff_left (show 0 < p - 1 by omega)).mp hdvd
  have hcop : Nat.Coprime (p + 1) R := by
    unfold Nat.Coprime
    rw [Nat.gcd_rec, repunit_mod_p_add_one_of_odd hp hs]
    exact Nat.gcd_one_left _
  have hRn : R ∣ n := hcop.symm.dvd_of_dvd_mul_left hdvd2
  have hle : n ≤ R := digitSum_le_repunit D hD
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · exact Or.inl h0
  · exact Or.inr (Nat.le_antisymm hle (Nat.le_of_dvd hpos hRn))

private theorem digitSum_eq_mul_Q_of_even {p s : ℕ} (hp : 2 ≤ p) (hs : s % 2 = 0) (hs1 : 1 ≤ s)
    (D : Finset ℕ) (hD : ∀ j ∈ D, j < s)
    (hcong : (p ^ 2 - 1) * (∑ j ∈ D, p ^ j) % (p ^ s - 1) = 0) :
    ∃ u ∈ ({0, 1, p, p + 1} : Finset ℕ),
      (∑ j ∈ D, p ^ j) = u * ((p ^ s - 1) / (p ^ 2 - 1)) := by
  set n := ∑ j ∈ D, p ^ j with hn
  obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t := ⟨s / 2, by omega⟩
  have ht1 : 1 ≤ t := by omega
  have hp2 : 2 ≤ p ^ 2 := by
    have : p * p ≥ 2 * 2 := Nat.mul_le_mul (by omega) (by omega)
    calc 2 ≤ 2 * 2 := by omega
    _ ≤ p * p := this
    _ = p ^ 2 := (sq p).symm
  set Qt := ∑ i ∈ Finset.range t, (p ^ 2) ^ i with hQt
  have hgeom : (p ^ 2 - 1) * Qt + 1 = (p ^ 2) ^ t := pred_mul_geom_add_one (by omega) t
  have hpow : (p ^ 2) ^ t = p ^ (2 * t) := by rw [← pow_mul]
  have hfac : p ^ (2 * t) - 1 = (p ^ 2 - 1) * Qt := by omega
  have hQdef : (p ^ (2 * t) - 1) / (p ^ 2 - 1) = Qt := by
    rw [hfac]; exact Nat.mul_div_cancel_left Qt (by omega)
  have hdvd : (p ^ 2 - 1) * Qt ∣ (p ^ 2 - 1) * n := by
    rw [← hfac]; exact Nat.dvd_of_mod_eq_zero hcong
  have hQn : Qt ∣ n := (Nat.mul_dvd_mul_iff_left (show 0 < p ^ 2 - 1 by omega)).mp hdvd
  obtain ⟨m, hm⟩ := hQn
  have hQt1 : 1 ≤ Qt := by
    rcases Nat.eq_zero_or_pos Qt with h | h
    · exfalso
      rw [h, Nat.mul_zero] at hgeom
      have h2 : p ^ 2 ≤ (p ^ 2) ^ t := Nat.le_self_pow (by omega) _
      omega
    · exact h
  have hle : n ≤ (p + 1) * Qt := by
    have h := digitSum_le_repunit (p := p) D hD
    rwa [repunit_two_mul_eq p t] at h
  have hmle : m ≤ p + 1 := by
    by_contra hgt
    push Not at hgt
    have h1 : Qt * (p + 2) ≤ Qt * m := Nat.mul_le_mul_left Qt (by omega)
    have h2 : Qt * (p + 2) = (p + 1) * Qt + Qt := by ring
    omega
  have hQtmod : Qt % p = 1 := geom_sum_mod_of_dvd hp ⟨p, sq p⟩ ht1
  have hnm : n % p = m % p := by
    have h1 := Nat.mul_mod Qt m p
    rw [hQtmod, Nat.one_mul] at h1
    have h2 : m % p < p := Nat.mod_lt _ (by omega)
    rw [hm, h1, Nat.mod_eq_of_lt h2]
  have hmmod : m % p = 0 ∨ m % p = 1 := by
    have h := digitSum_mod_p hp D
    rw [← hn] at h
    omega
  have hmem : m ∈ ({0, 1, p, p + 1} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases Nat.lt_or_ge m p with hlt | hge
    · have h := Nat.mod_eq_of_lt hlt
      omega
    · omega
  refine ⟨m, hmem, ?_⟩
  rw [hQdef, hm]
  exact Nat.mul_comm Qt m

private theorem dvd_p_sq_sub_one_mul_of_dvd_p_mul {p s n : ℕ} (hp : p.Prime) (hs1 : 1 ≤ s)
    (hdvd : (p ^ s - 1) ∣ p * ((p - 1) * n)) :
    (p ^ s - 1) ∣ (p ^ 2 - 1) * n := by
  have hp2 : 2 ≤ p := hp.two_le
  have hgeom : (p - 1) * (∑ j ∈ Finset.range s, p ^ j) + 1 = p ^ s :=
    pred_mul_geom_add_one (by omega) s
  have hRmod : (∑ j ∈ Finset.range s, p ^ j) % p = 1 := geom_sum_mod_of_dvd hp2 dvd_rfl hs1
  have hm_eq : p ^ s - 1 = (p - 1) * (∑ j ∈ Finset.range s, p ^ j) := by omega
  have hpm : ¬ p ∣ (p ^ s - 1) := by
    rw [hm_eq]
    rintro ⟨c, hc⟩
    have e1 : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
    have h1 : ((p - 1) * (∑ j ∈ Finset.range s, p ^ j)) % p = p - 1 := by
      rw [Nat.mul_mod, hRmod, Nat.mul_one, e1, e1]
    have h2 : ((p - 1) * (∑ j ∈ Finset.range s, p ^ j)) % p = 0 := by
      rw [hc]; exact Nat.mul_mod_right p c
    omega
  have hcop : Nat.Coprime (p ^ s - 1) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm).symm
  have hstep : (p ^ s - 1) ∣ (p - 1) * n := hcop.dvd_of_dvd_mul_left hdvd
  have hgeom2 : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
    have h1 : (q + 2) ^ 2 = q * q + 4 * q + 4 := by ring
    have h2 : (q + 2 - 1) * (q + 2 + 1) = q * q + 4 * q + 3 := by
      have h3 : q + 2 - 1 = q + 1 := by omega
      rw [h3]; ring
    omega
  have heq : (p ^ 2 - 1) * n = (p + 1) * ((p - 1) * n) := by
    rw [hgeom2]; ring
  rw [heq]
  exact hstep.mul_left (p + 1)

private theorem eigenvector_translate {k : Type} [Field k] {W : Type} [AddCommGroup W]
    [Module k W] {G : Type} [Group G] (ρ : G →* Module.End k W)
    (I : Subgroup G) (φ : G) (hconjmem : ∀ σ ∈ I, φ * σ * φ⁻¹ ∈ I)
    (χ χ' : G → k) (w : W)
    (hw : ∀ σ ∈ I, ρ σ w = χ σ • w)
    (hχ2 : ∀ σ ∈ I, χ (φ * σ * φ⁻¹) = χ' σ) :
    ∀ σ ∈ I, ρ σ (ρ φ⁻¹ w) = χ' σ • ρ φ⁻¹ w := by
  intro σ hσ
  have hmem := hconjmem σ hσ
  have h1 : φ⁻¹ * (φ * σ * φ⁻¹) = σ * φ⁻¹ := by
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]
  calc ρ σ (ρ φ⁻¹ w) = (ρ σ * ρ φ⁻¹) w := rfl
    _ = ρ (σ * φ⁻¹) w := by rw [← map_mul]
    _ = ρ (φ⁻¹ * (φ * σ * φ⁻¹)) w := by rw [h1]
    _ = (ρ φ⁻¹ * ρ (φ * σ * φ⁻¹)) w := by rw [map_mul]
    _ = ρ φ⁻¹ (ρ (φ * σ * φ⁻¹) w) := rfl
    _ = ρ φ⁻¹ (χ (φ * σ * φ⁻¹) • w) := by rw [hw _ hmem]
    _ = χ (φ * σ * φ⁻¹) • ρ φ⁻¹ w := map_smul _ _ _
    _ = χ' σ • ρ φ⁻¹ w := by rw [hχ2 σ hσ]

private theorem eigenvalue_mem_pair {k : Type} [Field k] {W : Type} [AddCommGroup W]
    [Module k W] (T : Module.End k W) (w₁ w₂ w₃ : W) (a b c : k)
    (hli : ∀ x y : k, x • w₁ + y • w₂ = 0 → x = 0 ∧ y = 0)
    (hspan : ∀ v : W, ∃ x y : k, v = x • w₁ + y • w₂)
    (h1 : T w₁ = a • w₁) (h2 : T w₂ = b • w₂) (h3 : T w₃ = c • w₃) (hw3 : w₃ ≠ 0) :
    c = a ∨ c = b := by
  obtain ⟨x, y, hxy⟩ := hspan w₃
  have hL : T w₃ = (c * x) • w₁ + (c * y) • w₂ := by
    rw [h3, hxy, smul_add, smul_smul, smul_smul]
  have hR : T w₃ = (a * x) • w₁ + (b * y) • w₂ := by
    rw [hxy, map_add, map_smul, map_smul, h1, h2, smul_smul, smul_smul,
      mul_comm x a, mul_comm y b]
  have e : (c * x) • w₁ + (c * y) • w₂ = (a * x) • w₁ + (b * y) • w₂ := hL.symm.trans hR
  have hzero : (c * x - a * x) • w₁ + (c * y - b * y) • w₂ = 0 := by
    rw [sub_smul, sub_smul, ← add_sub_add_comm, sub_eq_zero]
    exact e
  obtain ⟨hx, hy⟩ := hli _ _ hzero
  rcases eq_or_ne x 0 with hx0 | hx0
  · rcases eq_or_ne y 0 with hy0 | hy0
    · exact absurd (by rw [hxy, hx0, hy0, zero_smul, zero_smul, add_zero]) hw3
    · right
      have h' : (c - b) * y = 0 := by rw [sub_mul]; exact hy
      rcases mul_eq_zero.mp h' with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hy0
  · left
    have h' : (c - a) * x = 0 := by rw [sub_mul]; exact hx
    rcases mul_eq_zero.mp h' with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hx0

private theorem eigenvalue_eq_of_collinear {k : Type} [Field k] {W : Type} [AddCommGroup W]
    [Module k W] (T : Module.End k W) (w w' : W) (c d : k) (x : k)
    (hcol : w' = x • w) (hw' : w' ≠ 0)
    (hTw : T w = c • w) (hTw' : T w' = d • w') :
    d = c := by
  have hx0 : x ≠ 0 := fun h => hw' (by rw [hcol, h, zero_smul])
  have hwne : w ≠ 0 := fun h => hw' (by rw [hcol, h, smul_zero])
  have hL : T w' = (x * c) • w := by rw [hcol, map_smul, hTw, smul_smul]
  have hR : T w' = (d * x) • w := by rw [hTw', hcol, smul_smul]
  have h1 : (x * c - d * x) • w = 0 := by
    rw [sub_smul, ← hL, ← hR, sub_self]
  rcases smul_eq_zero.mp h1 with h | h
  · have h' : x * c = x * d := by
      have := sub_eq_zero.mp h
      rw [this, mul_comm]
    exact (mul_left_cancel₀ hx0 h').symm
  · exact absurd h hwne

private theorem modEq_of_pow_eq_pow {K : Type} [Field K] {ζ : K} {N : ℕ}
    (hprim : IsPrimitiveRoot ζ N) (hN : N ≠ 0) {a b : ℕ} (he : ζ ^ a = ζ ^ b) :
    b ≡ a [MOD N] := by
  obtain ⟨u, hueq⟩ := hprim.isUnit hN
  have heu : u ^ a = u ^ b := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hueq]; exact he)
  have h0 := (pow_eq_pow_iff_modEq.mp heu).symm
  rwa [← orderOf_units, hueq, ← hprim.eq_orderOf] at h0

private theorem exponent_congruence
    {p : ℕ} (hp : p.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    {W : Type} [AddCommGroup W] [Module (IsLocalRing.ResidueField P) W]
    (ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Module.End (IsLocalRing.ResidueField P) W)
    (hglue : ∀ w w' : W, w ≠ 0 → (¬ ∃ x : IsLocalRing.ResidueField P, w' = x • w) →
      (∀ x y : IsLocalRing.ResidueField P, x • w + y • w' = 0 → x = 0 ∧ y = 0) ∧
      (∀ v : W, ∃ x y : IsLocalRing.ResidueField P, v = x • w + y • w'))
    {s : ℕ} (hs1 : 1 ≤ s) {π₀ : AlgebraicClosure ℚ}
    (hπ₀ : π₀ ^ (p ^ s - 1) = (p : AlgebraicClosure ℚ))
    (n : ℕ) (w : W) (hw : w ≠ 0)
    (heig : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ' σ w = P.tameCharacter π₀ σ ^ n • w) :
    (p ^ s - 1) ∣ (p ^ 2 - 1) * n := by
  have hp2 : 2 ≤ p := hp.two_le
  have hps1 : 1 ≤ p ^ s := Nat.one_le_pow _ _ (by omega)
  have hps2 : 2 ≤ p ^ s := by
    calc 2 ≤ p := hp2
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ s := Nat.pow_le_pow_right (by omega) hs1
  have hm : 0 < p ^ s - 1 := by omega

  have hpm : ¬ p ∣ (p ^ s - 1) := by
    have hgeomR : (p - 1) * (∑ j ∈ Finset.range s, p ^ j) + 1 = p ^ s :=
      pred_mul_geom_add_one (by omega) s
    have hRmod : (∑ j ∈ Finset.range s, p ^ j) % p = 1 := geom_sum_mod_of_dvd hp2 dvd_rfl hs1
    have hm_eq : p ^ s - 1 = (p - 1) * (∑ j ∈ Finset.range s, p ^ j) := by omega
    rw [hm_eq]
    rintro ⟨c, hc⟩
    have e1 : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
    have h1 : ((p - 1) * (∑ j ∈ Finset.range s, p ^ j)) % p = p - 1 := by
      rw [Nat.mul_mod, hRmod, Nat.mul_one, e1, e1]
    have h2 : ((p - 1) * (∑ j ∈ Finset.range s, p ^ j)) % p = 0 := by
      rw [hc]; exact Nat.mul_mod_right p c
    omega

  obtain ⟨σ₀, hσ₀I, hσ₀prim⟩ :=
    P.exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter hp hP hpm hπ₀
  obtain ⟨φ, hφ⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hp P hP

  have hφinv : φ⁻¹ • P = P := by
    have h1 : φ⁻¹ ∈ P.decompositionSubgroup ℚ := inv_mem hφ.mem_decompositionSubgroup
    exact MulAction.mem_stabilizer_iff.mp h1
  have hconjmem : ∀ σ ∈ P.inertiaSubgroupIn ℚ, φ * σ * φ⁻¹ ∈ P.inertiaSubgroupIn ℚ := by
    intro σ hσ
    have h1 : σ ∈ ((φ⁻¹) • P).inertiaSubgroupIn ℚ := by rw [hφinv]; exact hσ
    have h2 := P.conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul φ⁻¹ h1
    rwa [inv_inv] at h2

  have hT3 : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      P.tameCharacter π₀ (φ * σ * φ⁻¹) = P.tameCharacter π₀ σ ^ p := fun σ hσ =>
    P.tameCharacter_conj_of_isFrobeniusAt π₀ hm hπ₀ hφ hσ

  have hw'eig := eigenvector_translate ρ' (P.inertiaSubgroupIn ℚ) φ hconjmem
    (fun σ => P.tameCharacter π₀ σ ^ n) (fun σ => (P.tameCharacter π₀ σ ^ n) ^ p) w heig
    (fun σ hσ => by rw [hT3 σ hσ, pow_right_comm])

  have hinv : ∀ v : W, ρ' φ⁻¹ v = 0 → v = 0 := by
    intro v h0
    have h1 : ρ' φ (ρ' φ⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [h0, map_zero] at h1
    exact h1.symm
  have hw'ne : ρ' φ⁻¹ w ≠ 0 := fun h0 => hw (hinv w h0)

  by_cases hcol : ∃ x : IsLocalRing.ResidueField P, ρ' φ⁻¹ w = x • w
  ·
    obtain ⟨x, hx⟩ := hcol
    have hd := eigenvalue_eq_of_collinear (ρ' σ₀) w (ρ' φ⁻¹ w)
      (P.tameCharacter π₀ σ₀ ^ n) ((P.tameCharacter π₀ σ₀ ^ n) ^ p) x hx hw'ne
      (heig σ₀ hσ₀I) (hw'eig σ₀ hσ₀I)
    have he : P.tameCharacter π₀ σ₀ ^ (n * p) = P.tameCharacter π₀ σ₀ ^ n := by
      rw [pow_mul]; exact hd
    have hmodeq : n ≡ n * p [MOD p ^ s - 1] :=
      modEq_of_pow_eq_pow hσ₀prim
        (Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) (by omega))) he
    have h1 := (Nat.modEq_iff_dvd' (Nat.le_mul_of_pos_right n (by omega))).mp hmodeq
    have h2 : n * p - n = (p - 1) * n := by
      rw [Nat.mul_comm n p, Nat.sub_one_mul]
    rw [h2] at h1
    exact dvd_p_sq_sub_one_mul_of_dvd_p_mul hp hs1 (h1.mul_left p)
  ·
    obtain ⟨hli, hspan⟩ := hglue w (ρ' φ⁻¹ w) hw hcol
    have hw''eig := eigenvector_translate ρ' (P.inertiaSubgroupIn ℚ) φ hconjmem
      (fun σ => (P.tameCharacter π₀ σ ^ n) ^ p)
      (fun σ => ((P.tameCharacter π₀ σ ^ n) ^ p) ^ p) (ρ' φ⁻¹ w) hw'eig
      (fun σ hσ => by rw [hT3 σ hσ, pow_right_comm (P.tameCharacter π₀ σ) p n])
    have hw''ne : ρ' φ⁻¹ (ρ' φ⁻¹ w) ≠ 0 := fun h0 => hw'ne (hinv _ h0)
    have hmem := eigenvalue_mem_pair (ρ' σ₀) w (ρ' φ⁻¹ w) (ρ' φ⁻¹ (ρ' φ⁻¹ w))
      (P.tameCharacter π₀ σ₀ ^ n) ((P.tameCharacter π₀ σ₀ ^ n) ^ p)
      (((P.tameCharacter π₀ σ₀ ^ n) ^ p) ^ p) hli hspan
      (heig σ₀ hσ₀I) (hw'eig σ₀ hσ₀I) (hw''eig σ₀ hσ₀I) hw''ne
    rcases hmem with h | h
    ·
      have he : P.tameCharacter π₀ σ₀ ^ (n * p * p) = P.tameCharacter π₀ σ₀ ^ n := by
        rw [pow_mul, pow_mul]; exact h
      have hmodeq : n ≡ n * p * p [MOD p ^ s - 1] :=
        modEq_of_pow_eq_pow hσ₀prim
          (Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) (by omega))) he
      have h1 := (Nat.modEq_iff_dvd' (by
        calc n = n * 1 := (Nat.mul_one n).symm
        _ ≤ n * (p * p) := Nat.mul_le_mul_left n
              (Nat.pos_of_ne_zero (Nat.mul_ne_zero (by omega) (by omega)))
        _ = n * p * p := by rw [Nat.mul_assoc])).mp hmodeq
      have h2 : n * p * p - n = (p ^ 2 - 1) * n := by
        have h3 : n * p * p = n * p ^ 2 := by rw [Nat.mul_assoc, ← sq]
        rw [h3, Nat.mul_comm n (p ^ 2), Nat.sub_one_mul]
      rw [h2] at h1
      exact h1
    ·
      have he : P.tameCharacter π₀ σ₀ ^ (n * p * p) = P.tameCharacter π₀ σ₀ ^ (n * p) := by
        rw [pow_mul, pow_mul]; exact h
      have hmodeq : n * p ≡ n * p * p [MOD p ^ s - 1] :=
        modEq_of_pow_eq_pow hσ₀prim
          (Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) (by omega))) he
      have h1 := (Nat.modEq_iff_dvd' (Nat.le_mul_of_pos_right (n * p) (by omega))).mp hmodeq
      have h2 : n * p * p - n * p = p * ((p - 1) * n) := by
        have ha : p * ((p - 1) * n) = (p - 1) * (n * p) := by ring
        have hb : (p - 1) * (n * p) = p * (n * p) - n * p := Nat.sub_one_mul p (n * p)
        have hc : p * (n * p) = n * p * p := by ring
        rw [ha, hb, hc]
      rw [h2] at h1
      exact dvd_p_sq_sub_one_mul_of_dvd_p_mul hp hs1 h1

end RaynL2

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (hflat : ρ.IsFlatAt p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    {π : AlgebraicClosure ℚ} (hπ : π ^ (p ^ 2 - 1) = p) :
    ∃ (ψk : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField P)
      (v : (ρ.residual.baseChangeAlong ψk).V), v ≠ 0 ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ, (ρ.residual.baseChangeAlong ψk).ρ σ v = v) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (ρ.residual.baseChangeAlong ψk).ρ σ v = P.tameCharacter π σ • v) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (ρ.residual.baseChangeAlong ψk).ρ σ v = P.tameCharacter π σ ^ p • v) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (ρ.residual.baseChangeAlong ψk).ρ σ v = P.tameCharacter π σ ^ (p + 1) • v)) := by
  have hple : 2 ≤ p := hp.two_le

  obtain ⟨H, instH1, instH2, hFinH, hFlatH, hCocommH, e, hemul, heequiv⟩ :=
    hflat.2 (IsLocalRing.maximalIdeal A) hflat.1
  letI := instH1
  letI := instH2
  haveI := hFinH
  haveI := hFlatH
  haveI := hCocommH
  set ψk : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField P :=
    L04_psiK hp hpA P hP hflat.1 with hψkdef
  refine ⟨ψk, ?_⟩

  obtain ⟨s, hs1, hwall⟩ :=
    HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat hp hp2
      (L0_hMp ρ hpA e hemul) P hP ((ρ.residual.baseChangeAlong ψk).V)
      (fun σ => (ρ.residual.baseChangeAlong ψk).ρ σ) (L0_F ρ P ψk e)
      (L0_hFmul ρ P ψk e hemul)
      (fun σ _hσ f g hgsf => L0_hFequiv ρ P ψk e heequiv σ f g hgsf)
      (L0_hFne ρ P ψk e)

  have hglue : ∀ w w' : (ρ.residual.baseChangeAlong ψk).V, w ≠ 0 →
      (¬ ∃ x : IsLocalRing.ResidueField P, w' = x • w) →
      (∀ x y : IsLocalRing.ResidueField P, x • w + y • w' = 0 → x = 0 ∧ y = 0) ∧
      (∀ v : (ρ.residual.baseChangeAlong ψk).V,
        ∃ x y : IsLocalRing.ResidueField P, v = x • w + y • w') := by
    intro w w' hw hnc
    exact ⟨fun x y h => L0_dim2_li hw hnc x y h,
      fun v => L0_dim2_span (ρ.residual.baseChangeAlong ψk).finrank_eq hw hnc v⟩
  have hps2 : 2 ≤ p ^ s := by
    calc 2 ≤ p := hple
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ s := Nat.pow_le_pow_right (by omega) hs1
  rcases Nat.even_or_odd s with hse | hso
  ·
    obtain ⟨t, hst⟩ := hse
    have ht1 : 1 ≤ t := by omega
    have hp21 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hgeomQ : (p ^ 2 - 1) * (∑ i ∈ Finset.range t, (p ^ 2) ^ i) + 1 = (p ^ 2) ^ t :=
      RaynL2.pred_mul_geom_add_one hp21 t
    have hp2t : p ^ 2 ≤ (p ^ 2) ^ t := Nat.le_self_pow (by omega) _
    have hp24 : 4 ≤ p ^ 2 := by
      have h1 : 2 * 2 ≤ p * p := Nat.mul_le_mul hple hple
      have h2 : p * p = p ^ 2 := (sq p).symm
      omega
    have hQ1 : 0 < ∑ i ∈ Finset.range t, (p ^ 2) ^ i := by
      have ht1 : 1 ≤ t := by omega
      calc (0 : ℕ) < 1 := by omega
        _ = ∑ i ∈ Finset.range 1, (p ^ 2) ^ i := by simp
        _ ≤ ∑ i ∈ Finset.range t, (p ^ 2) ^ i :=
            Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr ht1)
    obtain ⟨π₀, hπ₀Q⟩ :=
      IsAlgClosed.exists_pow_nat_eq π (n := ∑ i ∈ Finset.range t, (p ^ 2) ^ i) hQ1
    have hpowst : (p ^ 2) ^ t = p ^ s := by rw [← pow_mul, hst, Nat.two_mul]
    have hmulQ : p ^ s - 1 = (∑ i ∈ Finset.range t, (p ^ 2) ^ i) * (p ^ 2 - 1) := by
      have hc : (∑ i ∈ Finset.range t, (p ^ 2) ^ i) * (p ^ 2 - 1) =
          (p ^ 2 - 1) * (∑ i ∈ Finset.range t, (p ^ 2) ^ i) := Nat.mul_comm _ _
      omega
    have hπ₀ : π₀ ^ (p ^ s - 1) = (p : AlgebraicClosure ℚ) := by
      rw [hmulQ, pow_mul, hπ₀Q, hπ]
    obtain ⟨D, hD, w, hwne, heig⟩ := hwall π₀ hπ₀
    have hdvd := RaynL2.exponent_congruence hp P hP
      ((ρ.residual.baseChangeAlong ψk).ρ) hglue hs1 hπ₀ (∑ j ∈ D, p ^ j) w hwne heig
    have hcong : (p ^ 2 - 1) * (∑ j ∈ D, p ^ j) % (p ^ s - 1) = 0 := by
      obtain ⟨c, hc⟩ := hdvd
      rw [hc]
      exact Nat.mul_mod_right _ c
    obtain ⟨u, humem, hueq⟩ :=
      RaynL2.digitSum_eq_mul_Q_of_even hple (by omega) hs1 D hD hcong
    have hdiv : (p ^ s - 1) / (p ^ 2 - 1) = ∑ i ∈ Finset.range t, (p ^ 2) ^ i := by
      rw [hmulQ, Nat.mul_comm]
      exact Nat.mul_div_cancel_left _ (by omega)
    have hneq : (∑ j ∈ D, p ^ j) = u * ∑ i ∈ Finset.range t, (p ^ 2) ^ i := by
      rw [hueq, hdiv]
    have hchar : ∀ σ', P.tameCharacter π₀ σ' ^ (∑ j ∈ D, p ^ j) =
        P.tameCharacter π σ' ^ u := by
      intro σ'
      rw [hneq, Nat.mul_comm u, pow_mul, ← ValuationSubring.tameCharacter_pow_left, hπ₀Q]
    simp only [Finset.mem_insert, Finset.mem_singleton] at humem
    rcases humem with h0 | h1 | hP' | hP1
    · exact ⟨w, hwne, Or.inl (fun σ hσ => by
        rw [heig σ hσ, hchar σ, h0, pow_zero, one_smul])⟩
    · exact ⟨w, hwne, Or.inr (Or.inl (fun σ hσ => by
        rw [heig σ hσ, hchar σ, h1, pow_one]))⟩
    · exact ⟨w, hwne, Or.inr (Or.inr (Or.inl (fun σ hσ => by
        rw [heig σ hσ, hchar σ, hP'])))⟩
    · exact ⟨w, hwne, Or.inr (Or.inr (Or.inr (fun σ hσ => by
        rw [heig σ hσ, hchar σ, hP1])))⟩
  ·
    have hgeomR : (p - 1) * (∑ j ∈ Finset.range s, p ^ j) + 1 = p ^ s :=
      RaynL2.pred_mul_geom_add_one (by omega) s
    have hR1 : 0 < ∑ j ∈ Finset.range s, p ^ j := by
      calc (0 : ℕ) < 1 := by omega
        _ = ∑ j ∈ Finset.range 1, p ^ j := by simp
        _ ≤ ∑ j ∈ Finset.range s, p ^ j :=
            Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hs1)
    obtain ⟨π₀, hπ₀R⟩ :=
      IsAlgClosed.exists_pow_nat_eq (π ^ (p + 1)) (n := ∑ j ∈ Finset.range s, p ^ j) hR1
    have hexp : (p + 1) * (p - 1) = p ^ 2 - 1 := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
      have h1 : (q + 2) ^ 2 = q * q + 4 * q + 4 := by ring
      have h2 : (q + 2 + 1) * (q + 2 - 1) = q * q + 4 * q + 3 := by
        have h3 : q + 2 - 1 = q + 1 := by omega
        rw [h3]; ring
      omega
    have hmulR : p ^ s - 1 = (∑ j ∈ Finset.range s, p ^ j) * (p - 1) := by
      have hc : (∑ j ∈ Finset.range s, p ^ j) * (p - 1) =
          (p - 1) * (∑ j ∈ Finset.range s, p ^ j) := Nat.mul_comm _ _
      omega
    have hπ₀ : π₀ ^ (p ^ s - 1) = (p : AlgebraicClosure ℚ) := by
      rw [hmulR, pow_mul, hπ₀R, ← pow_mul, hexp, hπ]
    obtain ⟨D, hD, w, hwne, heig⟩ := hwall π₀ hπ₀
    have hdvd := RaynL2.exponent_congruence hp P hP
      ((ρ.residual.baseChangeAlong ψk).ρ) hglue hs1 hπ₀ (∑ j ∈ D, p ^ j) w hwne heig
    have hcong : (p ^ 2 - 1) * (∑ j ∈ D, p ^ j) % (p ^ s - 1) = 0 := by
      obtain ⟨c, hc⟩ := hdvd
      rw [hc]
      exact Nat.mul_mod_right _ c
    have hsodd : s % 2 = 1 := Nat.odd_iff.mp hso
    rcases RaynL2.digitSum_eq_zero_or_repunit_of_odd hple hsodd D hD hcong with hn0 | hnR
    · exact ⟨w, hwne, Or.inl (fun σ hσ => by
        rw [heig σ hσ, hn0, pow_zero, one_smul])⟩
    · refine ⟨w, hwne, Or.inr (Or.inr (Or.inr (fun σ hσ => ?_)))⟩
      have hchar : P.tameCharacter π₀ σ ^ (∑ j ∈ D, p ^ j) =
          P.tameCharacter π σ ^ (p + 1) := by
        rw [hnR, ← ValuationSubring.tameCharacter_pow_left, hπ₀R,
          ValuationSubring.tameCharacter_pow_left]
      rw [heig σ hσ, hchar]

end S_GaloisRepAdic_exists_inertia_eigenvector_tameCharacter_of_isFlatAt
end P2MW
export P2MW.S_GaloisRepAdic_exists_inertia_eigenvector_tameCharacter_of_isFlatAt (solution)
