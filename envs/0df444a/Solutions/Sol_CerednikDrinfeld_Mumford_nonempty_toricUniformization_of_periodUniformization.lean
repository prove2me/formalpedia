-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.nonempty_toricUniformization_of_periodUniformization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/21c167ae-3199-576c-982c-822ab539539a

import Definitions.Def_CerednikDrinfeld_MumfordUniformization
import Definitions.Def_CerednikDrinfeld_ToricUniformization
import Theorems.Thm_CerednikDrinfeld_Mumford_PeriodDatum_U_divisible
import Theorems.Thm_CerednikDrinfeld_Mumford_PeriodDatum_exists_periodEquiv
import Theorems.Thm_CerednikDrinfeld_Mumford_PeriodDatum_period_adjoint_of_ord_Q
import Theorems.Thm_CerednikDrinfeld_Mumford_PeriodDatum_pi_surj_torsion
import Theorems.Thm_CerednikDrinfeld_Mumford_PeriodUniformization_exists_torsionEquiv_tameCharacter_kummerLaw
import Theorems.Thm_ValuationSubring_isAlgClosed_completion_of_liesOverPrime
import Theorems.Thm_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization
p2m_attr_erase "instance" "ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj ExtCitation.LocalLevel.coe_smul_OO"

set_option autoImplicit false

noncomputable section

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld.Mumford ModularCurve"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Mumford.PeriodUniformization DegeneracyData ribbonKernel ribbonGram HeckeData heckeKernelMap HeckeData.comm ToricUniformization Mumford.PeriodUniformization.exists_torsionEquiv_tameCharacter_kummerLaw Mumford.PeriodUniformization.frobenius_toric_and_frobenius_quot_of_torsionEquiv"
p2m_open "CerednikDrinfeld"
namespace Mumford
p2m_export "CerednikDrinfeld.Mumford" "PeriodDatum.precomp_apply PeriodUniformization PeriodDatum PeriodDatum.U_divisible PeriodDatum.exists_periodEquiv PeriodDatum.period_adjoint_of_ord_Q PeriodUniformization.exists_torsionEquiv_tameCharacter_kummerLaw PeriodUniformization.frobenius_toric_and_frobenius_quot_of_torsionEquiv"
p2m_open "CerednikDrinfeld.Mumford"

namespace PeriodDatum
p2m_export "CerednikDrinfeld.Mumford.PeriodDatum" "precomp precomp_apply HeckeAdjointable TorusPoints QL QL_apply periodLattice U π U_divisible exists_periodEquiv period_adjoint_of_ord_Q"
p2m_open "CerednikDrinfeld.Mumford.PeriodDatum"

variable {E V : Type} [Fintype E] [Fintype V] [DecidableEq V] {D : DegeneracyData E V} {H : HeckeData D}
  {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ} (P : PeriodDatum D K L ord)

private theorem _root_.CerednikDrinfeld.Mumford.PeriodDatum.mem_ker_pi_iff (u : ↥P.U) : u ∈ LinearMap.ker P.π ↔ (u : P.TorusPoints) ∈ P.periodLattice := by
  rw [LinearMap.mem_ker]
  exact Submodule.Quotient.mk_eq_zero P.periodLattice

p2m_export "CerednikDrinfeld.Mumford.PeriodDatum" "mem_ker_pi_iff"

theorem heckeKernelMap_comm (ℓ ℓ' : Nat.Primes) (z : ↥(ribbonKernel D)) :
    heckeKernelMap H ℓ (heckeKernelMap H ℓ' z) = heckeKernelMap H ℓ' (heckeKernelMap H ℓ z) := by
  apply Subtype.ext
  simp only [heckeKernelMap, LinearMap.coe_restrict_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  rw [(H.comm ℓ ℓ').eq]

private theorem _root_.CerednikDrinfeld.Mumford.PeriodDatum.precomp_mem_periodLattice (hadj : P.HeckeAdjointable H) (ℓ : Nat.Primes) {w : P.TorusPoints}
    (hw : w ∈ P.periodLattice) : P.precomp (heckeKernelMap H ℓ) w ∈ P.periodLattice := by
  obtain ⟨y, rfl⟩ := hw
  obtain ⟨y', hy'⟩ := hadj ℓ y
  refine ⟨y', ?_⟩
  apply LinearMap.ext
  intro z
  rw [precomp_apply, QL_apply, QL_apply, hy' z]

p2m_export "CerednikDrinfeld.Mumford.PeriodDatum" "precomp_mem_periodLattice"

private theorem _root_.CerednikDrinfeld.Mumford.PeriodDatum.precomp_mem_U (hadj : P.HeckeAdjointable H) (ℓ : Nat.Primes) {u : P.TorusPoints} (hu : u ∈ P.U) :
    P.precomp (heckeKernelMap H ℓ) u ∈ P.U := by
  rw [U, Submodule.mem_comap] at hu ⊢
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).mp hu
  refine (Submodule.mem_torsion_iff _).mpr ⟨a, ?_⟩
  rw [Submonoid.smul_def, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at ha ⊢
  rw [← map_smul]
  exact P.precomp_mem_periodLattice hadj ℓ ha

p2m_export "CerednikDrinfeld.Mumford.PeriodDatum" "precomp_mem_U"
end PeriodDatum

namespace PeriodUniformization
p2m_export "CerednikDrinfeld.Mumford.PeriodUniformization" "e_hecke P heckeAdj ord K e e_surj_torsion e_ker exists_torsionEquiv_tameCharacter_kummerLaw frobenius_toric_and_frobenius_quot_of_torsionEquiv"
p2m_open "CerednikDrinfeld.Mumford.PeriodUniformization"

variable {r : ℕ} [Fact r.Prime] {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
  {D : DegeneracyData E V} {H : HeckeData D}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
  {T : Type} [AddCommGroup T] {hecke : HeckeAlg →+* Module.End ℤ T}
  {gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T}
  (PU : PeriodUniformization r D H A hA T hecke gal)

private def _root_.CerednikDrinfeld.Mumford.PeriodUniformization.heckeUGen (ℓ : Nat.Primes) : Module.End ℤ ↥PU.P.U :=
  (PU.P.precomp (heckeKernelMap H ℓ)).restrict fun _ hu => PU.P.precomp_mem_U PU.heckeAdj ℓ hu

p2m_export "CerednikDrinfeld.Mumford.PeriodUniformization" "heckeUGen"
@[scoped simp] theorem coe_heckeUGen_apply (ℓ : Nat.Primes) (u : ↥PU.P.U) :
    ((PU.heckeUGen ℓ u : ↥PU.P.U) : PU.P.TorusPoints) = PU.P.precomp (heckeKernelMap H ℓ) (u : PU.P.TorusPoints) :=
  rfl

private theorem _root_.CerednikDrinfeld.Mumford.PeriodUniformization.heckeUGen_comm (ℓ ℓ' : Nat.Primes) : PU.heckeUGen ℓ * PU.heckeUGen ℓ' = PU.heckeUGen ℓ' * PU.heckeUGen ℓ := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  simp only [Module.End.mul_apply, coe_heckeUGen_apply, PeriodDatum.precomp_apply]
  rw [PeriodDatum.heckeKernelMap_comm]

p2m_export "CerednikDrinfeld.Mumford.PeriodUniformization" "heckeUGen_comm"
private theorem _root_.CerednikDrinfeld.Mumford.PeriodUniformization.isMulCommutative_adjoin_heckeUGen :
    IsMulCommutative (Algebra.adjoin ℤ (Set.range PU.heckeUGen)) :=
  Algebra.isMulCommutative_adjoin ℤ (by
    rintro _ ⟨ℓ, rfl⟩ _ ⟨ℓ', rfl⟩
    exact PU.heckeUGen_comm ℓ ℓ')

p2m_export "CerednikDrinfeld.Mumford.PeriodUniformization" "isMulCommutative_adjoin_heckeUGen"

@[reducible] private def _root_.CerednikDrinfeld.Mumford.PeriodUniformization.commRingAdjoin : CommRing ↥(Algebra.adjoin ℤ (Set.range PU.heckeUGen)) :=
  { (inferInstance : Ring ↥(Algebra.adjoin ℤ (Set.range PU.heckeUGen))) with
    mul_comm := PU.isMulCommutative_adjoin_heckeUGen.is_comm.comm }

p2m_export "CerednikDrinfeld.Mumford.PeriodUniformization" "commRingAdjoin"

private def _root_.CerednikDrinfeld.Mumford.PeriodUniformization.heckeUAux : HeckeAlg →ₐ[ℤ] (Algebra.adjoin ℤ (Set.range PU.heckeUGen) : Subalgebra ℤ (Module.End ℤ ↥PU.P.U)) :=
  letI : CommSemiring ↥(Algebra.adjoin ℤ (Set.range PU.heckeUGen)) := PU.commRingAdjoin.toCommSemiring
  MvPolynomial.aeval fun ℓ =>
    (⟨PU.heckeUGen ℓ, Algebra.subset_adjoin (Set.mem_range_self ℓ)⟩ : Algebra.adjoin ℤ (Set.range PU.heckeUGen))

p2m_export "CerednikDrinfeld.Mumford.PeriodUniformization" "heckeUAux"

private def _root_.CerednikDrinfeld.Mumford.PeriodUniformization.heckeU : HeckeAlg →+* Module.End ℤ ↥PU.P.U :=
  ((Algebra.adjoin ℤ (Set.range PU.heckeUGen)).val.comp PU.heckeUAux).toRingHom

p2m_export "CerednikDrinfeld.Mumford.PeriodUniformization" "heckeU"
theorem heckeUAux_heckeGen (ℓ : Nat.Primes) :
    PU.heckeUAux (heckeGen ℓ) = ⟨PU.heckeUGen ℓ, Algebra.subset_adjoin (Set.mem_range_self ℓ)⟩ := by
  letI : CommSemiring ↥(Algebra.adjoin ℤ (Set.range PU.heckeUGen)) := PU.commRingAdjoin.toCommSemiring
  unfold heckeUAux heckeGen
  exact MvPolynomial.aeval_X _ ℓ

theorem heckeU_apply (x : HeckeAlg) : PU.heckeU x = (PU.heckeUAux x : Module.End ℤ ↥PU.P.U) := rfl

theorem heckeU_heckeGen (ℓ : Nat.Primes) : PU.heckeU (heckeGen ℓ) = PU.heckeUGen ℓ := by
  rw [heckeU_apply, heckeUAux_heckeGen]

@[scoped simp] private theorem _root_.CerednikDrinfeld.Mumford.PeriodUniformization.coe_heckeU_heckeGen_apply (ℓ : Nat.Primes) (u : ↥PU.P.U) :
    ((PU.heckeU (heckeGen ℓ) u : ↥PU.P.U) : PU.P.TorusPoints) =
      PU.P.precomp (heckeKernelMap H ℓ) (u : PU.P.TorusPoints) := by
  rw [heckeU_heckeGen]
  rfl

p2m_export "CerednikDrinfeld.Mumford.PeriodUniformization" "coe_heckeU_heckeGen_apply"

private theorem _root_.CerednikDrinfeld.Mumford.PeriodUniformization.U_divisible (hC : ∀ n : ℕ, 0 < n → ∀ c : (A.valuation.Completion)ˣ, ∃ c' : (A.valuation.Completion)ˣ, c' ^ n = c) :
    ∀ u : ↥PU.P.U, ∀ n : ℕ, 0 < n → ∃ u' : ↥PU.P.U, n • u' = u :=
  PU.P.U_divisible fun x n hn => hC n hn x

p2m_export "CerednikDrinfeld.Mumford.PeriodUniformization" "U_divisible"
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 800000 in

private theorem _root_.CerednikDrinfeld.Mumford.PeriodUniformization.e_heckeU (x : HeckeAlg) : ∀ u : ↥PU.P.U, PU.e (PU.heckeU x u) = hecke x (PU.e u) := by
  induction x using MvPolynomial.induction_on with
  | C a =>
    intro u
    rw [eq_intCast MvPolynomial.C a, map_intCast PU.heckeU, map_intCast hecke, Module.End.intCast_apply,
      Module.End.intCast_apply, map_zsmul]
  | add f g hf hg =>
    intro u
    rw [PU.heckeU.map_add, hecke.map_add, LinearMap.add_apply, LinearMap.add_apply, PU.e.map_add, hf u, hg u]
  | mul_X f ℓ hf =>
    intro u
    rw [PU.heckeU.map_mul, hecke.map_mul, Module.End.mul_apply, Module.End.mul_apply, hf]
    congr 1
    have hu : PU.P.precomp (heckeKernelMap H ℓ) (u : PU.P.TorusPoints) ∈ PU.P.U :=
      PU.P.precomp_mem_U PU.heckeAdj ℓ u.2
    have h1 : PU.heckeU (MvPolynomial.X ℓ) u = ⟨PU.P.precomp (heckeKernelMap H ℓ) (u : PU.P.TorusPoints), hu⟩ :=
      Subtype.ext (PU.coe_heckeU_heckeGen_apply ℓ u)
    rw [h1]
    exact PU.e_hecke ℓ u hu

p2m_export "CerednikDrinfeld.Mumford.PeriodUniformization" "e_heckeU"

private theorem _root_.CerednikDrinfeld.Mumford.PeriodUniformization.e_surj_pTorsion {p : ℕ} (hp : 0 < p) (t : T) (ht : p • t = 0) : ∃ u : ↥PU.P.U, PU.e u = t := by
  have hfin : IsOfFinAddOrder t := isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨p, hp, ht⟩
  obtain ⟨u, hu⟩ := PU.e_surj_torsion t hfin
  exact ⟨u, hu⟩

p2m_export "CerednikDrinfeld.Mumford.PeriodUniformization" "e_surj_pTorsion"

private def _root_.CerednikDrinfeld.Mumford.PeriodUniformization.kerEquiv : ↥(LinearMap.ker PU.P.π) ≃+ ↥PU.e.ker where
  toFun u := ⟨(u : ↥PU.P.U), by
    rw [AddMonoidHom.mem_ker, PU.e_ker]
    exact (PU.P.mem_ker_pi_iff _).mp u.2⟩
  invFun u := ⟨(u : ↥PU.P.U), by
    rw [PU.P.mem_ker_pi_iff, ← PU.e_ker]
    exact u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

p2m_export "CerednikDrinfeld.Mumford.PeriodUniformization" "kerEquiv"

private def _root_.CerednikDrinfeld.Mumford.PeriodUniformization.periodEquiv : ↥(ribbonKernel D) ≃+ ↥PU.e.ker :=
  (PU.P.exists_periodEquiv.choose.toAddEquiv).trans PU.kerEquiv

p2m_export "CerednikDrinfeld.Mumford.PeriodUniformization" "periodEquiv"
private theorem _root_.CerednikDrinfeld.Mumford.PeriodUniformization.coe_periodEquiv (x : ↥(ribbonKernel D)) :
    (((PU.periodEquiv x : ↥PU.e.ker) : ↥PU.P.U) : PU.P.TorusPoints) = PU.P.QL x :=
  PU.P.exists_periodEquiv.choose_spec x

p2m_export "CerednikDrinfeld.Mumford.PeriodUniformization" "coe_periodEquiv"

private theorem _root_.CerednikDrinfeld.Mumford.PeriodUniformization.period_adjoint (ℓ : Nat.Primes) (x y y' : ↥(ribbonKernel D))
    (h : PU.heckeU (heckeGen ℓ) (PU.periodEquiv y : ↥PU.P.U) = (PU.periodEquiv y' : ↥PU.P.U)) :
    ribbonGram D (heckeKernelMap H ℓ x) y = ribbonGram D x y' := by
  apply PU.P.period_adjoint_of_ord_Q H ℓ x y y'
  intro z
  have h' := congrArg (fun v : ↥PU.P.U => (v : PU.P.TorusPoints) z) h
  simpa only [coe_heckeU_heckeGen_apply, PeriodDatum.precomp_apply, coe_periodEquiv] using h'

p2m_export "CerednikDrinfeld.Mumford.PeriodUniformization" "period_adjoint"
end PeriodUniformization
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld.Mumford.PeriodUniformization"

end Mumford
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld.Mumford.PeriodUniformization P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld.Mumford"
end CerednikDrinfeld
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld.Mumford.PeriodUniformization P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Mumford.PeriodUniformization DegeneracyData ribbonKernel ribbonGram HeckeData heckeKernelMap HeckeData.comm ToricUniformization Mumford.PeriodUniformization.exists_torsionEquiv_tameCharacter_kummerLaw Mumford.PeriodUniformization.frobenius_toric_and_frobenius_quot_of_torsionEquiv"
p2m_open "CerednikDrinfeld"
namespace Mumford
p2m_export "CerednikDrinfeld.Mumford" "PeriodDatum.precomp_apply PeriodUniformization PeriodDatum PeriodDatum.U_divisible PeriodDatum.exists_periodEquiv PeriodDatum.period_adjoint_of_ord_Q PeriodUniformization.exists_torsionEquiv_tameCharacter_kummerLaw PeriodUniformization.frobenius_toric_and_frobenius_quot_of_torsionEquiv"
p2m_open "CerednikDrinfeld.Mumford"

theorem exists_isPrimitiveRoot_units_completion {r : ℕ} (hr : r.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) (p : ℕ) [hp : Fact p.Prime] :
    ∃ ζ : (A.valuation.Completion)ˣ, IsPrimitiveRoot ζ p := by
  haveI := ValuationSubring.isAlgClosed_completion_of_liesOverPrime r hr A hA
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hdeg : (Polynomial.cyclotomic p A.valuation.Completion).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr hp.out.pos).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  have hprim : IsPrimitiveRoot z p := Polynomial.isRoot_cyclotomic_iff.mp hz
  refine ⟨(hprim.isUnit hp.out.ne_zero).unit, ?_⟩
  exact IsPrimitiveRoot.coe_units_iff.mp (by rw [IsUnit.unit_spec]; exact hprim)

namespace PeriodUniformization
p2m_export "CerednikDrinfeld.Mumford.PeriodUniformization" "e_hecke P heckeAdj ord K e e_surj_torsion e_ker exists_torsionEquiv_tameCharacter_kummerLaw frobenius_toric_and_frobenius_quot_of_torsionEquiv"
p2m_open "CerednikDrinfeld.Mumford.PeriodUniformization"

variable {r : ℕ} [Fact r.Prime] {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
  {D : DegeneracyData E V} {H : HeckeData D}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
  {T : Type} [AddCommGroup T] {hecke : HeckeAlg →+* Module.End ℤ T}
  {gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T}
  (PU : PeriodUniformization r D H A hA T hecke gal)

set_option maxHeartbeats 1600000 in
private theorem _root_.CerednikDrinfeld.Mumford.PeriodUniformization.torsion_hecke_of_spec {p : ℕ} [hp : Fact p.Prime]
    (ζ : (A.valuation.Completion)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (χ : ↥(Submodule.torsionBy ℤ ↥PU.P.U (p : ℤ)) ≃+ (↥(ribbonKernel D) →ₗ[ℤ] ZMod p))
    (hχ : ∀ (v : ↥(Submodule.torsionBy ℤ ↥PU.P.U (p : ℤ))) (z : ↥(ribbonKernel D)),
      Additive.toMul ((((v : ↥PU.P.U) : PU.P.TorusPoints) z)) = ζ ^ (χ v z).val)
    (ℓ : Nat.Primes) (v : ↥(Submodule.torsionBy ℤ ↥PU.P.U (p : ℤ)))
    (hv : PU.heckeU (heckeGen ℓ) (v : ↥PU.P.U) ∈ Submodule.torsionBy ℤ ↥PU.P.U (p : ℤ)) :
    χ ⟨PU.heckeU (heckeGen ℓ) (v : ↥PU.P.U), hv⟩ = (χ v) ∘ₗ heckeKernelMap H ℓ := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  apply LinearMap.ext
  intro z
  rw [LinearMap.comp_apply]
  apply ZMod.val_injective p
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [← hχ ⟨PU.heckeU (heckeGen ℓ) (v : ↥PU.P.U), hv⟩ z, ← hχ v (heckeKernelMap H ℓ z)]
  congr 1
  have h1 : (((⟨PU.heckeU (heckeGen ℓ) (v : ↥PU.P.U), hv⟩ : ↥(Submodule.torsionBy ℤ ↥PU.P.U (p : ℤ))) :
      ↥PU.P.U) : PU.P.TorusPoints) = PU.P.precomp (heckeKernelMap H ℓ) ((v : ↥PU.P.U) : PU.P.TorusPoints) :=
    PU.coe_heckeU_heckeGen_apply ℓ (v : ↥PU.P.U)
  rw [h1, PeriodDatum.precomp_apply]

p2m_export "CerednikDrinfeld.Mumford.PeriodUniformization" "torsion_hecke_of_spec"
end PeriodUniformization
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld.Mumford.PeriodUniformization P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld"
end Mumford
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld.Mumford.PeriodUniformization P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld"
end CerednikDrinfeld
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld.Mumford.PeriodUniformization P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld"

open _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld _root_.CerednikDrinfeld.Mumford _root_.P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.CerednikDrinfeld.Mumford ModularCurve in
set_option maxHeartbeats 3200000 in
theorem solution
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hpr : p ≠ r)
    {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} {H : HeckeData D}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
    (hC : ∀ n : ℕ, 0 < n → ∀ c : (A.valuation.Completion)ˣ, ∃ c' : (A.valuation.Completion)ˣ, c' ^ n = c)
    {T : Type} [AddCommGroup T] {hecke : HeckeAlg →+* Module.End ℤ T}
    {gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T}
    (PU : PeriodUniformization r D H A hA T hecke gal) :
    Nonempty (ToricUniformization p r D H A hA T hecke gal) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := CerednikDrinfeld.Mumford.exists_isPrimitiveRoot_units_completion Fact.out A hA p
  obtain ⟨χ, hχ, tame, htame, hkummer⟩ :=
    CerednikDrinfeld.Mumford.PeriodUniformization.exists_torsionEquiv_tameCharacter_kummerLaw hpr PU ζ hζ
  obtain ⟨hfrob₁, hfrob₂⟩ :=
    CerednikDrinfeld.Mumford.PeriodUniformization.frobenius_toric_and_frobenius_quot_of_torsionEquiv hpr PU ζ hζ χ hχ
  refine ⟨{ U := ↥PU.P.U
            instAddCommGroupU := inferInstance
            heckeU := PU.heckeU
            divisible := PU.U_divisible hC
            π := PU.e
            π_hecke := fun x u => PU.e_heckeU x u
            π_surj_torsion := fun t ht => PU.e_surj_pTorsion (Fact.out : p.Prime).pos t ht
            periodEquiv := PU.periodEquiv
            period_adjoint := fun ℓ x y y' h => PU.period_adjoint ℓ x y y' h
            torsionEquiv := χ
            torsion_hecke := fun ℓ v hv => PU.torsion_hecke_of_spec ζ hζ χ hχ ℓ v hv
            tame := tame
            tame_surjective := htame
            kummer := ?_
            frob_toric := hfrob₁
            frob_quot := ?_ }⟩
  · intro σ u x hux
    have hux' : (p : ℤ) • (u : PU.P.TorusPoints) = PU.P.QL x := by
      rw [← PU.coe_periodEquiv x, ← hux]; rfl
    exact hkummer σ u x hux'
  · intro φ hφ u x hux
    have hux' : (p : ℤ) • (u : PU.P.TorusPoints) = PU.P.QL x := by
      rw [← PU.coe_periodEquiv x, ← hux]; rfl
    have hu : PU.P.precomp (heckeKernelMap H ⟨r, Fact.out⟩) (u : PU.P.TorusPoints) ∈ PU.P.U :=
      PU.P.precomp_mem_U PU.heckeAdj ⟨r, Fact.out⟩ u.2
    obtain ⟨v, hv0, hv⟩ := hfrob₂ φ hφ u x hux' hu
    refine ⟨v, hv0, hv.trans ?_⟩
    congr 2
    exact Subtype.ext (PU.coe_heckeU_heckeGen_apply ⟨r, Fact.out⟩ u).symm

end
end S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization (solution)
