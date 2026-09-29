-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.mem_map_conj_of_mem_awayUnits_of_exists_pow_smul_star_mul_mul_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ad7fcd5a-bbdf-5bfb-874e-d5d0ee7276e6

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_QuaternionAlgebra_exists_pow_smul_mem_of_finiteAdeleEvalAt_eq_tmul_of_mul_inv_mem_primeHeckeSet
import Theorems.Thm_CerednikDrinfeld_CosetGraph_exists_nrd_mul_pow_eq_pow_of_mem_awayUnits
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_relIndex_eq_of_isMaximalOrder_of_le
import Theorems.Thm_QuaternionAlgebra_IsOrder_star_mem_and_exists_int_trd_nrd
import Theorems.Thm_CerednikDrinfeld_CosetGraph_mem_awayUnits_iff_exists_pow_smul_mem_of_forall_localBox_eq
import Theorems.Thm_CerednikDrinfeld_exists_mem_forall_pow_smul_mul_mul_star_ne_smul_of_mem_levelHeckeUSet_meetOrder_of_dvd
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_forall_exists_pow_smul_star_mul_mul_eq_smul_of_forall_pow_smul_mul_mul_star_ne_smul_of_inf_eq_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_CosetGraph_mem_map_conj_of_mem_awayUnits_of_exists_pow_smul_star_mul_mul_eq_smul
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions CerednikDrinfeld.ShimuraCurveModel.instFieldFc CerednikDrinfeld.ShimuraCurveModel.isCurveOverC CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeF CerednikDrinfeld.ShimuraCurveModel.instFieldF CerednikDrinfeld.ShimuraCurveModel.instAlgebraFbar CerednikDrinfeld.ShimuraCurveModel.instAlgebraFc CerednikDrinfeld.ShimuraCurveModel.instFieldFbar CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeC CerednikDrinfeld.ShimuraCurveModel.instFiniteTors CerednikDrinfeld.ShimuraCurveModel.isCurveOverF CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeBar CerednikDrinfeld.ShimuraCurveModel.isCurveOverBar CerednikDrinfeld.ShimuraCurveModel.instAlgebraF CerednikDrinfeld.TwoPlaceTorsionDatum.instAddCommGroup CerednikDrinfeld.TwoPlaceTorsionDatum.instFinite CerednikDrinfeld.JPrimeTorsionDatum.instAddCommGroup CerednikDrinfeld.JPrimeTorsionDatum.instFinite instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "LocalGL2.swapUnit_val QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul CerednikDrinfeld.ShimuraCurveModel.mk.injEq CerednikDrinfeld.ShimuraCurveModel.coe_torsionHecke_apply CerednikDrinfeld.ShimuraCurveModel.galJ_apply CerednikDrinfeld.ShimuraCurveModel.heckeGenJ_apply CerednikDrinfeld.ShimuraCurveModel.coe_torsionGal_apply CerednikDrinfeld.ShimuraCurveModel.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.signTwist_heckeGen CerednikDrinfeld.ShimuraCurveModel.coe_restrictTors_apply ModularCurve.UniformizedHeckeCurve.mk.sizeOf_spec ModularCurve.UniformizedHeckeCurve.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CerednikDrinfeld.TwoPlaceTorsionDatum.snd_T CerednikDrinfeld.TwoPlaceTorsionDatum.snd_toric CerednikDrinfeld.TwoPlaceTorsionDatum.mk.injEq CerednikDrinfeld.TwoPlaceTorsionDatum.fst_T CerednikDrinfeld.TwoPlaceTorsionDatum.mk.sizeOf_spec CerednikDrinfeld.TwoPlaceTorsionDatum.fst_D CerednikDrinfeld.TwoPlaceTorsionDatum.snd_D CerednikDrinfeld.TwoPlaceTorsionDatum.fst_toric ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld
open scoped Quaternion TensorProduct NumberField

namespace SDGroupAux

open scoped Quaternion

variable {a b : ℚ}

theorem nrd_mul (x y : ℍ[ℚ, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.nrd_mk, QuaternionAlgebra.mk_mul_mk]
  ring

theorem nrd_smul (c : ℚ) (x : ℍ[ℚ, a, b]) : nrd (c • x) = c ^ 2 * nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.nrd_mk, QuaternionAlgebra.smul_mk, smul_eq_mul]
  ring

theorem pow_smul_pow_smul (r : ℕ) (m n : ℕ) (x : ℍ[ℚ, a, b]) :
    ((r ^ m : ℕ) : ℚ) • (((r ^ n : ℕ) : ℚ) • x) = ((r ^ (m + n) : ℕ) : ℚ) • x := by
  rw [smul_smul]; congr 1; push_cast; ring

theorem natCast_smul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (n : ℕ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) :
    ((n : ℕ) : ℚ) • x ∈ Λ := by
  rw [Nat.cast_smul_eq_nsmul]; exact Λ.toAddSubmonoid.nsmul_mem hx n

end SDGroupAux

theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N)
    (hN : Squarefree N)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓt : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt ↔ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v)
    (Λ₁s : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁s : IsMaximalOrder Λ₁s) (hR₁Λ₁s : R₁ ≤ Λ₁s) (htwin : Λ₁ ⊓ Λ₁s = R₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ r)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * r))
    (ℓ : HeckeTower.AwayPrime r rbar) (s : (ℍ[ℚ, a₁, b₁])ˣ)
    (sf : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs :
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * sf⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))
    (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt)
    (hint : ∃ (K : ℕ) (y : ↥Λ₁s), ((r ^ K : ℕ) : ℚ) •
      (star ((s : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * ((s : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) =
      ((ℓ.1 : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁])) :
    γ ∈ Γt.map (MulAut.conj s).toMonoidHom := by

  classical

  have hℓP : (ℓ.1 : ℕ).Prime := ℓ.1.prop
  have hℓ0 : ((ℓ.1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hℓP.ne_zero
  have hrP : r.Prime := Fact.out
  have hR₁o : IsOrder R₁ := hR₁.isOrder
  have hΛ₁o : IsOrder Λ₁ := hΛ₁.isOrder
  have hΛ₁so : IsOrder Λ₁s := hΛ₁s.isOrder
  set σ : ℍ[ℚ, a₁, b₁] := ((s : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) with hσ
  set g : ℍ[ℚ, a₁, b₁] := ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) with hg
  set w : ℍ[ℚ, a₁, b₁] := star σ * g * σ with hw
  have hnrd : nrd σ = ((ℓ.1 : ℕ) : ℚ) := hs.2.2.2
  have hiff := (CerednikDrinfeld.CosetGraph.mem_awayUnits_iff_exists_pow_smul_mem_of_forall_localBox_eq R₁ R₁ hR₁o hR₁o
      r v hv (fun _ _ => rfl)).1

  obtain ⟨c, -, hc, -⟩ := (hiff γ).1 ((hΓt γ).1 hγ)

  have hprime : Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
      (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
        (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * sf⁻¹ ∈
      primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ) := by
    have h3 := hs.2.2.1
    by_cases hdiv : (ℓ.1 : ℕ) ∣ N
    · rw [if_pos hdiv] at h3; exact h3.1
    · rw [if_neg hdiv] at h3; exact h3
  obtain ⟨a, ha⟩ := QuaternionAlgebra.exists_pow_smul_mem_of_finiteAdeleEvalAt_eq_tmul_of_mul_inv_mem_primeHeckeSet R₁
    (meetOrder R₁ n₁) hR₁o (by unfold meetOrder; exact inf_le_left) r (ℓ.1 : ℕ) ℓ.1.prop.ne_zero s sf hs.1 hprime
  have ha' : ((r ^ a : ℕ) : ℚ) • star σ ∈ R₁ := by
    have := (QuaternionAlgebra.IsOrder.star_mem_and_exists_int_trd_nrd hR₁o ha).1
    rwa [QuaternionAlgebra.star_smul] at this

  have hPw : ((r ^ (a + c + a) : ℕ) : ℚ) • w =
      (((r ^ a : ℕ) : ℚ) • star σ) * (((r ^ c : ℕ) : ℚ) • g) * (((r ^ a : ℕ) : ℚ) • σ) := by
    simp only [hw, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
    congr 1; push_cast; ring
  have hP : ((r ^ (a + c + a) : ℕ) : ℚ) • w ∈ R₁ := by
    rw [hPw]; exact hR₁o.mul_mem (hR₁o.mul_mem ha' hc) ha

  have goalA : ∃ (M : ℕ) (y' : ℍ[ℚ, a₁, b₁]), y' ∈ R₁ ∧ ((r ^ M : ℕ) : ℚ) • w = ((ℓ.1 : ℕ) : ℚ) • y' := by
    obtain ⟨K, y, hKy⟩ := hint
    have hKy' : ((r ^ K : ℕ) : ℚ) • w = ((ℓ.1 : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]) := by rw [hw]; exact hKy

    set e : ℕ := a + c + a with he
    have hy₁s : ((r ^ e : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]) ∈ Λ₁s := SDGroupAux.natCast_smul_mem _ y.2
    have hℓy₁ : ((ℓ.1 : ℕ) : ℚ) • (((r ^ e : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁])) = ((r ^ (e + K) : ℕ) : ℚ) • w := by
      calc ((ℓ.1 : ℕ) : ℚ) • (((r ^ e : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]))
          = ((r ^ e : ℕ) : ℚ) • (((ℓ.1 : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁])) := smul_comm _ _ _
        _ = ((r ^ e : ℕ) : ℚ) • (((r ^ K : ℕ) : ℚ) • w) := by rw [← hKy']
        _ = ((r ^ (e + K) : ℕ) : ℚ) • w := SDGroupAux.pow_smul_pow_smul _ _ _ _
    have hℓy₁R : ((ℓ.1 : ℕ) : ℚ) • (((r ^ e : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁])) ∈ R₁ := by
      rw [hℓy₁, Nat.add_comm, ← SDGroupAux.pow_smul_pow_smul]; exact SDGroupAux.natCast_smul_mem _ hP
    by_cases hdiv : (ℓ.1 : ℕ) ∣ N
    ·
      have hz := CerednikDrinfeld.exists_mem_forall_pow_smul_mul_mul_star_ne_smul_of_mem_levelHeckeUSet_meetOrder_of_dvd
        Λ₁ R₁ hΛ₁ hR₁ hRΛ₁ n₁ hn₁ hS₁ ℓ s sf hs hdiv
      obtain ⟨K₂, y₂, hy₂, hK₂⟩ :=
        QuaternionAlgebra.IsEichlerOrder.forall_exists_pow_smul_star_mul_mul_eq_smul_of_forall_pow_smul_mul_mul_star_ne_smul_of_inf_eq_of_dvd
          hrN hrbarN hN hdef Λ₁ R₁ hΛ₁ hR₁ hRΛ₁ Λ₁s hΛ₁s hR₁Λ₁s htwin (ℓ.1 : ℕ) hℓP hdiv σ hnrd ⟨a, ha⟩ ⟨a, ha'⟩ hz
          (((r ^ c : ℕ) : ℚ) • g) hc

      have hK₂' : ((r ^ (K₂ + c) : ℕ) : ℚ) • w = ((ℓ.1 : ℕ) : ℚ) • y₂ := by
        rw [← hK₂, hw]; simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]; congr 1; push_cast; ring

      have hy₃ : ((r ^ (K₂ + c) : ℕ) : ℚ) • (((r ^ e : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁])) =
          ((r ^ (e + K) : ℕ) : ℚ) • y₂ := by
        apply smul_right_injective ℍ[ℚ, a₁, b₁] hℓ0
        show ((ℓ.1 : ℕ) : ℚ) • _ = ((ℓ.1 : ℕ) : ℚ) • _
        calc ((ℓ.1 : ℕ) : ℚ) • (((r ^ (K₂ + c) : ℕ) : ℚ) • (((r ^ e : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁])))
            = ((r ^ (K₂ + c) : ℕ) : ℚ) • (((ℓ.1 : ℕ) : ℚ) • (((r ^ e : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]))) := smul_comm _ _ _
          _ = ((r ^ (K₂ + c) : ℕ) : ℚ) • (((r ^ (e + K) : ℕ) : ℚ) • w) := by rw [hℓy₁]
          _ = ((r ^ (e + K) : ℕ) : ℚ) • (((r ^ (K₂ + c) : ℕ) : ℚ) • w) := smul_comm _ _ _
          _ = ((r ^ (e + K) : ℕ) : ℚ) • (((ℓ.1 : ℕ) : ℚ) • y₂) := by rw [hK₂']
          _ = ((ℓ.1 : ℕ) : ℚ) • (((r ^ (e + K) : ℕ) : ℚ) • y₂) := smul_comm _ _ _
      refine ⟨K₂ + c + (e + K), ((r ^ (K₂ + c) : ℕ) : ℚ) • (((r ^ e : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁])), ?_, ?_⟩
      · rw [← htwin]
        exact ⟨by rw [hy₃]; exact SDGroupAux.natCast_smul_mem _ hy₂, SDGroupAux.natCast_smul_mem _ hy₁s⟩
      · calc ((r ^ (K₂ + c + (e + K)) : ℕ) : ℚ) • w
            = ((r ^ (K₂ + c) : ℕ) : ℚ) • (((r ^ (e + K) : ℕ) : ℚ) • w) := (SDGroupAux.pow_smul_pow_smul _ _ _ _).symm
          _ = ((r ^ (K₂ + c) : ℕ) : ℚ) • (((ℓ.1 : ℕ) : ℚ) • (((r ^ e : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]))) := by rw [hℓy₁]
          _ = ((ℓ.1 : ℕ) : ℚ) • (((r ^ (K₂ + c) : ℕ) : ℚ) • (((r ^ e : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]))) := smul_comm _ _ _
    ·
      have hidx := QuaternionAlgebra.IsEichlerOrder.relIndex_eq_of_isMaximalOrder_of_le (Fact.out : rbar.Prime) hdef hR₁ hΛ₁s hR₁Λ₁s
      have hNy : (N : ℤ) • (((r ^ e : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁])) ∈ R₁ := by
        have := AddSubgroup.nsmul_relIndex_mem R₁.toAddSubgroup (K := Λ₁s.toAddSubgroup) hy₁s
        rw [hidx] at this
        rwa [← natCast_zsmul] at this
      have hℓy : ((ℓ.1 : ℕ) : ℤ) • (((r ^ e : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁])) ∈ Λ₁ := by
        rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ]; exact hRΛ₁ hℓy₁R
      have hcop : IsCoprime ((ℓ.1 : ℕ) : ℤ) (N : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hℓP).mpr hdiv)
      obtain ⟨u, u', huu'⟩ := hcop
      have hy₁Λ₁ : ((r ^ e : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]) ∈ Λ₁ := by
        have : ((r ^ e : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]) =
            u • (((ℓ.1 : ℕ) : ℤ) • (((r ^ e : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]))) +
              u' • ((N : ℤ) • (((r ^ e : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]))) := by
          rw [smul_smul, smul_smul, ← add_smul, huu', one_smul]
        rw [this]
        exact Λ₁.add_mem (Λ₁.smul_mem u hℓy) (Λ₁.smul_mem u' (hRΛ₁ hNy))
      refine ⟨e + K, ((r ^ e : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]), ?_, hℓy₁.symm⟩
      rw [← htwin]; exact ⟨hy₁Λ₁, hy₁s⟩
  obtain ⟨M, y', hy'R, hM⟩ := goalA

  set x : (ℍ[ℚ, a₁, b₁])ˣ := s⁻¹ * γ * s with hx
  have hsbar : star σ = ((ℓ.1 : ℕ) : ℚ) • (((s⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ)) : ℍ[ℚ, a₁, b₁]) := by
    calc star σ = star σ * (σ * (((s⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ)) : ℍ[ℚ, a₁, b₁])) := by rw [hσ, Units.mul_inv, mul_one]
      _ = (star σ * σ) * (((s⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ)) : ℍ[ℚ, a₁, b₁]) := by rw [mul_assoc]
      _ = ((ℓ.1 : ℕ) : ℚ) • (((s⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ)) : ℍ[ℚ, a₁, b₁]) := by
          rw [QuaternionAlgebra.star_mul_eq_coe_nrd, hnrd, QuaternionAlgebra.coe_mul_eq_smul]
  have hxval : ((ℓ.1 : ℕ) : ℚ) • ((x : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = w := by
    rw [hx, Units.val_mul, Units.val_mul, hw, hsbar, ← hg, ← hσ]
    simp only [Algebra.smul_mul_assoc]

  have hxR : ((r ^ M : ℕ) : ℚ) • ((x : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = y' := by
    apply smul_right_injective ℍ[ℚ, a₁, b₁] hℓ0
    show ((ℓ.1 : ℕ) : ℚ) • _ = ((ℓ.1 : ℕ) : ℚ) • _
    calc ((ℓ.1 : ℕ) : ℚ) • (((r ^ M : ℕ) : ℚ) • ((x : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]))
        = ((r ^ M : ℕ) : ℚ) • (((ℓ.1 : ℕ) : ℚ) • ((x : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) := smul_comm _ _ _
      _ = ((r ^ M : ℕ) : ℚ) • w := by rw [hxval]
      _ = ((ℓ.1 : ℕ) : ℚ) • y' := hM

  have hnx : nrd ((x : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = nrd g := by
    have h1 : (((s⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ)) : ℍ[ℚ, a₁, b₁]) * σ = 1 := by rw [hσ]; exact Units.inv_mul _
    rw [hx, Units.val_mul, Units.val_mul, ← hσ, ← hg, SDGroupAux.nrd_mul, SDGroupAux.nrd_mul]
    calc nrd (((s⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ)) : ℍ[ℚ, a₁, b₁]) * nrd g * nrd σ
        = nrd g * (nrd (((s⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ)) : ℍ[ℚ, a₁, b₁]) * nrd σ) := by ring
      _ = nrd g := by rw [← SDGroupAux.nrd_mul, h1, QuaternionAlgebra.nrd_one, mul_one]
  obtain ⟨i, j, hij⟩ := CerednikDrinfeld.CosetGraph.exists_nrd_mul_pow_eq_pow_of_mem_awayUnits R₁ hR₁o r v hv γ ((hΓt γ).1 hγ)
  rw [← hg] at hij
  have hstarx : star ((x : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = nrd g • (((x⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ)) : ℍ[ℚ, a₁, b₁]) := by
    have h2 : ((x : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * star ((x : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) =
        ((nrd g : ℚ) : ℍ[ℚ, a₁, b₁]) := by rw [QuaternionAlgebra.mul_star_eq_coe_nrd, hnx]
    calc star ((x : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])
        = (((x⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ)) : ℍ[ℚ, a₁, b₁]) *
            (((x : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * star ((x : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) := by
          rw [Units.inv_mul_cancel_left]
      _ = (((x⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ)) : ℍ[ℚ, a₁, b₁]) * ((nrd g : ℚ) : ℍ[ℚ, a₁, b₁]) := by rw [h2]
      _ = nrd g • (((x⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ)) : ℍ[ℚ, a₁, b₁]) := by rw [QuaternionAlgebra.mul_coe_eq_smul]
  have hstar_mem : ((r ^ M : ℕ) : ℚ) • star ((x : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ∈ R₁ := by
    rw [← QuaternionAlgebra.star_smul, hxR]; exact (QuaternionAlgebra.IsOrder.star_mem_and_exists_int_trd_nrd hR₁o hy'R).1
  have hri : ((r : ℚ) ^ i) = ((r ^ i : ℕ) : ℚ) := by push_cast; rfl
  have hkey : ((r : ℚ) ^ j) • (((x⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ)) : ℍ[ℚ, a₁, b₁]) =
        ((r : ℚ) ^ i) • star ((x : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ∨
      ((r : ℚ) ^ j) • (((x⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ)) : ℍ[ℚ, a₁, b₁]) =
        -(((r : ℚ) ^ i) • star ((x : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) := by
    rw [hstarx, smul_smul, mul_comm ((r : ℚ) ^ i) (nrd g)]
    rcases hij with h | h
    · left; rw [h]
    · right; rw [h, neg_smul, neg_neg]
  have hinv_mem : ((r ^ (M + j) : ℕ) : ℚ) • (((x⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ)) : ℍ[ℚ, a₁, b₁]) ∈ R₁ := by
    have e1 : ((r ^ (M + j) : ℕ) : ℚ) • (((x⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ)) : ℍ[ℚ, a₁, b₁]) =
        ((r ^ M : ℕ) : ℚ) • (((r : ℚ) ^ j) • (((x⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ)) : ℍ[ℚ, a₁, b₁])) := by
      rw [smul_smul]; congr 1; push_cast; ring
    rw [e1]
    rcases hkey with h | h
    · rw [h, smul_comm, hri]; exact SDGroupAux.natCast_smul_mem _ hstar_mem
    · rw [h, smul_neg, smul_comm, hri]; exact R₁.neg_mem (SDGroupAux.natCast_smul_mem _ hstar_mem)
  have hxaway : x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v :=
    (hiff x).2 ⟨M, M + j, by rw [hxR]; exact hy'R, hinv_mem⟩
  refine Subgroup.mem_map.mpr ⟨x, (hΓt x).2 hxaway, ?_⟩
  show (MulAut.conj s) x = γ
  rw [MulAut.conj_apply, hx]; group

end S_CerednikDrinfeld_CosetGraph_mem_map_conj_of_mem_awayUnits_of_exists_pow_smul_star_mul_mul_eq_smul
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_mem_map_conj_of_mem_awayUnits_of_exists_pow_smul_star_mul_mul_eq_smul (solution)
