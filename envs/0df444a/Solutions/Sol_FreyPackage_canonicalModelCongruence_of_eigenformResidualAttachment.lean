-- Prove2me | solution 1 for FreyPackage.canonicalModelCongruence_of_eigenformResidualAttachment
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/516325da-ab9d-502c-b984-2f5cee891ded

import Mathlib
import Definitions.Def_FreyPackage_RouteAReversePinSeam
import Definitions.Def_FreyPackage_EigenformResidualAttachment
import Definitions.Def_FreyCurve_Basic
import Theorems.Thm_Representation_trace_eq_and_det_eq_of_frobenius_agree_of_ker_restrictNormalHom_le
import Theorems.Thm_WeierstrassCurve_IsIntegralModelOf_galoisTrace_det_frobenius
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Theorems.Thm_WeierstrassCurve_finrank_torsionBy_of_isAlgClosed
import Theorems.Thm_FreyPackage_freyCurveInt_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_canonicalModelCongruence_of_eigenformResidualAttachment
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec FrobeniusEndo.linePencil_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open WeierstrassCurve WeierstrassCurve.Affine.Point
open scoped CongruenceSubgroup WeierstrassCurve.Affine

noncomputable section

noncomputable local instance instDecEqQbarWs11C1 :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

theorem solution (P : FreyPackage)
    (hatt : ∀ M : ℕ, 0 < M → P.EigenformResidualAttachmentAt M)
    {N : ℕ} {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} {W : WeierstrassCurve ℤ}
    {𝔪 : Ideal (integralClosure ℤ ℂ)} (hwit : P.IsCongruentWitness N f W 𝔪) :
    ∀ ℓ₀ : ℕ, ℓ₀.Prime → (FreyPackage.freyCurveInt P).IsGoodPrimeFor ℓ₀ → ¬ ℓ₀ ∣ N → ℓ₀ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ₀ ∧
        a - (((FreyPackage.freyCurveInt P).apOfModel ℓ₀ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪 := by
  intro ℓ₀ hℓ₀ hgoodInt hℓ₀N hℓ₀p
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  obtain ⟨hf, hWmodel, h𝔪, hp𝔪, hcong⟩ := hwit

  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · exact absurd (dvd_zero ℓ₀) hℓ₀N
    · exact h

  have hΔ : W.Δ ≠ 0 := by
    obtain ⟨C, hC⟩ := hWmodel
    intro h0
    have h1 : (W.map (Int.castRingHom ℚ)).Δ = 0 := by rw [WeierstrassCurve.map_Δ, h0, _root_.map_zero]
    rw [← hC, WeierstrassCurve.variableChange_Δ] at h1
    have hE : P.freyCurve.Δ ≠ 0 := by
      rw [← WeierstrassCurve.coe_Δ']; exact Units.ne_zero _
    exact (mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hE) h1

  have hInt : (FreyPackage.freyCurveInt P).IsIntegralModelOf P.freyCurve :=
    ⟨1, by rw [one_smul, P.freyCurveInt_map]⟩

  obtain ⟨K, _, _, V, _, _, ρ, ψ, F, _, _, _, _, _, hψ𝔪, hfrV, hker, htrA, hdetA⟩ :=
    hatt N hN f hf 𝔪 h𝔪 hp𝔪
  have hkerψ : RingHom.ker ψ = 𝔪 :=
    (h𝔪.eq_of_le (RingHom.ker_ne_top ψ) hψ𝔪).symm

  have hNp : N * P.p ≠ 0 := by
    have := P.pp.pos
    positivity
  set S : Finset ℕ := (N * P.p).primeFactors ∪ W.Δ.natAbs.primeFactors with hSdef
  have hSpec : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N ∧ ℓ ≠ P.p ∧ W.IsGoodPrimeFor ℓ := by
    intro ℓ hℓ hℓS
    rw [hSdef, Finset.mem_union, not_or] at hℓS
    have hNpdvd : ¬ ℓ ∣ N * P.p := fun h =>
      hℓS.1 (Nat.mem_primeFactors.mpr ⟨hℓ, h, hNp⟩)
    refine ⟨fun h => hNpdvd (dvd_mul_of_dvd_left h P.p),
      fun h => hNpdvd (h ▸ dvd_mul_left P.p N), ?_⟩
    intro hdvd
    exact hℓS.2 (Nat.mem_primeFactors.mpr
      ⟨hℓ, by simpa using Int.natAbs_dvd_natAbs.mpr hdvd, Int.natAbs_ne_zero.mpr hΔ⟩)

  have htr : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          algebraMap (ZMod P.p) K (LinearMap.trace (ZMod P.p)
              (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p)
              (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) P.freyCurve P.p τ))
            = LinearMap.trace K V (ρ τ) := by
    intro ℓ hℓ hℓS A hA τ hτ
    obtain ⟨hℓN, hℓp, hgoodW⟩ := hSpec ℓ hℓ hℓS
    obtain ⟨a, ha, ham⟩ := hcong ℓ hℓ hgoodW hℓN hℓp
    obtain ⟨a', ha', htra'⟩ := htrA ℓ hℓ hℓN hℓp A hA τ hτ
    have haa' : a = a' := Subtype.ext (ha.trans ha'.symm)
    have hcongK : ψ a = ψ ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) := by
      rw [← sub_eq_zero, ← map_sub]
      exact RingHom.mem_ker.mp (hkerψ ▸ ham)
    have h10 := (hWmodel.galoisTrace_det_frobenius P.p ℓ P.pp hℓ hℓp hgoodW A hA τ hτ).1
    rw [galoisTrace_def] at h10
    rw [h10, htra', ← haa', hcongK, map_intCast, map_intCast]

  have hdet : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          algebraMap (ZMod P.p) K (LinearMap.det
              (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) P.freyCurve P.p τ))
            = LinearMap.det (ρ τ) := by
    intro ℓ hℓ hℓS A hA τ hτ
    obtain ⟨hℓN, hℓp, hgoodW⟩ := hSpec ℓ hℓ hℓS
    have h10 := (hWmodel.galoisTrace_det_frobenius P.p ℓ P.pp hℓ hℓp hgoodW A hA τ hτ).2
    rw [h10, hdetA ℓ hℓ hℓN hℓp A hA τ hτ, map_natCast]

  have hp0 : ((P.p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast P.pp.ne_zero
  have hfrE : Module.finrank (ZMod P.p)
      (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p) = 2 :=
    WeierstrassCurve.finrank_torsionBy_of_isAlgClosed (F := ℚ) (K := AlgebraicClosure ℚ)
      P.freyCurve (p := P.p) hp0

  have hall := fun σ => Representation.trace_eq_and_det_eq_of_frobenius_agree_of_ker_restrictNormalHom_le
    (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) P.freyCurve P.p) ρ
    hfrE hfrV F hker S htr hdet σ

  obtain ⟨A₀, hA₀, τ₀, hτ₀⟩ := ValuationSubring.exists_isFrobeniusAt_rat ℓ₀ hℓ₀
  obtain ⟨a₀, ha₀, htra₀⟩ := htrA ℓ₀ hℓ₀ hℓ₀N hℓ₀p A₀ hA₀ τ₀ hτ₀
  refine ⟨a₀, ha₀, ?_⟩
  have h10 := (hInt.galoisTrace_det_frobenius P.p ℓ₀ P.pp hℓ₀ hℓ₀p hgoodInt A₀ hA₀ τ₀ hτ₀).1
  rw [galoisTrace_def] at h10
  rw [← hkerψ, RingHom.mem_ker, map_sub, sub_eq_zero, ← htra₀, ← (hall τ₀).1, h10,
    map_intCast, map_intCast]

end
end S_FreyPackage_canonicalModelCongruence_of_eigenformResidualAttachment
end P2MW
export P2MW.S_FreyPackage_canonicalModelCongruence_of_eigenformResidualAttachment (solution)
