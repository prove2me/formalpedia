-- Prove2me | solution 1 for FLT.Gamma0FundamentalSet.integral_gammaFundamentalSet_eq_finsum_integral_fd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/4315ed41-7bbc-5d2a-95c5-f127ea600b63

import Mathlib
import Definitions.Def_AutomorphicForm_Gamma0ExactVolume
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FLT_Gamma0FundamentalSet_integral_gammaFundamentalSet_eq_finsum_integral_fd

noncomputable section

open scoped MatrixGroups UpperHalfPlane Modular Pointwise
open UpperHalfPlane MeasureTheory

namespace ModularCurve
namespace GammaTileUnfold

variable {Γ : Subgroup SL(2, ℤ)}

theorem measurableSet_smul_fd (γ : SL(2, ℤ)) : MeasurableSet (γ • (𝒟 : Set ℍ)) :=
  (ModularGroup.isClosed_fd.smul γ).measurableSet

theorem measurePreserving_smul (γ : SL(2, ℤ)) :
    MeasurePreserving (fun w : ℍ => γ • w) volume volume := by
  have hemb : MeasurableEmbedding (fun w : ℍ => γ • w) :=
    (Homeomorph.smul γ (α := ℍ)).measurableEmbedding
  exact ⟨hemb.measurable, by
    ext s hs
    rw [Measure.map_apply hemb.measurable hs, Set.preimage_smul,
      FLT.HyperbolicMeasure.volume_smul_sl2z]⟩

theorem setIntegral_smul_fd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ : SL(2, ℤ)) (f : ℍ → E) :
    ∫ u in γ • (𝒟 : Set ℍ), f u = ∫ w in (𝒟 : Set ℍ), f (γ • w) := by
  rw [← Set.image_smul]
  exact (measurePreserving_smul γ).setIntegral_image_emb
    (Homeomorph.smul γ (α := ℍ)).measurableEmbedding f _

theorem aedisjoint_tiles (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) {q q' : SL(2, ℤ) ⧸ Γ} (hqq' : q ≠ q') :
    AEDisjoint volume ((Quotient.out q)⁻¹ • (𝒟 : Set ℍ)) ((Quotient.out q')⁻¹ • (𝒟 : Set ℍ)) := by
  set a := (Quotient.out q : SL(2, ℤ))
  set b := (Quotient.out q' : SL(2, ℤ))

  have hset : a⁻¹ • (𝒟 : Set ℍ) ∩ b⁻¹ • (𝒟 : Set ℍ) =
      a⁻¹ • ((a * b⁻¹) • (𝒟 : Set ℍ) ∩ 𝒟) := by
    rw [Set.smul_set_inter, ← mul_smul, inv_mul_cancel_left, Set.inter_comm]
  have hne : ∀ ε : SL(2, ℤ), ε ∈ Γ → ε ∈ Subgroup.center SL(2, ℤ) → a * b⁻¹ ≠ ε := by
    intro ε hε hc h
    apply hqq'
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    change (QuotientGroup.mk a : SL(2, ℤ) ⧸ Γ) = QuotientGroup.mk b
    rw [QuotientGroup.eq]
    have this : a = ε * b := by rw [← h, inv_mul_cancel_right]
    have hc' : b⁻¹ * ε⁻¹ = ε⁻¹ * b⁻¹ := (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hc) b⁻¹)
    rw [this, mul_inv_rev, hc', mul_assoc, inv_mul_cancel, mul_one]
    exact Γ.inv_mem hε
  have h1 : a * b⁻¹ ≠ 1 := hne 1 Γ.one_mem (Subgroup.one_mem _)
  have h2 : a * b⁻¹ ≠ -1 := hne (-1) hΓ (by
    rw [Subgroup.mem_center_iff]; intro g; simp)
  rw [AEDisjoint, hset, FLT.HyperbolicMeasure.volume_smul_sl2z]
  refine measure_mono_null ?_ FLT.Gamma0ExactVolume.volume_fd_diff_fdo
  rintro z ⟨hzγ, hz⟩
  refine ⟨hz, fun hzo => ?_⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hzγ
  rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hzo hzγ with h | h
  · exact h1 (by rw [← inv_inv (a * b⁻¹), h, inv_one])
  · exact h2 (by rw [← inv_inv (a * b⁻¹), h, inv_neg_one])

end ModularCurve.GammaTileUnfold

open ModularCurve.GammaTileUnfold in

theorem solution
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℍ → E) (hf : IntegrableOn f (FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ)) :
    ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, f τ =
      ∑ᶠ q : SL(2, ℤ) ⧸ Γ, ∫ τ in ModularGroup.fd, f ((Quotient.out q)⁻¹ • τ) := by
  haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Subgroup.fintypeQuotientOfFiniteIndex
  rw [finsum_eq_sum_of_fintype]
  unfold FLT.Gamma0FundamentalSet.gammaFundamentalSet at hf ⊢
  rw [integral_iUnion_ae (fun q => (measurableSet_smul_fd _).nullMeasurableSet)
    (fun q q' h => aedisjoint_tiles hΓ h) hf, tsum_fintype]
  exact Finset.sum_congr rfl fun q _ => setIntegral_smul_fd _ f

end
end S_FLT_Gamma0FundamentalSet_integral_gammaFundamentalSet_eq_finsum_integral_fd
end P2MW
export P2MW.S_FLT_Gamma0FundamentalSet_integral_gammaFundamentalSet_eq_finsum_integral_fd (solution)
