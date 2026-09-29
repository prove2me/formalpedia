-- Prove2me | solution 1 for CuspForm.heckeLocal.pi_U_eq_zero_of_sq_dvd_of_not_cube_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e2ec3216-69c9-52b2-a56d-7b2b2ea6680c

import Definitions.Def_CuspForm_HeckeLocal
import Theorems.Thm_CuspForm_exists_heckeULin_mul_aeval_eq_zero_of_sq_dvd_of_not_cube_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_pi_U_eq_zero_of_sq_dvd_of_not_cube_dvd
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CuspForm.coe_heckeULowerLin_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

open IsLocalRing

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 4000000 in
open CuspForm in
theorem solution
    (N : ℕ) [NeZero N] (S₀ : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ' : CuspForm.heckeAlgebra N 2 S₀ →+* ResidueField 𝒪)
    (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS₀ : q ∉ S₀) (hsq : q ^ 2 ∣ N) (hcube : ¬ q ^ 3 ∣ N)
    (hq𝒪 : IsUnit (q : 𝒪))
    (hθ' : θ' (CuspForm.heckeAlgebra.U hq hqN hqS₀) = 0) :
    CuspForm.heckeLocal.π N S₀ 𝒪 θ' (CuspForm.heckeAlgebra.U hq hqN hqS₀) = 0 := by
  classical

  obtain ⟨R, a, hR0, hRU⟩ :=
    CuspForm.exists_heckeULin_mul_aeval_eq_zero_of_sq_dvd_of_not_cube_dvd N Fact.out q hq hqN hsq hcube

  set U : heckeAlgebra N 2 S₀ := heckeAlgebra.U hq hqN hqS₀ with hUdef
  set r : heckeAlgebra N 2 S₀ := Polynomial.aeval U R with hrdef
  have hrU : r * U = 0 := by
    apply Subtype.ext
    have hval : ((r * U : heckeAlgebra N 2 S₀) : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) =
        Polynomial.aeval (heckeULin (N := N) 2 hqN) R * heckeULin 2 hqN := by
      rw [Subalgebra.coe_mul, hrdef, Polynomial.aeval_subalgebra_coe, hUdef, heckeAlgebra.coe_U]
    rw [hval, Subalgebra.coe_zero]

    have h1 : Polynomial.aeval (heckeULin (N := N) 2 hqN) (R * Polynomial.X) =
        Polynomial.aeval (heckeULin (N := N) 2 hqN) R * heckeULin 2 hqN := by
      rw [map_mul, Polynomial.aeval_X]
    have h2 : Polynomial.aeval (heckeULin (N := N) 2 hqN) (Polynomial.X * R) =
        heckeULin 2 hqN * Polynomial.aeval (heckeULin (N := N) 2 hqN) R := by
      rw [map_mul, Polynomial.aeval_X]
    rw [← h1, mul_comm R, h2]
    exact hRU

  have hθ'r : θ' r = ((R.eval 0 : ℤ) : ResidueField 𝒪) := by
    have h := (Polynomial.aeval_algHom_apply θ'.toIntAlgHom U R).symm
    rw [RingHom.toIntAlgHom_apply, RingHom.toIntAlgHom_apply, hθ',
      ← Polynomial.coeff_zero_eq_aeval_zero', Polynomial.coeff_zero_eq_eval_zero] at h
    rw [hrdef, h]
    rfl
  have hqk : ((q : ℕ) : ResidueField 𝒪) ≠ 0 := by
    have h := hq𝒪.map (residue 𝒪)
    rw [map_natCast] at h
    exact h.ne_zero
  have hR0k : ((R.eval 0 : ℤ) : ResidueField 𝒪) ≠ 0 := by
    obtain ⟨c, hc⟩ := hR0
    intro h0
    have hcast : ((q : ℤ) ^ a : ℤ) = R.eval 0 * c := hc
    have hk : ((q : ℕ) : ResidueField 𝒪) ^ a = ((R.eval 0 : ℤ) : ResidueField 𝒪) * (c : ResidueField 𝒪) := by
      have := congrArg (Int.cast : ℤ → ResidueField 𝒪) hcast
      push_cast at this
      exact this
    rw [h0, zero_mul] at hk
    exact pow_ne_zero a hqk hk
  have hθ'r_ne : θ' r ≠ 0 := by rw [hθ'r]; exact hR0k

  have hmem : (1 : 𝒪) ⊗ₜ[ℤ] r ∈ (heckeCharKernel N S₀ 𝒪 θ').primeCompl := by
    rw [Ideal.mem_primeCompl_iff, mem_heckeCharKernel_iff, residualCharacter_tmul, map_one, one_mul]
    exact hθ'r_ne
  have hsub : latticeBaseChange N S₀ 𝒪 ((1 : 𝒪) ⊗ₜ[ℤ] r) ∈ heckeLocalSubmonoid N S₀ 𝒪 θ' :=
    ⟨(1 : 𝒪) ⊗ₜ[ℤ] r, hmem, rfl⟩

  have hkill : latticeBaseChange N S₀ 𝒪 ((1 : 𝒪) ⊗ₜ[ℤ] r) *
      latticeBaseChange N S₀ 𝒪 ((1 : 𝒪) ⊗ₜ[ℤ] U) = 0 := by
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hrU, TensorProduct.tmul_zero, map_zero]
  have hπ : heckeLocal.π N S₀ 𝒪 θ' U =
      algebraMap (heckeBaseAlgebra N S₀ 𝒪) (heckeLocal N S₀ 𝒪 θ')
        (latticeBaseChange N S₀ 𝒪 ((1 : 𝒪) ⊗ₜ[ℤ] U)) := rfl
  rw [hπ, IsLocalization.map_eq_zero_iff (heckeLocalSubmonoid N S₀ 𝒪 θ')]
  exact ⟨⟨_, hsub⟩, hkill⟩

end S_CuspForm_heckeLocal_pi_U_eq_zero_of_sq_dvd_of_not_cube_dvd
end P2MW
export P2MW.S_CuspForm_heckeLocal_pi_U_eq_zero_of_sq_dvd_of_not_cube_dvd (solution)
