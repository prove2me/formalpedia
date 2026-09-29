-- Prove2me | solution 1 for CerednikDrinfeld.jointDelta_classSetEdgeHecke_mulVecLin_eq_zero_of_forall_jointDelta_eq_zero_of_mem_primeHeckeSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e9d793a0-9748-521b-8497-2f251c762bdb

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder

import Theorems.Thm_CerednikDrinfeld_jointDelta_one_classSetEdgeHecke_mulVecLin_eq_natCast_smul_jointDelta_zero_of_mem_primeHeckeSet
import Theorems.Thm_CerednikDrinfeld_jointDelta_zero_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_sub_of_mem_primeHeckeSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_jointDelta_classSetEdgeHecke_mulVecLin_eq_zero_of_forall_jointDelta_eq_zero_of_mem_primeHeckeSet
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem solution
    (N q q' : ℕ) [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqq' : q' ≠ q) (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    {a b : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]
    (hn : IsEichlerOrder (meetOrder R n) (N * q)) (hnH : n ∈ primeHeckeSet R q)
    (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ)
    (hx : ∀ i, jointDelta (classSetDegeneracyData R n) i x = 0) (i : Fin 2) :
    jointDelta (classSetDegeneracyData R n) i
      ((classSetEdgeHecke N q Λ R n ⟨q, Fact.out⟩).mulVecLin x) = 0 := by
  have h0 := hx 0
  have h1 := hx 1
  have hA := CerednikDrinfeld.jointDelta_zero_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_sub_of_mem_primeHeckeSet
      N q q' hqq' hqN hq'N hdef Λ R hΛ hR hRΛ n hn hnH x
  have hB := CerednikDrinfeld.jointDelta_one_classSetEdgeHecke_mulVecLin_eq_natCast_smul_jointDelta_zero_of_mem_primeHeckeSet
      N q q' hqq' hqN hq'N hdef Λ R hΛ hR hRΛ n hn hnH x
  fin_cases i
  ·
    show jointDelta (classSetDegeneracyData R n) 0 _ = 0
    rw [hA, h0, h1, map_zero, sub_zero]
  ·
    show jointDelta (classSetDegeneracyData R n) 1 _ = 0
    rw [hB, h0, smul_zero]

end S_CerednikDrinfeld_jointDelta_classSetEdgeHecke_mulVecLin_eq_zero_of_forall_jointDelta_eq_zero_of_mem_primeHeckeSet
end P2MW
export P2MW.S_CerednikDrinfeld_jointDelta_classSetEdgeHecke_mulVecLin_eq_zero_of_forall_jointDelta_eq_zero_of_mem_primeHeckeSet (solution)
