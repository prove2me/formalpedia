-- Prove2me | solution 1 for CuspForm.IsNewform.hasNewvectorConductor_adelicSpan_factorization_of_isAdelicLiftOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/121466b5-d901-5638-87df-288ea4bd4357

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Theorems.Thm_LocalNewvector_AdelicSpan_exists_hasNewvectorConductor_le_factorization
import Theorems.Thm_CuspForm_IsNormalizedEigenform_goodEigensystemOccursAt_of_adelicLift_of_mem_span_of_fixed
import Theorems.Thm_CuspForm_IsAdelicLiftOf_exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_hasNewvectorConductor_adelicSpan_factorization_of_isAdelicLiftOf
p2m_attr_erase "instance" "LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic FLT.SpectralSide.instCompactSpaceMatrix"
p2m_attr_erase "simp" "ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul LocalNewvector.coe_borelElem_inv"

set_option autoImplicit false

theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦ0 : Φ ≠ 0)
    (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime] :
    LocalNewvector.HasNewvectorConductor q (LocalNewvector.AdelicSpan Φ) (M.factorization q) := by
  obtain ⟨c, hce, hc⟩ :=
    LocalNewvector.AdelicSpan.exists_hasNewvectorConductor_le_factorization Φ hΦ0 (NeZero.ne M) hΦg.level_inv q
  rcases Nat.lt_or_eq_of_le hce with hlt | heq
  · exfalso
    obtain ⟨y, hy, hy₀, hfix, hcent⟩ :=
      CuspForm.IsAdelicLiftOf.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot hΦg q c hc.1
    have hocc : g.GoodEigensystemOccursAt (M / q ^ (M.factorization q - c)) :=
      CuspForm.IsNormalizedEigenform.goodEigensystemOccursAt_of_adelicLift_of_mem_span_of_fixed hg.1 q Φ hΦg c y hy
        hy₀ hfix hcent
    have hpow : q ^ (M.factorization q - c) ∣ M :=
      (pow_dvd_pow q (Nat.sub_le _ _)).trans (Nat.ordProj_dvd M q)
    have hlt' : M / q ^ (M.factorization q - c) < M :=
      Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne M))
        (Nat.one_lt_pow (Nat.sub_ne_zero_of_lt hlt) (Fact.out : q.Prime).one_lt)
    exact hg.2 _ (Nat.div_dvd_of_dvd hpow) hlt'.ne hocc
  · rw [← heq]
    exact hc

end S_CuspForm_IsNewform_hasNewvectorConductor_adelicSpan_factorization_of_isAdelicLiftOf
end P2MW
export P2MW.S_CuspForm_IsNewform_hasNewvectorConductor_adelicSpan_factorization_of_isAdelicLiftOf (solution)
