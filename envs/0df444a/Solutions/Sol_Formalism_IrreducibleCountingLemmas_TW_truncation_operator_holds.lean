-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.truncation_operator_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:11:31.230785+00:00
-- url     : https://prove2.me/submissions/abfdaed0-2954-4a31-ad7e-7667a7787d22

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWCentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWCutOperator
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_asAlgebraHom_apply_eq_sum
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_central_idempotent_integral_twist


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
namespace Formalism.IrreducibleCountingLemmas.TW
theorem _root_.solution : CutOperator := by
  intro O K _ _ _ _ _ _ _ G _ _ V _ _ _ _ ρ Msup U ψU e hM he hc v hv hψ
  have hcomm : ∀ (g : G) (x : MonoidAlgebra K G) (w : V), (∀ y, x * y = y * x) →
      ρ g (ρ.asAlgebraHom x w) = ρ.asAlgebraHom x (ρ g w) := by
    intro g x w hx
    rw [← Representation.asAlgebraHom_single_one ρ g, ← Module.End.mul_apply, ← map_mul,
      ← Module.End.mul_apply, ← map_mul, hx]
  have hcA : ∀ y : MonoidAlgebra K G,
      ((Fintype.card G : K) • e) * y = y * ((Fintype.card G : K) • e) := by
    intro y
    rw [smul_mul_assoc, mul_smul_comm, hc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [asAlgebraHom_apply_eq_sum]
    refine Submodule.sum_mem _ fun g _ => ?_
    have hint : IsIntegral ℤ ((Fintype.card G : K) * e.coeff g) :=
      central_idempotent_integral_twist K G e he hc g
    have hintO : IsIntegral O ((Fintype.card G : K) * e.coeff g) := hint.tower_top
    obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.1 hintO
    have : ((Fintype.card G : K) • e).coeff g = algebraMap O K o := by
      rw [ho, MonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    rw [this, algebraMap_smul]
    exact Msup.smul_mem o (hM g v hv)
  · intro u
    rw [hcomm _ _ _ hcA, hψ u, map_smul]
  · rw [← Module.End.mul_apply, ← map_mul, mul_smul_comm, he]
  · intro hev
    rw [map_smul, LinearMap.smul_apply, hev]
  · intro T hT
    rw [asAlgebraHom_apply_eq_sum, asAlgebraHom_apply_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, hT]
end Formalism.IrreducibleCountingLemmas.TW
