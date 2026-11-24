-- Prove2me | solution 1 for Formalism.MainNotions.UnusedSlot33.HK.diffK_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:24:38.445279+00:00
-- url     : https://prove2.me/submissions/9f461b9f-6603-4abd-88d8-32a4f10920c5

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_EqOfLeOfAbsNormEq
import Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_different_quad
import Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_gen_top
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.UnusedSlot33 Formalism.MainNotions.UnusedSlot33.HK
open NumberField Polynomial Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise
variable {R : Ranks} (H : Host R)
namespace Formalism.MainNotions.UnusedSlot33.HK
theorem _root_.solution (H : Host R) : DiffKH H := by
  obtain ⟨-, hd, -, hd16, -⟩ := H.hyp
  have hmem : H.sqd ∈ H.K := IntermediateField.mem_adjoin_simple_self ℚ H.sqd
  have hx2 : (⟨H.sqd, hmem⟩ : H.K) ^ 2 = -(H.d : H.K) := by
    apply Subtype.ext
    simp [H.sqd_sq]
  have hint : IsIntegral ℤ (⟨H.sqd, hmem⟩ : H.K) := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (H.d : ℤ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hx2]
    simp
  have hint' : (⟨H.sqd, hmem⟩ : H.K) ∈ integralClosure ℤ H.K := (mem_integralClosure_iff ℤ _).2 hint
  have hdiff := Formalism.MainNotions.UnusedSlot33.HK.different_quad H.K (-(H.d : ℤ)) ⟨H.sqd, hmem⟩ (by rw [hx2]; simp)
    (Formalism.MainNotions.UnusedSlot33.HK.gen_top H _ rfl)
    (Int.squarefree_natAbs.1 (by simpa using Irreducible.squarefree hd)) (by omega) (by omega)
    ⟨⟨H.sqd, hmem⟩, hint'⟩ rfl
  refine ⟨algebraMap (𝓞 H.K) (𝓞 H.E) ⟨⟨H.sqd, hmem⟩, hint'⟩, rfl, ?_⟩
  rw [hdiff, Ideal.map_span]
  exact congrArg Ideal.span Set.image_singleton
end Formalism.MainNotions.UnusedSlot33.HK
