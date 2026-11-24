-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.key_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:42.637571+00:00
-- url     : https://prove2.me/submissions/b88a18fa-7318-442d-8d03-eeedf17ee9d0

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
import Theorems.Thm_Formalism_YangianSpanCharacter_P_left_cancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution {a b ai bi mu lu mv lv hu hv η μ : A} {c : 𝕜}
    (ha2 : ai * a = 1) (hb2 : bi * b = 1) (hab : a * b = b * a)
    (h1 : lv * a = a * (lv + η)) (h2 : mu * b = b * (mu - μ)) (hη : c • η = lu - lv)
    (hμ : c • μ = mu - mv)
    (hR : c • (a * mu * (b * lv) - b * lv * (a * mu)) =
      a * (b * (mv * lv + hv)) - b * (a * (mu * lu + hu))) :
    (c - 1) • (mu * lv - lv * mu) = hv - hu - (mu * lu - lu * mu) := by
  have hA : a * mu * (b * lv) = a * (b * ((mu - μ) * lv)) := by
    calc a * mu * (b * lv) = a * (mu * b) * lv := by simp only [mul_assoc]
      _ = a * (b * ((mu - μ) * lv)) := by rw [h2]; simp only [mul_assoc]
  have hB : b * lv * (a * mu) = a * (b * ((lv + η) * mu)) := by
    calc b * lv * (a * mu) = b * (lv * a) * mu := by simp only [mul_assoc]
      _ = b * (a * ((lv + η) * mu)) := by rw [h1]; simp only [mul_assoc]
      _ = a * (b * ((lv + η) * mu)) := by rw [← mul_assoc b a, ← hab, mul_assoc a b]
  have hC : b * (a * (mu * lu + hu)) = a * (b * (mu * lu + hu)) := by
    rw [← mul_assoc b a, ← hab, mul_assoc a b]
  have e : a * (b * (c • ((mu - μ) * lv - (lv + η) * mu))) =
      a * (b * (mv * lv + hv - (mu * lu + hu))) := by
    calc a * (b * (c • ((mu - μ) * lv - (lv + η) * mu)))
        = c • (a * mu * (b * lv) - b * lv * (a * mu)) := by
          rw [hA, hB, ← mul_sub, ← mul_sub, mul_smul_comm, mul_smul_comm]
      _ = a * (b * (mv * lv + hv - (mu * lu + hu))) := by
          rw [hR, hC, ← mul_sub, ← mul_sub]
  have e2 := left_cancel hb2 (left_cancel ha2 e)
  have hμ' : c • (μ * lv) = (mu - mv) * lv := by rw [← smul_mul_assoc, hμ]
  have hη' : c • (η * mu) = (lu - lv) * mu := by rw [← smul_mul_assoc, hη]
  rw [sub_mul, add_mul, smul_sub, smul_sub, smul_add, hμ', hη'] at e2
  have key : c • (mu * lv) - c • (lv * mu) =
      mv * lv + hv - (mu * lu + hu) + (mu - mv) * lv + (lu - lv) * mu := by
    rw [← e2]
    abel
  rw [sub_smul, one_smul, smul_sub, key, sub_mul, sub_mul]
  abel
end Formalism.YangianSpanCharacter.P
