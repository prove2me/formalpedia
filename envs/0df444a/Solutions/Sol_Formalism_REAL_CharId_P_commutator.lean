-- Prove2me | solution 1 for Formalism.REAL.CharId_P_commutator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:12:42.857396+00:00
-- url     : https://prove2.me/submissions/f4b6a6b1-15d5-46c4-b683-f1eca482d916

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId
import Theorems.Thm_Formalism_REAL_generatorPowCovariance_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (ν : Fin n → ℂ) (a b c d : Fin n) :
    E c d * CharId_P E ν a b - CharId_P E ν a b * E c d =
      (if d = a then CharId_P E ν c b else 0) - (if b = c then CharId_P E ν a d else 0) := by
  unfold CharId_P
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  have h : ∀ i ∈ range (n + 1),
      E c d * ((∏ s : Fin n, (X - C (lsh ν s))).coeff i • epow E i a b) -
        ((∏ s : Fin n, (X - C (lsh ν s))).coeff i • epow E i a b) * E c d =
      (if d = a then (∏ s : Fin n, (X - C (lsh ν s))).coeff i • epow E i c b else 0) -
        (if b = c then (∏ s : Fin n, (X - C (lsh ν s))).coeff i • epow E i a d else 0) := by
    intro i _
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, generatorPowCovariance_holds _ n E hE i a b c d]
    split_ifs <;> simp [smul_sub]
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib]
  split_ifs <;> simp [smul_sub]
end Formalism.REAL
