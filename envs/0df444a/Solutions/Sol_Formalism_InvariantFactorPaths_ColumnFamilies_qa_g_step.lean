-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_g_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:43:46.952942+00:00
-- url     : https://prove2.me/submissions/a0e9e374-2724-4657-9db1-ccaab1b1154b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_Slt
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_g_le_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (hint : Formalism.GradedWeylDivisibility.Interlaced m) (k : ℤ) (hk1 : 1 ≤ k)
    (p p' : Fin n) (hpp : p'.val = p.val + 1) (hk : k ≤ (∑ b : Fin n, m (b, p) : ℕ))
    (hk' : k ≤ (∑ b : Fin n, m (b, p') : ℕ)) : qa_g m k p < qa_g m k p' := by
  have h1 : k ≤ qa_S m (qa_g m k p') p' := (qa_g_le_iff m k p' hk' _).mp le_rfl
  have h2 : qa_S m (qa_g m k p') p' ≤ 0 + ∑ b : Fin n with b < qa_g m k p', m (b, p) :=
    hint p p' hpp (qa_g m k p')
  by_contra hc
  rcases qa_Slt m (qa_g m k p') p with h0 | ⟨b, hb, h3⟩
  · omega
  · have h4 : ¬ qa_g m k p ≤ b := fun hh => hc (lt_of_le_of_lt hh hb)
    rw [qa_g_le_iff m k p hk] at h4
    omega
end Formalism.InvariantFactorPaths.ColumnFamilies
