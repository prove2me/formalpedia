-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BruhatBigCell.mid_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:12:47.943803+00:00
-- url     : https://prove2.me/submissions/fffb8544-d725-483c-b874-49a49660e796

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_col_mid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.BruhatBigCell
open GBasic
variable {k r : ℕ}
variable (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
namespace Formalism.QuantumDeterminants.BruhatBigCell
theorem _root_.solution (p q : Fin (k + 1)) : bigCell k r c μ (wI k r p) (wI k r q) = μ p q := by
  have hp := p.isLt
  have hq := q.isLt
  rw [col_mid c μ _ _ (by simp [wI]) (by simp only [wI]; omega),
    dif_pos ⟨by simp [wI], by simp only [wI]; omega⟩]
  congr 1 <;> apply Fin.ext <;> simp [wI]
end Formalism.QuantumDeterminants.BruhatBigCell
