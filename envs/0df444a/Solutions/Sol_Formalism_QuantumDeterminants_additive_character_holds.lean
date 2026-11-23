-- Prove2me | solution 1 for Formalism.QuantumDeterminants.additive_character_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:56.372286+00:00
-- url     : https://prove2.me/submissions/239e8683-0387-45fe-ac01-58e2972094b7

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_nset_iff
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_ell_mul

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
namespace Formalism.QuantumDeterminants
theorem _root_.solution : PsiChar := by
  unfold PsiChar
  intro k r z c hz g hg
  refine ⟨fun h hh => ?_, ?_⟩
  · unfold psi
    rw [WeylGroupFacts.ell_mul z hz ((WeylGroupFacts.nset_iff g).1 hg).2 ((WeylGroupFacts.nset_iff h).1 hh).2]
    rw [← Complex.exp_add]
    congr 1
    simp only [mul_add, Complex.add_re, Complex.ofReal_add]
  · unfold psi
    rw [mul_comm Complex.I]
    first
      | exact Complex.norm_exp_ofReal_mul_I _
      | simp [Complex.norm_exp]
end Formalism.QuantumDeterminants
