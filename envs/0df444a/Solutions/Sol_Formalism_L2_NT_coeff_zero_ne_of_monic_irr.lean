-- Prove2me | solution 1 for Formalism.L2.NT.coeff_zero_ne_of_monic_irr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:12:43.119939+00:00
-- url     : https://prove2.me/submissions/7d7c2121-40e8-4921-b984-f8938450fb52

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory
open Formalism Formalism.L2 Formalism.L2.NT
variable {g : ℕ} [Fact g.Prime]
namespace Formalism.L2.NT
theorem _root_.solution {K : Type} [Field K] {P : K[X]} (hm : P.Monic) (hi : Irreducible P) (hX : P ≠ X) :
    P.coeff 0 ≠ 0 := by
  intro h0
  obtain ⟨q, hq⟩ := X_dvd_iff.mpr h0
  rcases hi.isUnit_or_isUnit hq with hX' | hq'
  · exact not_isUnit_X hX'
  · apply hX
    have hmq : q.Monic := Monic.of_mul_monic_left monic_X (by rw [← hq]; exact hm)
    rw [hq, hmq.isUnit_iff.mp hq', mul_one]
end Formalism.L2.NT
