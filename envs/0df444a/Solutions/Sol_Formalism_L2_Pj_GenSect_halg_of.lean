-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.halg_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:34.42357+00:00
-- url     : https://prove2.me/submissions/2b8d48b3-0147-4303-963c-192487052d68

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial Cardinal
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution (x : Fin m → Ω) (j₀ : Fin m) (htr : Algebra.trdeg K Ω = D)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) = D) :
    ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω := by
  intro ω
  have hadd := trdeg_add_eq (R := K)
    (S := IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) (A := Ω)
  rw [hbig, htr] at hadd
  have h0 : Algebra.trdeg (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) Ω = 0 := by
    rcases (Cardinal.add_eq_left_iff).mp hadd with h | h
    · exact absurd ((le_max_left _ _).trans h) (not_le.mpr ((Cardinal.natCast_lt_aleph0 (n := D))))
    · exact h
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) Ω := by
    first
    | exact Algebra.trdeg_eq_zero_iff.mp h0
    | exact trdeg_eq_zero_iff.mp h0
  exact IntermediateField.isAlgebraic_adjoin_iff.mp (halg.isAlgebraic ω)
end Formalism.L2.Pj.GenSect
