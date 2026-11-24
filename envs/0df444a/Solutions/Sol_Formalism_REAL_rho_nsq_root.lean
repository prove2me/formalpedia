-- Prove2me | solution 1 for Formalism.REAL.rho_nsq_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:36:03.237814+00:00
-- url     : https://prove2.me/submissions/b96e8617-3070-4f98-afe1-5b460631f32a

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (x : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b) :
    nsq (x + root a b) = nsq x + 2 * (x a - x b) + 2 := by
  have hs : ∀ i, (x + (Pi.single a 1 - Pi.single b 1) : Fin n → ℝ) i *
        (x + (Pi.single a 1 - Pi.single b 1) : Fin n → ℝ) i
      = x i * x i + (2 * x i + 1) * (Pi.single a (1 : ℝ) : Fin n → ℝ) i +
        (1 - 2 * x i) * (Pi.single b (1 : ℝ) : Fin n → ℝ) i := by
    intro i
    by_cases h1 : i = a <;> by_cases h2 : i = b
    · exact absurd (h1.symm.trans h2) hab
    all_goals simp [Pi.single_apply, h1, h2, hab, Ne.symm hab] <;> ring
  unfold root nsq dot
  rw [Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp [Pi.single_apply] <;> ring
end Formalism.REAL
