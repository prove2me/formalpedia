-- Prove2me | solution 1 for Formalism.L2.NG.pow_level_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:19:56.797187+00:00
-- url     : https://prove2.me/submissions/f7555665-c3c5-42cf-8d18-30df07b74350

import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsLab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.L2 Formalism.L2.NG
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {p : ℕ} [Fact p.Prime]
namespace Formalism.L2.NG
theorem _root_.solution {x : Formalism.CyclotomicNorms.Fbar p} {d : ℕ} (h : x ^ (p ^ d - 1) = 1) (e : ℕ) : x ^ (p ^ (d * e) - 1) = 1 := by
  obtain ⟨c, hc⟩ : (p ^ d - 1) ∣ (p ^ (d * e) - 1) := by
    rw [pow_mul]; exact Nat.sub_one_dvd_pow_sub_one _ _
  rw [hc, pow_mul, h, one_pow]
end Formalism.L2.NG
