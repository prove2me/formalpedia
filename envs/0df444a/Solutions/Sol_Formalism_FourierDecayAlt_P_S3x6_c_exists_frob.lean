-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.c_exists_frob
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:22.38682+00:00
-- url     : https://prove2.me/submissions/eb4501fa-712e-41ff-a18a-dbae2faf1fea

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
open Finset
variable (K : Type) [Field K] [Fintype K] (q : ℕ)
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution (hq : Fintype.card K = q ^ 2) : ∃ σ : K →+* K, ∀ x, σ x = x ^ q := by
  obtain ⟨p, hp⟩ := CharP.exists K
  obtain ⟨n, hpp, hn⟩ := FiniteField.card K p
  have : ExpChar K p := ExpChar.prime hpp
  have hdvd : q ∣ p ^ (n : ℕ) := by rw [← hn, hq]; exact Dvd.intro_left q (by ring)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hpp).1 hdvd
  refine ⟨iterateFrobenius K p m, fun x => ?_⟩
  rw [iterateFrobenius_def, hm]
end Formalism.FourierDecayAlt.P.S3x6
