-- Prove2me | solution 1 for Formalism.L2.Col.eq_prW_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:46:16.197589+00:00
-- url     : https://prove2.me/submissions/9b7cad7f-9cf1-4905-bb44-5e34c951ba28

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
import Theorems.Thm_Formalism_L2_Col_prW_prime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.Col
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : q.Prime)
    (h : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : q = prW w := by
  have h1 : ((q : ℕ) : ℤ) ∈ w.asIdeal.under ℤ := by
    rw [Ideal.under, Ideal.mem_comap]; simpa using h
  rw [← Int.ideal_span_absNorm_eq_self (w.asIdeal.under ℤ), Ideal.mem_span_singleton] at h1
  have h2 : prW w ∣ q := by unfold prW; exact_mod_cast h1
  exact ((Nat.prime_dvd_prime_iff_eq (prW_prime w) hq).1 h2).symm
end Formalism.L2.Col
