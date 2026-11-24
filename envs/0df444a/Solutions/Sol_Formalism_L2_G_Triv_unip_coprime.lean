-- Prove2me | solution 1 for Formalism.L2.G.Triv.unip_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:08:34.604395+00:00
-- url     : https://prove2.me/submissions/14c95278-fe7a-497c-8998-4368ef72db9a

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ClosureUpperUni
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddPowOfMulSelfEqZero
import Definitions.Def_Lemmata_GeneralBFactLeftTail_Imports
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_OneAddPowOfSq
import Theorems.Thm_Formalism_L2_G_Triv_unip_pow
import Theorems.Thm_Formalism_L2_G_Triv_cong_coprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {R : Type} [CommRing R] {k : ℕ}
namespace Formalism.L2.G.Triv
theorem _root_.solution (I : Ideal R) (hinf : (⨅ m : ℕ, I ^ m) = ⊥) (g : ℕ) (hg : g.Prime) (hgI : (g : R) ∈ I)
    (A : Matrix (Fin k) (Fin k) R) (hA : ∀ i j, j ≤ i → (A - 1) i j ∈ I) (N : ℕ) (hN : IsUnit (N : R))
    (hc : Nat.Coprime N g) (hAN : A ^ N = 1) : A = 1 := by
  obtain ⟨s, hs⟩ : ∃ s, k ≤ g ^ s := ⟨k, (Nat.lt_pow_self hg.one_lt).le⟩
  have h1 : A ^ (g ^ s) = 1 :=
    cong_coprime I hinf _ (unip_pow I g hg hgI A hA s hs) N hN (by rw [← pow_mul, mul_comm, pow_mul, hAN, one_pow])
  have h2 := pow_gcd_eq_one.2 ⟨hAN, h1⟩
  rwa [Nat.Coprime.pow_right s hc, pow_one] at h2
end Formalism.L2.G.Triv
