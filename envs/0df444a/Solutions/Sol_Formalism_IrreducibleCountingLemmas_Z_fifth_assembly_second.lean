-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.fifth_assembly_second
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:11:48.963147+00:00
-- url     : https://prove2.me/submissions/1ad3447b-ed82-481b-983b-81a595028b44

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_monic_of_eval_monic
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_fifth_factor_monic
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_charpoly_eq_restrict_mul_scalar
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_charpolyFactorAnnihilator
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_g5b_multiplicity_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Topology
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : FactorAnnihilatorFamily := by
  intro O K _ _ _ _ hinj X' _ T hT V _ _ _ A B γ₀ γ c cγ t F hF hAB hA0 hA hB0 hB hfr hmult
  have := hT
  have hDm : ((X - C c : O[X]) ^ t).Monic := (monic_X_sub_C _).pow t
  have hDK : ((X - C c : O[X]) ^ t).map (algebraMap O K) = (X - C (algebraMap O K c)) ^ t := by
    rw [Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]
  have hsplit : ∀ x, (γ₀ x).charpoly =
      ((γ₀ x).restrict (hA0 x)).charpoly * (X - C (algebraMap O K c)) ^ t := by
    intro x
    have := charpoly_eq_restrict_mul_scalar (A x) (B x) (γ₀ x) (algebraMap O K c) (hAB x) (hA0 x) (hB0 x)
    rwa [hfr x] at this
  have hFx : ∀ x, F.map (ev T x) = (F.map (ev T x) /ₘ (X - C c) ^ t) * (X - C c) ^ t := by
    intro x
    have hrem : F.map (ev T x) %ₘ (X - C c) ^ t = 0 := by
      apply Polynomial.map_injective _ hinj
      rw [map_modByMonic _ hDm, hDK, hF x, hsplit x, Polynomial.map_zero]
      exact (modByMonic_eq_zero_iff_dvd ((monic_X_sub_C _).pow t)).2 (dvd_mul_left _ _)
    have := modByMonic_add_div (F.map (ev T x)) ((X - C c) ^ t)
    rw [hrem, zero_add] at this
    rw [mul_comm]; exact this.symm
  have hFm : ∀ x, (F.map (ev T x)).Monic := by
    intro x
    apply monic_of_injective hinj
    rw [hF x]; exact LinearMap.charpoly_monic _
  have hsm : ∀ x, (F.map (ev T x) /ₘ (X - C c) ^ t).Monic := by
    intro x
    have := hFm x
    rw [hFx x] at this
    exact Monic.of_mul_monic_right hDm this
  have hunit : ∀ x, IsUnit ((F.map (ev T x) /ₘ (X - C c) ^ t).eval c) := by
    intro x
    apply g5b_multiplicity_holds O t c _ (hsm x)
    rw [← hFx x]; exact hmult x
  obtain ⟨P, hPm, hP1, hP2, hP3⟩ := fifth_factor_monic O X' T hT t c F
    (fun x => F.map (ev T x) /ₘ (X - C c) ^ t) (monic_of_eval_monic T F hFm) hFx hunit
  refine ⟨P, hPm, hP1, hP2, fun x => ?_⟩
  apply charpolyFactorAnnihilator K (V x) (A x) (B x) (γ₀ x) (γ x) (algebraMap O K c) (algebraMap O K cγ) t _
    (hAB x) (hA0 x) (hA x) (hB0 x) (hB x) (hfr x)
  rw [hP3 x, ← hF x, ← hDK, ← Polynomial.map_mul, ← hFx x]
end Formalism.IrreducibleCountingLemmas.Z
