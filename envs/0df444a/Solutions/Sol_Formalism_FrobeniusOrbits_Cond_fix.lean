-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:43:50.20538+00:00
-- url     : https://prove2.me/submissions/cc156d08-b0e9-4f7b-a013-97c1d6a17348

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_z_spec
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_pow_congr_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Cond
namespace Formalism.FrobeniusOrbits.Cond
theorem _root_.solution {m N : ℕ} [NeZero m] (hm : m ∣ N) (ι : Cyc m →ₐ[ℚ] Cyc N) (σ : Cyc N ≃ₐ[ℚ] Cyc N) (v : ℕ)
    (hσ : ∀ w : Cyc N, w ^ N = 1 → σ w = w ^ v) (hv : v % m = 1 % m) (y : Cyc m) :
    σ (ι y) = ι y := by
  have hext : (σ : Cyc N →ₐ[ℚ] Cyc N).comp ι = ι := by
    apply AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top (z_spec m))
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have h1 : (ι (z m)) ^ m = 1 := by rw [← map_pow, (z_spec m).pow_eq_one, map_one]
    have h2 : (ι (z m)) ^ N = 1 := by
      obtain ⟨k, hk⟩ := hm
      calc ι (z m) ^ N = ι (z m) ^ (m * k) := congrArg (fun n => ι (z m) ^ n) hk
        _ = 1 := by rw [pow_mul, h1, one_pow]
    show σ (ι (z m)) = ι (z m)
    rw [hσ _ h2, pow_congr_of h1 hv, pow_one]
  exact AlgHom.congr_fun hext y
end Formalism.FrobeniusOrbits.Cond
