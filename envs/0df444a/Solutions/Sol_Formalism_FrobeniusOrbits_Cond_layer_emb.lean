-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.layer_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:18:21.468909+00:00
-- url     : https://prove2.me/submissions/5b999fcf-f63d-4fc9-b212-f61ec75eadbe

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_splits_of_dvd
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_splits_pow
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_splits_sq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_prim_pow
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_sqrt_exists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IntermediateField Polynomial
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace Cond
section Gauss
variable {K : Type*} [Field K] [CharZero K]
end Gauss
section Cyc
end Cyc
section Div
private theorem X_sq_add_C_natCast_ne_zero (c : ℕ) : (X ^ 2 + C (c : ℚ) : ℚ[X]) ≠ 0 := by
  exact (Polynomial.monic_X_pow_add_C _ two_ne_zero).ne_zero
end Div
section Two
end Two
end Cond
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Cond
namespace Formalism.FrobeniusOrbits.Cond
theorem _root_.solution {n q d : ℕ} [Fact q.Prime] [Fact d.Prime] (hq4 : q % 4 = 3) (hd4 : d % 4 = 3)
    {L : Type*} [Field L] [NumberField L] {ζ a b : L} (h : IsLayer n q d ζ a b)
    {N : ℕ} [NeZero N] (h2 : 2 ^ n ∣ N) (hq : q ∣ N) (hd : d ∣ N) :
    Nonempty (L →ₐ[ℚ] Cyc N) := by
  obtain ⟨gq, hgq⟩ := sqrt_exists hq4 hq
  obtain ⟨gd, hgd⟩ := sqrt_exists hd4 hd
  have hne : (X ^ (2 ^ n) - 1 : ℚ[X]) ≠ 0 := by
    simpa using Polynomial.X_pow_sub_C_ne_zero (pow_pos two_pos n) (1 : ℚ)
  have hfacts : ∀ x ∈ ({ζ, a, b} : Set L),
      IsIntegral ℚ x ∧ ((minpoly ℚ x).map (algebraMap ℚ (Cyc N))).Splits := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact splits_of_dvd _ (X ^ (2 ^ n) - 1) hne (by simp [h.1.pow_eq_one])
        (splits_pow (prim_pow h2))
    · exact splits_of_dvd _ _ (X_sq_add_C_natCast_ne_zero q) (by simp [h.2.1]) (splits_sq q gq hgq)
    · exact splits_of_dvd _ _ (X_sq_add_C_natCast_ne_zero d) (by simp [h.2.2.1]) (splits_sq d gd hgd)
  exact IntermediateField.nonempty_algHom_of_adjoin_splits hfacts h.2.2.2
end Formalism.FrobeniusOrbits.Cond
