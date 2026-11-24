-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.aut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:19:17.710095+00:00
-- url     : https://prove2.me/submissions/7e296c13-3bfa-4f39-b279-88bcd9ecbac5

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_z_spec
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_pow_mod_of

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
theorem _root_.solution (N : ℕ) [NeZero N] (v : ℕ) (hv : v.Coprime N) :
    ∃ σ : Cyc N ≃ₐ[ℚ] Cyc N, ∀ w : Cyc N, w ^ N = 1 → σ w = w ^ v := by
  have hpos : 0 < N := NeZero.pos N
  have hirr : Irreducible (cyclotomic N ℚ) := cyclotomic.irreducible_rat hpos
  let u : (ZMod N)ˣ := ZMod.unitOfCoprime v hv
  refine ⟨(IsCyclotomicExtension.autEquivPow (Cyc N) hirr).symm u, fun w hw => ?_⟩
  have hu : (IsCyclotomicExtension.autEquivPow (Cyc N) hirr)
      ((IsCyclotomicExtension.autEquivPow (Cyc N) hirr).symm u) = u := MulEquiv.apply_symm_apply _ _
  have hz : (IsCyclotomicExtension.autEquivPow (Cyc N) hirr).symm u (z N) = z N ^ v := by
    have h2 := (z_spec N).autToPow_spec ℚ ((IsCyclotomicExtension.autEquivPow (Cyc N) hirr).symm u)
    have h3 : ((z_spec N).autToPow ℚ ((IsCyclotomicExtension.autEquivPow (Cyc N) hirr).symm u) :
        ZMod N) = (v : ZMod N) := by
      rw [show (z_spec N).autToPow ℚ ((IsCyclotomicExtension.autEquivPow (Cyc N) hirr).symm u)
         = u from hu]
      simp [u]
    rw [← h2, h3, ZMod.val_natCast]
    exact pow_mod_of (z_spec N).pow_eq_one v
  obtain ⟨i, -, rfl⟩ := (z_spec N).eq_pow_of_pow_eq_one hw
  rw [map_pow, hz, ← pow_mul, ← pow_mul, mul_comm]
end Formalism.FrobeniusOrbits.Cond
