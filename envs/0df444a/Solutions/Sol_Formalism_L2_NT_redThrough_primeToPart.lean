-- Prove2me | solution 1 for Formalism.L2.NT.redThrough_primeToPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:54.884565+00:00
-- url     : https://prove2.me/submissions/70124d57-1235-467f-afff-5c3ac044ee88

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Theorems.Thm_Formalism_L2_NT_mem_of_pow_eq_one
import Theorems.Thm_Formalism_L2_NT_redThrough_one
import Theorems.Thm_Formalism_L2_NT_redThrough_pow
import Theorems.Thm_Formalism_L2_NT_pow_eq_one_of_charP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
open Formalism Formalism.L2 Formalism.L2.NT
open Formalism.L2.Host
variable {Ω : Type} [Field Ω]
variable (B : ValuationSubring Ω) {l : ℕ} [Fact l.Prime] (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l)
namespace Formalism.L2.NT
theorem _root_.solution {M : Type} [Monoid M] (t : M →* Ω) (u : M) (hu : 0 < orderOf u) :
    redThrough B κ (t (Formalism.CyclotomicNorms.primeToPart l u)) = redThrough B κ (t u) := by
  have hB : t u ∈ B := mem_of_pow_eq_one B hu (by rw [← map_pow, pow_orderOf_eq_one, map_one])
  set y := redThrough B κ (t u) with hy
  set m := orderOf u
  set a := m.factorization l
  set m' := m / l ^ a
  have hm : l ^ a * m' = m := Nat.ordProj_mul_ordCompl_eq_self m l
  have hy1 : y ^ m = 1 := by
    rw [hy, ← redThrough_pow B κ hB, ← map_pow, pow_orderOf_eq_one, map_one, redThrough_one]
  haveI : CharP (Formalism.CyclotomicNorms.Fbar l) l := inferInstance
  have hy2 : y ^ m' = 1 := pow_eq_one_of_charP l y a m' (by rw [hm]; exact hy1)
  have hm'0 : m' ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hm
    exact hu.ne' hm.symm
  haveI : NeZero m' := ⟨hm'0⟩
  have hcop : Nat.Coprime (l ^ a) m' :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl (Fact.out : l.Prime) hu.ne')
  have hc : ((l ^ a * ((l ^ a : ℕ) : ZMod m')⁻¹.val : ℕ) : ZMod m') = ((1 : ℕ) : ZMod m') := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ hcop
  rw [ZMod.natCast_eq_natCast_iff'] at hc
  unfold Formalism.CyclotomicNorms.primeToPart
  rw [map_pow, redThrough_pow B κ hB, ← hy, pow_eq_pow_mod _ hy2, hc, ← pow_eq_pow_mod _ hy2, pow_one]
end Formalism.L2.NT
