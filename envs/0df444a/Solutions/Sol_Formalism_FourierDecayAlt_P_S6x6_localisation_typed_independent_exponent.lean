-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x6.localisation_typed_independent_exponent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:46.226731+00:00
-- url     : https://prove2.me/submissions/78611885-5fc8-45b8-9531-4da6793c115e

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationTypedIndependentExponent
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_exists_real_mem_different
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_dd_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_dd_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x6
open NumberField NumberField.IsCMField Module Formalism.FourierDecayAlt.S6
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x6
theorem _root_.solution (g : ℕ) (k ν ν' : ℤ) (hc : PrimeToDifferent E g)
    (P : Ideal (𝓞 (maximalRealSubfield E))) (hP : P.IsPrime)
    (hgP : (g : 𝓞 (maximalRealSubfield E)) ∈ P) (t : E)
    (ht : t ∈ locAt E P (zsub E (idl E g k ν))) : t ∈ locAt E P (zsub E (idl E g k ν')) := by
  obtain ⟨a, haP, ha⟩ := exists_real_mem_different E g hc P hP hgP
  obtain ⟨b, hb, h⟩ := ht
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ν' ≤ ν + n := ⟨(ν' - ν).toNat, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (n : ℤ) + ν = m + ν' := ⟨(ν + n - ν').toNat, by omega⟩
  refine ⟨a ^ n * b, fun hh => (hP.mem_or_mem hh).elim (fun h' => haP (hP.mem_of_pow_mem _ h')) hb, ?_⟩
  change _ ∈ idl E g k ν at h
  show _ ∈ idl E g k ν'
  have ha' : algebraMap (𝓞 (maximalRealSubfield E)) E a ∈ dd E := by
    unfold dd
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨_, ha, rfl⟩
  have hpow : ∀ j : ℕ, algebraMap (𝓞 (maximalRealSubfield E)) E a ^ j ∈ dd E ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_succ]; exact FractionalIdeal.mul_mem_mul ih ha'
  have h1 : algebraMap (𝓞 (maximalRealSubfield E)) E a ^ n ∈ dd E ^ n :=
    hpow n
  have h2 := FractionalIdeal.mul_mem_mul h1 h
  have h3 : dd E ^ n * idl E g k ν = dd E ^ m * idl E g k ν' := by
    unfold idl
    rw [← mul_assoc, ← mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (dd_ne_zero E),
      ← zpow_add₀ (dd_ne_zero E), hm]
  have h4 : dd E ^ m * idl E g k ν' ≤ idl E g k ν' := by
    calc dd E ^ m * idl E g k ν' ≤ 1 * idl E g k ν' :=
          mul_le_mul_left (pow_le_one' (dd_le_one E) m) _
      _ = _ := one_mul _
  rw [map_mul, map_pow, mul_assoc]
  exact h4 (h3 ▸ h2)
end Formalism.FourierDecayAlt.P.S6x6
