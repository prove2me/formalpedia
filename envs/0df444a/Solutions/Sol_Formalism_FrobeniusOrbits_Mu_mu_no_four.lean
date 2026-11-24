-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Mu.mu_no_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:08:48.124272+00:00
-- url     : https://prove2.me/submissions/701a0c41-e2d2-4abb-af84-379966ff70d8

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_MuCardLeTwo
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_galMap_zeta_inversion
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_mem_hostE_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Mu
variable {L : Type} [Field L] [NumberField L]
variable {e q d : ℕ} {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Mu
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (y : L)
    (hyE : y ∈ hostE ζ a b) (hy : IsPrimitiveRoot y 4) : False := by
  have hfix : Galois.tau0 hqd h y = y := (Formalism.FrobeniusOrbits.Galois.mem_hostE_iff hqd h y).mp hyE
  have hζ := h.1
  have hτζ : Galois.tau0 hqd h ζ = ζ⁻¹ := by
    have hg := Formalism.FrobeniusOrbits.Galois.galMap_zeta_inversion hqd h
    have hau : hζ.autToPow ℚ (Galois.tau0 hqd h) = -1 := congrArg Prod.fst hg
    have hspec : ζ ^ ((hζ.autToPow ℚ (Galois.tau0 hqd h) : ZMod (2 ^ (e + 2))).val) = Galois.tau0 hqd h ζ := by
      first
        | exact hζ.autToPow_spec ℚ (Galois.tau0 hqd h)
        | exact hζ.autToPow_spec (Galois.tau0 hqd h)
    rw [← hspec, hau]
    set v := (((-1 : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2)))).val with hvdef
    have hz : ((v + 1 : ℕ) : ZMod (2 ^ (e + 2))) = 0 := by
      rw [Nat.cast_add, hvdef, ZMod.natCast_zmod_val]
      simp
    have hv : 2 ^ (e + 2) ∣ v + 1 := by
      first
        | exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp hz
        | exact (ZMod.natCast_eq_zero_iff _ _).mp hz
        | exact (ZMod.natCast_self_eq_zero_iff _ _).mp hz
    have h1 := (hζ.pow_eq_one_iff_dvd _).mpr hv
    rw [pow_succ] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hyN : y ^ (2 ^ (e + 2)) = 1 := by
    rw [show 2 ^ (e + 2) = 4 * 2 ^ e by ring, pow_mul, hy.pow_eq_one, one_pow]
  haveI : NeZero (2 ^ (e + 2)) := ⟨by positivity⟩
  obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one hyN
  have hτy : Galois.tau0 hqd h y = y⁻¹ := by
    rw [← hj, map_pow, hτζ, inv_pow]
  rw [hτy] at hfix
  have hy0 : y ≠ 0 := hy.ne_zero (by norm_num)
  have hy2 : y ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [← hfix]
    exact inv_mul_cancel₀ hy0
  have h4 := (hy.pow_eq_one_iff_dvd 2).mp hy2
  norm_num at h4
end Formalism.FrobeniusOrbits.Mu
