-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.hecke_operator_terms
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:47.601536+00:00
-- url     : https://prove2.me/submissions/1c37326d-503b-4e20-bcd7-05b1237a85e0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CardUnitsZmodPrimeSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
private lemma card_units_zmod_prime_sq (p : ℕ) (hp : p.Prime) [NeZero (p ^ 2)] :
    (Finset.univ.filter (fun a : ZMod (p ^ 2) => IsUnit a)).card = p * (p - 1) := by
  classical
  have h1 : Finset.univ.filter (fun a : ZMod (p ^ 2) => IsUnit a)
      = (Finset.univ : Finset (ZMod (p ^ 2))ˣ).map ⟨Units.val, Units.val_injective⟩ := by
    ext a
    constructor
    · intro ha
      obtain ⟨u, hu⟩ := (Finset.mem_filter.mp ha).2
      exact Finset.mem_map.mpr ⟨u, Finset.mem_univ _, hu⟩
    · intro ha
      obtain ⟨u, _, hu⟩ := Finset.mem_map.mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨u, hu⟩⟩
  rw [h1, Finset.card_map, Finset.card_univ, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow hp (by norm_num)]
  simp
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : SW_hecke_terms := by
  classical
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hp1 : 1 ≤ p := hp.one_lt.le
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  constructor
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card, ZMod.card_units_eq_totient,
      Nat.totient_prime hp]
    simp
    ring
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow hp (by norm_num), Fintype.card_subtype]
    have hU := card_units_zmod_prime_sq (k + 1) hp
    have hN : (Finset.univ.filter (fun a : ZMod ((k + 1) ^ 2) => ¬ IsUnit a)).card = k + 1 := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod ((k + 1) ^ 2))))
        (fun a => IsUnit a)
      rw [hU, Finset.card_univ, ZMod.card] at this
      simp at this
      nlinarith
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (ZMod ((k + 1) ^ 2) × ZMod ((k + 1) ^ 2))))
      (fun v => IsUnit v.1 ∨ IsUnit v.2)
    have hcompl : (Finset.univ.filter
        (fun v : ZMod ((k + 1) ^ 2) × ZMod ((k + 1) ^ 2) => ¬ (IsUnit v.1 ∨ IsUnit v.2)))
        = (Finset.univ.filter (fun a : ZMod ((k + 1) ^ 2) => ¬ IsUnit a)) ×ˢ
          (Finset.univ.filter (fun a : ZMod ((k + 1) ^ 2) => ¬ IsUnit a)) := by
      ext v
      simp [not_or]
    rw [hcompl, Finset.card_product, hN, Finset.card_univ, Fintype.card_prod, ZMod.card] at hsplit
    simp
    nlinarith
end Formalism.HermitianLattices.GenusMassVolumes
