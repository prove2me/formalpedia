-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.dualRadiiInequalities
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:34.487845+00:00
-- url     : https://prove2.me/submissions/44029635-745d-4272-a670-6aade5a4bee1

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneLetterRadiusIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
universe u
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
private theorem cancel_lemma {d : ℕ} {s s' : ZMod d} {a i : ℕ}
    (h : s + ((a + i : ℕ) : ZMod d) = s' + (a : ZMod d)) : s + (i : ZMod d) = s' := by
  rw [Nat.cast_add] at h
  linear_combination h
private theorem odd_of_odd_add_add_self {a i : ℕ} (h : Odd (a + i + a)) : Odd i := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k - a, by omega⟩
private theorem odd_of_odd_self_add_add {a i : ℕ} (h : Odd (a + (a + i))) : Odd i := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k - a, by omega⟩
private theorem exists_dTop_eq_le_of_odd_of_mem {d : ℕ} [NeZero d] {TT : Finset (ZMod d)} {s : ZMod d} {i : ℕ} (hi : Odd i)
    (hm : s + (i : ZMod d) ∈ TT) : ∃ e : ℕ, dTop d TT s = e ∧ e ≤ i := by
  have hle : dTop d TT s ≤ (i : ℕ∞) := by
    unfold dTop
    exact iInf₂_le i ⟨hi, hm⟩
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top i) hle)
  refine ⟨e, he.symm, ?_⟩
  rw [← he] at hle
  exact_mod_cast hle
end Formalism.DworkPowerSeriesWeights
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : ThmARadii := by
  unfold ThmARadii
  intro l d _ hl hd2 hd TT sig eps hdual hsig heps hT
  unfold IsDualAll at hdual
  have hL : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have hL0 : (0 : ℝ) < l := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s s' α β τ τ' hτ hτ' hodd heq
    rcases le_total β α with h | h
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
      have hi := odd_of_odd_add_add_self hodd
      have hs := cancel_lemma heq
      have hD := hdual s i hi
      rw [hs] at hD
      have hb : (1 : ℝ) ≤ (l : ℝ) ^ β := one_le_pow₀ hL
      calc (1 : ℝ) ≤ (l : ℝ) ^ β := hb
        _ = (l : ℝ) ^ β * 1 := (mul_one _).symm
        _ ≤ (l : ℝ) ^ β * ((l : ℝ) ^ i * sig s + sig s') := mul_le_mul_of_nonneg_left hD (by positivity)
        _ = (l : ℝ) ^ β * (l : ℝ) ^ i * sig s + (l : ℝ) ^ β * sig s' := by ring
        _ ≤ (l : ℝ) ^ β * (l : ℝ) ^ i * τ + (l : ℝ) ^ β * τ' :=
          add_le_add (mul_le_mul_of_nonneg_left hτ (by positivity))
            (mul_le_mul_of_nonneg_left hτ' (by positivity))
        _ = (l : ℝ) ^ (β + i) * τ + (l : ℝ) ^ β * τ' := by rw [pow_add]
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
      have hi := odd_of_odd_self_add_add hodd
      have hs := cancel_lemma heq.symm
      have hD := hdual s' i hi
      rw [hs] at hD
      have hb : (1 : ℝ) ≤ (l : ℝ) ^ α := one_le_pow₀ hL
      calc (1 : ℝ) ≤ (l : ℝ) ^ α := hb
        _ = (l : ℝ) ^ α * 1 := (mul_one _).symm
        _ ≤ (l : ℝ) ^ α * ((l : ℝ) ^ i * sig s' + sig s) := mul_le_mul_of_nonneg_left hD (by positivity)
        _ = (l : ℝ) ^ α * sig s + (l : ℝ) ^ α * (l : ℝ) ^ i * sig s' := by ring
        _ ≤ (l : ℝ) ^ α * τ + (l : ℝ) ^ α * (l : ℝ) ^ i * τ' :=
          add_le_add (mul_le_mul_of_nonneg_left hτ (by positivity))
            (mul_le_mul_of_nonneg_left hτ' (by positivity))
        _ = (l : ℝ) ^ α * τ + (l : ℝ) ^ (α + i) * τ' := by rw [pow_add]
  · intro s β j τ _ hτ
    have hb : (1 : ℝ) ≤ (l : ℝ) ^ β := one_le_pow₀ hL
    have h1 := mul_le_mul_of_nonneg_left hτ (by positivity : (0 : ℝ) ≤ (l : ℝ) ^ β)
    rw [pow_add]
    nlinarith
  · intro s α j τ _ hτ
    have hb : (1 : ℝ) ≤ (l : ℝ) ^ α := one_le_pow₀ hL
    have hj0 : (0 : ℝ) < (l : ℝ) ^ j := by positivity
    have h1 := mul_le_mul_of_nonneg_left hτ (by positivity : (0 : ℝ) ≤ (l : ℝ) ^ α * (l : ℝ) ^ j)
    have e : (l : ℝ) ^ α * (l : ℝ) ^ j * ((l : ℝ) ^ j)⁻¹ = (l : ℝ) ^ α := by
      rw [mul_assoc, mul_inv_cancel₀ hj0.ne', mul_one]
    have h2 : 0 ≤ (l : ℝ) ^ α * eps s := mul_nonneg (by positivity) (heps s)
    rw [pow_add]
    linarith
  · intro s hs s' hs' α β hodd heq
    rcases le_total β α with h | h
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
      have hi := odd_of_odd_add_add_self hodd
      have hss := cancel_lemma heq
      obtain ⟨e, he, hei⟩ := exists_dTop_eq_le_of_odd_of_mem (TT := TT) hi (hss ▸ hs')
      have hε := hT s hs e he
      have hpe : (0 : ℝ) < (l : ℝ) ^ e := by positivity
      have hei' : (l : ℝ) ^ e ≤ (l : ℝ) ^ i := pow_le_pow_right₀ hL hei
      have h1 : (l : ℝ) ^ (β + i) * ((l : ℝ) ^ e)⁻¹ ≤ (l : ℝ) ^ (β + i) * eps s :=
        mul_le_mul_of_nonneg_left hε (by positivity)
      have h2 : (l : ℝ) ^ β ≤ (l : ℝ) ^ (β + i) * ((l : ℝ) ^ e)⁻¹ := by
        rw [pow_add, mul_assoc, le_mul_iff_one_le_right (by positivity), le_mul_inv_iff₀ hpe, one_mul]
        exact hei'
      have hb : (1 : ℝ) ≤ (l : ℝ) ^ β := one_le_pow₀ hL
      have h3 : 0 ≤ (l : ℝ) ^ β * eps s' := mul_nonneg (by positivity) (heps s')
      linarith
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
      have hi := odd_of_odd_self_add_add hodd
      have hss := cancel_lemma heq.symm
      obtain ⟨e, he, hei⟩ := exists_dTop_eq_le_of_odd_of_mem (TT := TT) hi (hss ▸ hs)
      have hε := hT s' hs' e he
      have hpe : (0 : ℝ) < (l : ℝ) ^ e := by positivity
      have hei' : (l : ℝ) ^ e ≤ (l : ℝ) ^ i := pow_le_pow_right₀ hL hei
      have h1 : (l : ℝ) ^ (α + i) * ((l : ℝ) ^ e)⁻¹ ≤ (l : ℝ) ^ (α + i) * eps s' :=
        mul_le_mul_of_nonneg_left hε (by positivity)
      have h2 : (l : ℝ) ^ α ≤ (l : ℝ) ^ (α + i) * ((l : ℝ) ^ e)⁻¹ := by
        rw [pow_add, mul_assoc, le_mul_iff_one_le_right (by positivity), le_mul_inv_iff₀ hpe, one_mul]
        exact hei'
      have hb : (1 : ℝ) ≤ (l : ℝ) ^ α := one_le_pow₀ hL
      have h3 : 0 ≤ (l : ℝ) ^ α * eps s := mul_nonneg (by positivity) (heps s)
      linarith
end Formalism.DworkPowerSeriesWeights
