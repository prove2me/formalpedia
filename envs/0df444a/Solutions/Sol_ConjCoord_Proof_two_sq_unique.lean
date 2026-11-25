-- Prove2me | solution 1 for ConjCoord.Proof.two_sq_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:34.380563+00:00
-- url     : https://prove2.me/submissions/fe79e109-35c7-4840-82aa-6028010ac1d2

module
public import Definitions.Def_ConjCoord_Reps
public import Definitions.Def_ConjCoord_TwoSquares

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution {p : ℤ} (hp : Prime p) (hodd : p % 2 = 1) {α β γ δ : ℤ} (hα : 0 < α)
    (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ) (h1 : α ^ 2 + β ^ 2 = p) (h2 : γ ^ 2 + δ ^ 2 = p)
    (hβe : Even β) (hδe : Even δ) : α = γ ∧ β = δ := by
  subst h1
  set p := α ^ 2 + β ^ 2 with hpdef
  have hp0 : 0 < p := by positivity
  have key : p ∣ (α * δ - β * γ) * (α * δ + β * γ) :=
    ⟨α ^ 2 + δ ^ 2 - p, by linear_combination (-β ^ 2) * h2⟩
  have hαδ : α * δ < p := by nlinarith [sq_nonneg (α - δ)]
  have hβγ : β * γ < p := by nlinarith [sq_nonneg (β - γ)]
  have pos1 : 0 < α * δ := mul_pos hα hδ
  have pos2 : 0 < β * γ := mul_pos hβ hγ
  rcases hp.dvd_or_dvd key with hd | hd
  · have e : α * δ - β * γ = 0 :=
      Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
    have e2 : p * (β ^ 2 - δ ^ 2) = 0 := by
      linear_combination (-(α * δ + β * γ)) * e + (-β ^ 2) * h2
    have e3 : β ^ 2 - δ ^ 2 = 0 := by
      rcases mul_eq_zero.mp e2 with h | h
      · omega
      · exact h
    have hbd : β = δ := by nlinarith [sq_nonneg (β - δ), sq_nonneg (β + δ)]
    subst hbd
    refine ⟨?_, rfl⟩
    have : α ^ 2 = γ ^ 2 := by linarith
    nlinarith [sq_nonneg (α - γ), sq_nonneg (α + γ)]
  · obtain ⟨k, hk⟩ := hd
    have hk1 : k = 1 := by
      have : 0 < k := by
        by_contra hc; push_neg at hc; nlinarith
      have : k < 2 := by
        by_contra hc; push_neg at hc; nlinarith
      omega
    subst hk1
    have hsum : (α * γ - β * δ) ^ 2 + (α * δ + β * γ) ^ 2 = p * p := by
      linear_combination (α ^ 2 + β ^ 2) * h2
    have e : (α * γ - β * δ) ^ 2 = 0 := by rw [hk] at hsum; linarith
    have e' : α * γ - β * δ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e
    have e2 : p * (β ^ 2 - γ ^ 2) = 0 := by
      linear_combination (-(α * γ + β * δ)) * e' + (-β ^ 2) * h2
    have e3 : β ^ 2 - γ ^ 2 = 0 := by
      rcases mul_eq_zero.mp e2 with h | h
      · omega
      · exact h
    have hbg : γ = β := by nlinarith [sq_nonneg (γ - β), sq_nonneg (γ + β)]
    subst hbg
    have hda : δ = α := by
      have : δ ^ 2 = α ^ 2 := by linarith
      nlinarith [sq_nonneg (δ - α), sq_nonneg (δ + α)]
    subst hda
    obtain ⟨s, hs⟩ := hδe
    obtain ⟨t, ht⟩ := hβe
    exfalso
    have : p = 4 * (s ^ 2 + t ^ 2) := by rw [hpdef, hs, ht]; ring
    omega
end ConjCoord.Proof
