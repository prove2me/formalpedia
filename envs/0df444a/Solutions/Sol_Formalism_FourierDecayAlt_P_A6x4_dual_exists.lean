-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x4.dual_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:16.29035+00:00
-- url     : https://prove2.me/submissions/1751b06b-4fc5-4be8-9c05-c262a6a165d9

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_sum_reps_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_reps_nonempty
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_mem_mulR_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_psi_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_isLat_mulR
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_exists_reps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x4
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x4
theorem _root_.solution (hD : LocalDatum K R ψ) {a b : K} (hab : a * b = 1) (ha : a ∈ R)
    (χ : AddChar R ℂ) (hχ : ∀ r : R, (r : K) ∈ mulR R a → χ r = 1) :
    ∃ z : K, ∀ r : R, χ r = ψ (z * (r : K)) := by
  classical
  obtain ⟨S, hS⟩ := exists_reps (L := R.toAddSubgroup) (M := mulR R a) hD.isCompact
    (isLat_mulR hD hab).1
  have hle : mulR R a ≤ R.toAddSubgroup := by
    intro x hx
    have h := (mem_mulR_iff hab x).1 hx
    have e : x = a * (b * x) := by linear_combination (-x) * hab
    rw [e]
    exact R.mul_mem ha h
  by_contra hcon
  push Not at hcon
  let X : K → ℂ := fun x => if h : x ∈ R then χ ⟨x, h⟩ else 0
  have hX : ∀ (x : K) (h : x ∈ R), X x = χ ⟨x, h⟩ := fun x h => dif_pos h
  have hSR : ∀ s ∈ S, s ∈ R := fun s hs => hS.1 s hs

  have h1 : ∀ s ∈ S, ∑ r ∈ S, X r * ψ (b * s * r) = 0 := by
    intro s hs
    obtain ⟨r, hr⟩ := hcon (-(b * s))
    refine sum_reps_eq_zero hle hS (fun x => X x * ψ (b * s * x)) ?_ ?_ (l₀ := (r : K)) r.2 ?_
    · intro x hx y hy
      have hxy : x + y ∈ R := R.add_mem hx hy
      show X (x + y) * ψ (b * s * (x + y)) = X x * ψ (b * s * x) * (X y * ψ (b * s * y))
      rw [hX _ hxy, hX _ hx, hX _ hy, mul_add, AddChar.map_add_eq_mul]
      have : (⟨x + y, hxy⟩ : R) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, AddChar.map_add_eq_mul]
      ring
    · intro l hl
      have hlR : l ∈ R := hle hl
      show X l * ψ (b * s * l) = 1
      rw [hX _ hlR, hχ ⟨l, hlR⟩ hl, one_mul]
      apply psi_one hD
      have e : b * s * l = s * (b * l) := by ring
      rw [e]
      exact R.mul_mem (hSR s hs) ((mem_mulR_iff hab l).1 hl)
    · show X (r : K) * ψ (b * s * (r : K)) ≠ 1
      intro h
      apply hr
      rw [hX _ r.2] at h
      have h2 : ψ (b * s * (r : K)) * ψ (-(b * s) * (r : K)) = 1 := by
        rw [← AddChar.map_add_eq_mul]
        have : b * s * (r : K) + -(b * s) * (r : K) = 0 := by ring
        rw [this, AddChar.map_zero_eq_one]
      calc χ r = χ r * (ψ (b * s * (r : K)) * ψ (-(b * s) * (r : K))) := by rw [h2, mul_one]
        _ = (χ ⟨(r : K), r.2⟩ * ψ (b * s * (r : K))) * ψ (-(b * s) * (r : K)) := by ring
        _ = ψ (-(b * s) * (r : K)) := by rw [h, one_mul]

  obtain ⟨r₀, ⟨hr₀S, hr₀⟩, huniq⟩ := hS.2 0 R.toAddSubgroup.zero_mem
  have hr₀a : r₀ ∈ mulR R a := by
    have := (mulR R a).neg_mem hr₀
    simpa using this
  have h2 : ∀ r ∈ S, r ≠ r₀ → ∑ s ∈ S, ψ (b * s * r) = 0 := by
    intro r hr hne
    have hnot : ¬ b * r ∈ R := by
      intro h
      apply hne
      apply huniq
      refine ⟨hr, ?_⟩
      rw [zero_sub]
      exact (mulR R a).neg_mem ((mem_mulR_iff hab r).2 h)
    have hex : ∃ t ∈ R, ψ (b * r * t) ≠ 1 := by
      by_contra hc
      push Not at hc
      exact hnot ((hD.selfDual _).1 hc)
    obtain ⟨t, ht, hne'⟩ := hex
    refine sum_reps_eq_zero hle hS (fun x => ψ (b * x * r)) ?_ ?_ (l₀ := t) ht ?_
    · intro x _ y _
      show ψ (b * (x + y) * r) = ψ (b * x * r) * ψ (b * y * r)
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    · intro l hl
      apply psi_one hD
      have e : b * l * r = (b * l) * r := by ring
      rw [e]
      exact R.mul_mem ((mem_mulR_iff hab l).1 hl) (hSR r hr)
    · show ψ (b * t * r) ≠ 1
      have e : b * t * r = b * r * t := by ring
      rw [e]
      exact hne'
  have h3 : ∑ s ∈ S, ψ (b * s * r₀) = (S.card : ℂ) := by
    have : ∑ s ∈ S, ψ (b * s * r₀) = ∑ s ∈ S, (1 : ℂ) := by
      refine Finset.sum_congr rfl fun s hs => psi_one hD ?_
      have e : b * s * r₀ = s * (b * r₀) := by ring
      rw [e]
      exact R.mul_mem (hSR s hs) ((mem_mulR_iff hab r₀).1 hr₀a)
    rw [this, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h4 : ∑ s ∈ S, ∑ r ∈ S, X r * ψ (b * s * r) = (S.card : ℂ) := by
    rw [Finset.sum_comm]
    have : ∀ r ∈ S, ∑ s ∈ S, X r * ψ (b * s * r) = X r * ∑ s ∈ S, ψ (b * s * r) :=
      fun r _ => (Finset.mul_sum _ _ _).symm
    rw [Finset.sum_congr rfl this, Finset.sum_eq_single r₀]
    · rw [h3, hX _ (hSR r₀ hr₀S), hχ _ hr₀a, one_mul]
    · intro r hr hne
      rw [h2 r hr hne, mul_zero]
    · intro h
      exact absurd hr₀S h
  rw [Finset.sum_congr rfl h1, Finset.sum_const_zero] at h4
  have hc : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 (reps_nonempty hS)).ne'
  exact hc h4.symm
end Formalism.FourierDecayAlt.P.A6x4
