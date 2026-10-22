-- Prove2me | solution 1 for FlexCommitRO.BoxExt.value_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:32:28.514053+00:00
-- url     : https://prove2.me/submissions/37123a85-f343-47a5-95ee-5c5b350827c6

import Mathlib
import Definitions.Def_FlexCommitRO_BoxExt_Setting
set_option autoImplicit false

open FlexCommitRO.BoxExt

lemma ZZC_feas_mono {T : ℕ} (D : RSFCData T) (U1 U2 : Fin T → Set ℝ) (hU : ∀ t, U1 t ⊆ U2 t)
    (pol : RSFCPolicy T) (h : Feasible D U2 pol) : Feasible D U1 pol := by
  have hp : Set.univ.pi U1 ⊆ Set.univ.pi U2 := Set.pi_mono (fun t _ => hU t)
  obtain ⟨hna, h1, h2, h3, h4⟩ := h
  refine ⟨?_, h1, h2, h3, fun d hd => h4 d (hp hd)⟩
  intro d hd d' hd'
  exact hna d (hp hd) d' (hp hd')

lemma ZZC_value_mono {T : ℕ} (D : RSFCData T) (U1 U2 : Fin T → Set ℝ) (hU : ∀ t, U1 t ⊆ U2 t) :
    value D U1 ≤ value D U2 := by
  have hp : Set.univ.pi U1 ⊆ Set.univ.pi U2 := Set.pi_mono (fun t _ => hU t)
  unfold value
  refine le_iInf₂ (fun pol hpol => ?_)
  refine (iInf₂_le pol (ZZC_feas_mono D U1 U2 hU pol hpol)).trans ?_
  exact iSup₂_le (fun d hd => le_iSup₂_of_le d (hp hd) le_rfl)

lemma ZZC_bdd {T : ℕ} (S : Set (Fin T → ℝ)) (hS : S.Finite) (g : (Fin T → ℝ) → ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ d ∈ S, |g d| ≤ R := by
  obtain ⟨B, hB⟩ := (hS.image (fun d => |g d|)).bddAbove
  refine ⟨max B 0, le_max_right _ _, fun d hd => ?_⟩
  exact (hB ⟨d, hd, rfl⟩).trans (le_max_left _ _)

lemma ZZC_exists_R {T : ℕ} (D : RSFCData T) (U : Fin T → Set ℝ) (hU : ∀ t, (U t).Finite)
    (pol : RSFCPolicy T) (h : Feasible D U pol) : ∃ R : ℝ, FeasibleR D U R pol := by
  have hS : (Set.univ.pi U).Finite := Set.Finite.pi hU
  obtain ⟨Rx, hRx0, hRx⟩ := ZZC_bdd (Set.univ.pi U) hS (fun d => ∑ k, |pol.x k d|)
  obtain ⟨Rq, hRq0, hRq⟩ := ZZC_bdd (Set.univ.pi U) hS
    (fun d => ∑ t : Fin T, (|pol.q t d| + |∑ τ ∈ Finset.univ.filter (· ≤ t), pol.q τ d| + |pol.y t d| + |pol.u t d|))
  have hw0 : 0 ≤ ∑ t, |pol.w t| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hz0 : 0 ≤ ∑ t, |pol.z t| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨(∑ t, |pol.w t|) + (∑ t, |pol.z t|) + Rx + Rq, h, ?_, ?_, ?_⟩
  · intro t
    have := Finset.single_le_sum (f := fun t => |pol.w t|) (fun _ _ => abs_nonneg _) (Finset.mem_univ t)
    linarith
  · intro t
    have := Finset.single_le_sum (f := fun t => |pol.z t|) (fun _ _ => abs_nonneg _) (Finset.mem_univ t)
    linarith
  · intro d hd
    refine ⟨fun k => ?_, fun t => ?_⟩
    · have h1 := Finset.single_le_sum (f := fun k => |pol.x k d|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
      have := hRx d hd
      rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))] at this
      linarith
    · have h1 := Finset.single_le_sum
        (f := fun t : Fin T => |pol.q t d| + |∑ τ ∈ Finset.univ.filter (· ≤ t), pol.q τ d| + |pol.y t d| + |pol.u t d|)
        (fun _ _ => by positivity) (Finset.mem_univ t)
      have := hRq d hd
      rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => by positivity))] at this
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        nlinarith [abs_nonneg (pol.q t d), abs_nonneg (∑ τ ∈ Finset.univ.filter (· ≤ t), pol.q τ d),
          abs_nonneg (pol.y t d), abs_nonneg (pol.u t d)]

theorem solution {T : ℕ} (D : RSFCData T) (dmin dmax : Fin T → ℝ)
    (hle : ∀ t, dmin t ≤ dmax t) :
    (∀ R : ℝ, value D (fun t => Set.Icc (dmin t) (dmax t)) ≤
        valueR D (fun t => Set.Icc (dmin t) (dmax t)) R) ∧
      value D (fun t => ({dmin t, dmax t} : Set ℝ)) ≤ value D (fun t => Set.Icc (dmin t) (dmax t)) ∧
      value D (fun t => ({dmin t, dmax t} : Set ℝ)) =
        ⨅ R : ℝ, valueR D (fun t => ({dmin t, dmax t} : Set ℝ)) R := by
  refine ⟨fun R => ?_, ?_, ?_⟩
  · unfold value valueR
    exact le_iInf₂ (fun pol hpol => iInf₂_le pol hpol.1)
  · refine ZZC_value_mono D _ _ (fun t => ?_)
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨le_rfl, hle t⟩
    · exact ⟨hle t, le_rfl⟩
  · apply le_antisymm
    · exact le_iInf (fun R => by
        unfold value valueR
        exact le_iInf₂ (fun pol hpol => iInf₂_le pol hpol.1))
    · unfold value
      refine le_iInf₂ (fun pol hpol => ?_)
      obtain ⟨R, hR⟩ := ZZC_exists_R D (fun t => ({dmin t, dmax t} : Set ℝ))
        (fun t => by simp) pol hpol
      refine (iInf_le _ R).trans ?_
      unfold valueR
      exact iInf₂_le pol hR
