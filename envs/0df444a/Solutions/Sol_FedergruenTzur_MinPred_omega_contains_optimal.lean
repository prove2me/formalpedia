-- Prove2me | solution 1 for FedergruenTzur.MinPred.omega_contains_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T08:11:46.445055+00:00
-- url     : https://prove2.me/submissions/36423465-e346-4d5e-83ed-02b2eea75ce6

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Omega


namespace FedergruenTzur.MinPred.OmegaOpt

open Filter Topology

theorem lines_key (s : Finset ℕ) (α β : ℕ → ℝ) (x0 : ℝ) (l : ℕ)
    (hmin : ∀ i ∈ s, α l ≤ α i) (hslope : ∀ i ∈ s, α i = α l → β l ≤ β i)
    (hidx : ∀ i ∈ s, α i = α l → β i = β l → l ≤ i) :
    ∃ b, x0 < b ∧ ∀ x ∈ Set.Ioo x0 b, ∀ i ∈ s,
      (α l + β l * (x - x0) ≤ α i + β i * (x - x0)) ∧
      (i < l → α l + β l * (x - x0) < α i + β i * (x - x0)) := by
  have h : ∀ i ∈ s, ∀ᶠ x in 𝓝[>] x0,
      (α l + β l * (x - x0) ≤ α i + β i * (x - x0)) ∧
      (i < l → α l + β l * (x - x0) < α i + β i * (x - x0)) := by
    intro i hi
    rcases (hmin i hi).lt_or_eq with hlt | heq
    · have hc : ∀ᶠ x in 𝓝 x0, α l + β l * (x - x0) < α i + β i * (x - x0) := by
        apply ContinuousAt.eventually_lt (by fun_prop) (by fun_prop)
        simpa using hlt
      exact (hc.filter_mono nhdsWithin_le_nhds).mono fun x hx => ⟨hx.le, fun _ => hx⟩
    · rcases (hslope i hi heq.symm).lt_or_eq with hb | hb
      · filter_upwards [self_mem_nhdsWithin] with x (hx : x0 < x)
        have : β l * (x - x0) < β i * (x - x0) :=
          mul_lt_mul_of_pos_right hb (by linarith)
        constructor
        · rw [heq]; linarith
        · intro _; rw [heq]; linarith
      · refine Eventually.of_forall fun x => ⟨by rw [heq, hb], fun hil => ?_⟩
        exact absurd (hidx i hi heq.symm hb.symm) (by omega)
  have h2 := (eventually_all_finset s).2 h
  obtain ⟨b, hb, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h2
  exact ⟨b, hb, fun x hx => hsub hx⟩

end FedergruenTzur.MinPred.OmegaOpt

open FedergruenTzur.MinPred.OmegaOpt in
open FedergruenTzur.MinPred FedergruenTzur.MinPred.LotSizing in
theorem solution (P : LotSizing) (j : ℕ) (hj : 1 ≤ j) :
    ∃ l ∈ P.Omega j, P.Flast l j = P.Fopt j := by
  classical
  set α : ℕ → ℝ := fun i => P.Flast i j with hα
  set β : ℕ → ℝ := fun i => P.c i + (P.H (j - 1) - P.H (i - 1)) with hβ
  have hpot : ∀ i x, P.potCost j i x = α i + β i * (x - P.D j) := by
    intro i x; simp only [hα, hβ, potCost, Flast]; ring
  obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
  have hne : (Finset.Icc 1 (t + 1)).Nonempty := ⟨1, by simp⟩
  have hF : P.Fopt (t + 1) = (Finset.Icc 1 (t + 1)).inf' hne α := P.Fopt_succ t
  set O := (Finset.Icc 1 (t + 1)).filter (fun i => α i = P.Fopt (t + 1)) with hO
  have hOne : O.Nonempty := by
    obtain ⟨i, hi, hie⟩ := Finset.exists_mem_eq_inf' hne α
    exact ⟨i, Finset.mem_filter.2 ⟨hi, by rw [hF, hie]⟩⟩
  obtain ⟨i0, hi0, hi0min⟩ := Finset.exists_min_image O β hOne
  set O2 := O.filter (fun i => β i = β i0) with hO2
  have hO2ne : O2.Nonempty := ⟨i0, Finset.mem_filter.2 ⟨hi0, rfl⟩⟩
  set l := O2.min' hO2ne with hl
  have hlO2 : l ∈ O2 := Finset.min'_mem _ _
  have hlO : l ∈ O := (Finset.mem_filter.1 hlO2).1
  have hlI : l ∈ Finset.Icc 1 (t + 1) := (Finset.mem_filter.1 hlO).1
  have hlα : α l = P.Fopt (t + 1) := (Finset.mem_filter.1 hlO).2
  have hlβ : β l = β i0 := (Finset.mem_filter.1 hlO2).2
  have hle : ∀ i ∈ Finset.Icc 1 (t + 1), P.Fopt (t + 1) ≤ α i := by
    intro i hi; rw [hF]; exact Finset.inf'_le _ hi
  obtain ⟨b, hb, hall⟩ := lines_key (Finset.Icc 1 (t + 1)) α β (P.D (t + 1)) l
    (fun i hi => hlα ▸ hle i hi)
    (fun i hi he => by
      rw [hlβ]; exact hi0min i (Finset.mem_filter.2 ⟨hi, by rw [he, hlα]⟩))
    (fun i hi he hbe => Finset.min'_le _ _
      (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hi, by rw [he, hlα]⟩, by rw [hbe, hlβ]⟩))
  refine ⟨l, ?_, hlα⟩
  unfold Omega
  refine Finset.mem_filter.2 ⟨hlI, P.D (t + 1), b, le_rfl, hb, fun x hx => ?_⟩
  refine ⟨fun i hi => ?_, fun i hi hil => ?_⟩
  · rw [hpot, hpot]; exact (hall x hx i hi).1
  · rw [hpot, hpot]; exact (hall x hx i hi).2 hil
