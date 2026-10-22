-- Prove2me | solution 1 for BirkhoffGlobalSection.regularized_ray_first_zero_exists
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T10:30:14.816469+00:00
-- url     : https://prove2.me/submissions/48354bf2-d17f-442d-a566-e24b0ff4afb5

import Mathlib
import Theorems.Thm_BirkhoffGlobalSection_regularized_ray_energy_continuous_on_segment

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (x : Phase) (R : ℝ) (hR : 0 < R)
    (hpositive : 0 < leviCivitaHamiltonian μ c
      (fun i : Fin 4 => R * x i))
    (hfree : ∀ r : ℝ, 0 ≤ r → r ≤ R →
      0 < secondCollisionDistanceSq (fun i : Fin 4 => r * x i)) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      leviCivitaHamiltonian μ c (fun i : Fin 4 => r * x i) = 0 ∧
      ∀ t : ℝ, 0 ≤ t → t < r →
        leviCivitaHamiltonian μ c (fun i : Fin 4 => t * x i) < 0 := by
  let g : ℝ → ℝ := fun t =>
    leviCivitaHamiltonian μ c (fun i : Fin 4 => t * x i)
  have hgcont : ContinuousOn g (Set.Icc 0 R) :=
    regularized_ray_energy_continuous_on_segment μ c x R hfree
  have hg0 : g 0 = -(1 - μ) / 2 := by
    dsimp [g, leviCivitaHamiltonian, wNormSq, zNormSq,
      secondCollisionDistanceSq]
    norm_num <;> ring
  have hg0neg : g 0 < 0 := by rw [hg0]; linarith
  let S : Set ℝ := Set.Icc 0 R ∩ g ⁻¹' Set.Ici 0
  have hSclosed : IsClosed S := by
    exact hgcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSnonempty : S.Nonempty := by
    refine ⟨R, ⟨⟨le_of_lt hR, le_refl R⟩, ?_⟩⟩
    exact le_of_lt hpositive
  have hSbnd : BddBelow S := ⟨0, by
    intro t ht
    exact ht.1.1⟩
  let r : ℝ := sInf S
  have hrS : r ∈ S := hSclosed.csInf_mem hSnonempty hSbnd
  have hr0 : 0 ≤ r := hrS.1.1
  have hrR : r ≤ R := hrS.1.2
  have hrpos : 0 < r := by
    by_contra h
    have heq : r = 0 := le_antisymm (le_of_not_gt h) hr0
    rw [heq] at hrS
    have hval : 0 ≤ g 0 := hrS.2
    linarith
  have hgrzero : g r = 0 := by
    by_contra hne
    have hgrnonneg : 0 ≤ g r := hrS.2
    have hgrpos : 0 < g r := by
      rcases lt_or_eq_of_le hgrnonneg with hp | he
      · exact hp
      · exact False.elim (hne he.symm)
    have hcont' : ContinuousOn g (Set.Icc 0 r) :=
      hgcont.mono (by
        intro t ht
        exact ⟨ht.1, ht.2.trans hrR⟩)
    have hmid : g r / 2 ∈ Set.Icc (g 0) (g r) := by
      constructor <;> linarith
    obtain ⟨t, ht, htg⟩ :=
      (intermediate_value_Icc hr0 hcont' hmid)
    have htlt : t < r := by
      by_contra hn
      have heq : t = r := le_antisymm ht.2 (le_of_not_gt hn)
      rw [heq] at htg
      linarith
    have htS : t ∈ S := by
      refine ⟨⟨ht.1, htlt.le.trans hrR⟩, ?_⟩
      change 0 ≤ g t
      rw [htg]
      linarith
    have hrle : r ≤ t := csInf_le hSbnd htS
    linarith
  have hrRlt : r < R := by
    rcases lt_or_eq_of_le hrR with h | h
    · exact h
    · rw [h] at hgrzero
      exact False.elim (by linarith [hpositive, hgrzero])
  refine ⟨r, hrpos, hrRlt, hgrzero, ?_⟩
  intro t ht0 htr
  by_contra hn
  have htS : t ∈ S := by
    refine ⟨⟨ht0, htr.le.trans hrR⟩, ?_⟩
    change 0 ≤ g t
    exact le_of_not_gt hn
  have hrle : r ≤ t := csInf_le hSbnd htS
  linarith
