-- Prove2me | solution 1 for BirkhoffGlobalSection.left_component_closure_energy_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T09:18:24.986982+00:00
-- url     : https://prove2.me/submissions/af7dff22-350b-43fd-9f84-41bab27d3b9d

import Mathlib
import Theorems.Thm_BirkhoffGlobalSection_left_component_second_collision_separated

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ closure (leftEnergyComponent μ c),
      leviCivitaHamiltonian μ c s = 0 := by
  obtain ⟨δ, hδ, hsep⟩ :=
    left_component_second_collision_separated μ c hμ0 hμ1 hc
  have hdcont : Continuous (fun t : Phase =>
      Real.sqrt (secondCollisionDistanceSq t)) := by
    dsimp [secondCollisionDistanceSq]
    fun_prop
  have hclosed : IsClosed {t : Phase |
      δ ≤ Real.sqrt (secondCollisionDistanceSq t)} :=
    isClosed_Ici.preimage hdcont
  have hsepclosure : closure (leftEnergyComponent μ c) ⊆
      {t : Phase | δ ≤ Real.sqrt (secondCollisionDistanceSq t)} :=
    hclosed.closure_subset_iff.mpr (by
      intro t ht
      exact hsep t ht)
  let P : Phase → ℝ := fun t =>
    wNormSq t / 2 + c * zNormSq t - (1 - μ) / 2 +
      2 * zNormSq t * (t 0 * t 3 - t 1 * t 2) -
      μ * (t 0 * t 3 + t 1 * t 2)
  have hPcont : Continuous P := by
    dsimp [P, wNormSq, zNormSq]
    fun_prop
  have hNcont : Continuous (fun t : Phase => μ * zNormSq t) := by
    dsimp [zNormSq]
    fun_prop
  have hImage : (leviCivitaHamiltonian μ c) '' leftEnergyComponent μ c ⊆
      ({0} : Set ℝ) := by
    rintro y ⟨t, ht, rfl⟩
    have hreg : t ∈ regularEnergyLocus μ c :=
      connectedComponentIn_subset (regularEnergyLocus μ c)
        (leftCollisionPoint μ) ht
    simpa only [Set.mem_singleton_iff] using hreg.1
  intro s hs
  have hsD : δ ≤ Real.sqrt (secondCollisionDistanceSq s) := hsepclosure hs
  have hdenne : Real.sqrt (secondCollisionDistanceSq s) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hδ hsD)
  have hHcont : ContinuousAt (leviCivitaHamiltonian μ c) s := by
    change ContinuousAt (fun t => P t -
      μ * zNormSq t / Real.sqrt (secondCollisionDistanceSq t)) s
    exact hPcont.continuousAt.sub
      (hNcont.continuousAt.div hdcont.continuousAt hdenne)
  have hval := mem_closure_image hHcont hs
  have hzero : leviCivitaHamiltonian μ c s ∈ ({0} : Set ℝ) :=
    isClosed_singleton.closure_subset (closure_mono hImage hval)
  simpa only [Set.mem_singleton_iff] using hzero
