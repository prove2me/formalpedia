-- Prove2me | solution 1 for FirstLawThermo.exists_isInternalEnergy
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T13:15:22.852615+00:00
-- url     : https://prove2.me/submissions/4f3a8ac0-0981-489f-a51e-e23d7851d1c7

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem solution {σ : Type*} (procs : Set (Process σ)) (O : σ)
    (hcomp : ClosedUnderComp procs) (hnull : ContainsNull procs)
    (hpath : AdiabaticWorkPathIndependent procs) (hlink : AdiabaticallyLinkedTo procs O) :
    ∃ U : σ → ℝ, IsInternalEnergy procs U ∧ U O = 0 := by
  classical
  -- the chosen adiabatic link of each state to `O`
  let L : σ → Process σ := fun A => (hlink A).choose
  have hL : ∀ A, L A ∈ procs ∧ (L A).adiabatic ∧
      (((L A).start = O ∧ (L A).finish = A) ∨ ((L A).start = A ∧ (L A).finish = O)) :=
    fun A => (hlink A).choose_spec
  let U : σ → ℝ := fun A =>
    if (L A).start = O ∧ (L A).finish = A then -(L A).work else (L A).work
  -- an adiabatic cycle in `procs` does no work (compare with the null process)
  have hcyc : ∀ p ∈ procs, p.adiabatic → p.start = p.finish → p.work = 0 := by
    intro p hp had hsf
    have := hpath p hp (Process.null p.start) (hnull _) had trivial rfl hsf.symm
    simpa [Process.null] using this
  -- composition of two adiabatic processes in `procs`
  have hcompad : ∀ p ∈ procs, ∀ q ∈ procs, p.adiabatic → q.adiabatic → p.finish = q.start →
      p.comp q ∈ procs ∧ (p.comp q).adiabatic :=
    fun p hp q hq hpa hqa h => ⟨hcomp p hp q hq h, hpa, hqa⟩
  -- `U A = -W(p)` for any adiabatic `p : O → A`
  have hfrom : ∀ A, ∀ p ∈ procs, p.adiabatic → p.start = O → p.finish = A → U A = -p.work := by
    intro A p hp had hs hf
    obtain ⟨hLm, hLa, hLd⟩ := hL A
    by_cases h : (L A).start = O ∧ (L A).finish = A
    · have hU : U A = -(L A).work := if_pos h
      rw [hU, hpath _ hLm p hp hLa had (h.1.trans hs.symm) (h.2.trans hf.symm)]
    · have hU : U A = (L A).work := if_neg h
      have hd : (L A).start = A ∧ (L A).finish = O := hLd.resolve_left h
      obtain ⟨hcm, hca⟩ := hcompad _ hLm p hp hLa had (hd.2.trans hs.symm)
      have := hcyc _ hcm hca (by simp [Process.comp, hd.1, hf])
      simp only [Process.comp] at this
      rw [hU]; linarith
  -- `U A = W(q)` for any adiabatic `q : A → O`
  have hto : ∀ A, ∀ q ∈ procs, q.adiabatic → q.start = A → q.finish = O → U A = q.work := by
    intro A q hq had hs hf
    obtain ⟨hLm, hLa, hLd⟩ := hL A
    by_cases h : (L A).start = O ∧ (L A).finish = A
    · have hU : U A = -(L A).work := if_pos h
      obtain ⟨hcm, hca⟩ := hcompad _ hLm q hq hLa had (h.2.trans hs.symm)
      have := hcyc _ hcm hca (by simp [Process.comp, h.1, hf])
      simp only [Process.comp] at this
      rw [hU]; linarith
    · have hU : U A = (L A).work := if_neg h
      have hd : (L A).start = A ∧ (L A).finish = O := hLd.resolve_left h
      rw [hU, hpath _ hLm q hq hLa had (hd.1.trans hs.symm) (hd.2.trans hf.symm)]
  refine ⟨U, ?_, ?_⟩
  · intro r hr hra
    obtain ⟨hAm, hAa, hAd⟩ := hL r.start
    rcases hAd with ⟨hs, hf⟩ | ⟨hs, hf⟩
    · -- `O → A`, then `r : A → B` gives `O → B`
      obtain ⟨hcm, hca⟩ := hcompad _ hAm r hr hAa hra hf
      have h1 := hfrom r.start _ hAm hAa hs hf
      have h2 := hfrom r.finish _ hcm hca hs rfl
      simp only [Process.comp] at h2
      linarith
    · obtain ⟨hBm, hBa, hBd⟩ := hL r.finish
      have h1 := hto r.start _ hAm hAa hs hf
      rcases hBd with ⟨hs', hf'⟩ | ⟨hs', hf'⟩
      · -- `A → O → B` is compared with `r` by path independence
        obtain ⟨hcm, hca⟩ := hcompad _ hAm _ hBm hAa hBa (hf.trans hs'.symm)
        have h2 := hfrom r.finish _ hBm hBa hs' hf'
        have h3 := hpath r hr _ hcm hra hca hs.symm hf'.symm
        simp only [Process.comp] at h3
        linarith
      · -- `r : A → B`, then `B → O` gives `A → O`
        obtain ⟨hcm, hca⟩ := hcompad r hr _ hBm hra hBa hs'.symm
        have h2 := hto r.finish _ hBm hBa hs' hf'
        have h3 := hto r.start _ hcm hca rfl hf'
        simp only [Process.comp] at h3
        linarith
  · have := hto O (Process.null O) (hnull O) trivial rfl rfl
    simpa [Process.null] using this
