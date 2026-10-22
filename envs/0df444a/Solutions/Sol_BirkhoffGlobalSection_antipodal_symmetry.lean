-- Prove2me | solution 1 for BirkhoffGlobalSection.antipodal_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T07:15:12.662572+00:00
-- url     : https://prove2.me/submissions/f8cfe71e-6ec8-4d48-9e72-fb87326852e4

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem _root_.solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c) :
    (∀ s : Phase,
      leviCivitaHamiltonian μ c (-s) = leviCivitaHamiltonian μ c s) ∧
    IsAntipodallyInvariantComponent μ c ∧
    IsAntipodallyFreeComponent μ c := by
  have heven : ∀ s : Phase,
      leviCivitaHamiltonian μ c (-s) = leviCivitaHamiltonian μ c s := by
    intro s
    simp only [leviCivitaHamiltonian, wNormSq, zNormSq, secondCollisionDistanceSq,
      Pi.neg_apply]
    ring_nf
  have hsc : ∀ s : Phase, secondCollisionDistanceSq (-s) = secondCollisionDistanceSq s := by
    intro s
    simp only [secondCollisionDistanceSq, Pi.neg_apply]
    ring_nf
  have hLneg : ∀ s : Phase, s ∈ regularEnergyLocus μ c → -s ∈ regularEnergyLocus μ c := by
    intro s hs
    obtain ⟨h1, h2⟩ := hs
    exact ⟨by rw [heven]; exact h1, by rw [hsc]; exact h2⟩
  -- the circle over the collision
  set r : ℝ := Real.sqrt (1 - μ) with hr
  have hr2 : r ^ 2 = 1 - μ := by
    rw [hr, Real.sq_sqrt]; linarith
  let γ : ℝ → Phase := fun θ => ![0, 0, r * Real.cos θ, r * Real.sin θ]
  have hγc : Continuous γ := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp [γ] <;> fun_prop
  have hγL : ∀ θ, γ θ ∈ regularEnergyLocus μ c := by
    intro θ
    refine ⟨?_, ?_⟩
    · simp only [leviCivitaHamiltonian, wNormSq, zNormSq, secondCollisionDistanceSq, γ]
      simp
      have : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = 1 - μ := by
        rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, hr2, mul_one]
      rw [this]; ring
    · simp [secondCollisionDistanceSq, γ]
  have hp : γ 0 = leftCollisionPoint μ := by
    funext i; fin_cases i <;> simp [γ, leftCollisionPoint, hr]
  have hmp : γ Real.pi = -leftCollisionPoint μ := by
    funext i; fin_cases i <;> simp [γ, leftCollisionPoint, hr]
  have hrange : Set.range γ ⊆ leftEnergyComponent μ c := by
    apply (isPreconnected_range hγc).subset_connectedComponentIn
    · exact ⟨0, hp⟩
    · rintro _ ⟨θ, rfl⟩; exact hγL θ
  have hnegp : -leftCollisionPoint μ ∈ leftEnergyComponent μ c :=
    hrange ⟨Real.pi, hmp⟩
  have hsub : ∀ s, s ∈ leftEnergyComponent μ c → -s ∈ leftEnergyComponent μ c := by
    intro s hs
    have hpre : IsPreconnected ((fun x : Phase => -x) '' leftEnergyComponent μ c) :=
      (isPreconnected_connectedComponentIn).image _ (continuous_neg.continuousOn)
    have hsub' : (fun x : Phase => -x) '' leftEnergyComponent μ c ⊆
        connectedComponentIn (regularEnergyLocus μ c) (-leftCollisionPoint μ) := by
      apply hpre.subset_connectedComponentIn
      · exact ⟨leftCollisionPoint μ, mem_connectedComponentIn (by
          rw [← hp]; exact hγL 0), rfl⟩
      · rintro _ ⟨x, hx, rfl⟩
        exact hLneg x (connectedComponentIn_subset _ _ hx)
    have heq : connectedComponentIn (regularEnergyLocus μ c) (-leftCollisionPoint μ) =
        leftEnergyComponent μ c := (connectedComponentIn_eq hnegp).symm
    rw [heq] at hsub'
    exact hsub' ⟨s, hs, rfl⟩
  refine ⟨heven, ?_, ?_⟩
  · intro s
    constructor
    · exact hsub s
    · intro h
      have := hsub (-s) h
      simpa using this
  · intro s hs
    have hL : (s : Phase) ∈ regularEnergyLocus μ c :=
      connectedComponentIn_subset _ _ s.2
    have h0 : (s : Phase) = 0 := by
      funext i
      have := congrFun hs i
      simp only [Pi.neg_apply, Pi.zero_apply] at this ⊢
      linarith
    have hH := hL.1
    rw [h0] at hH
    simp [leviCivitaHamiltonian, wNormSq, zNormSq, secondCollisionDistanceSq] at hH
    linarith
