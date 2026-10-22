-- Prove2me | solution 1 for BirkhoffGlobalSection.birkhoff_retrograde_orbit_exists
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T23:12:06.490205+00:00
-- url     : https://prove2.me/submissions/3b98b426-96fc-4212-bf8e-475b3980a271

import Definitions.Def_BirkhoffGlobalSection
import Theorems.Thm_BirkhoffGlobalSection_antipodal_symmetry
import Theorems.Thm_BirkhoffGlobalSection_leviCivita_flow_antipodally_equivariant
import Theorems.Thm_BirkhoffGlobalSection_leviCivita_flow_q2_reversible
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_shooting_symmetric_half_orbit
import Theorems.Thm_BirkhoffGlobalSection_symmetric_half_loop_polar_winding
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Algebra.Field.Periodic
import Mathlib.Tactic

open BirkhoffGlobalSection Set

/-- The physical position relative to the first primary, in coordinates. -/
lemma relPos_zero (μ : ℝ) (s : Phase) :
    relativePosition μ s 0 = 2 * (s 0 ^ 2 - s 1 ^ 2) := by
  simp [relativePosition, leviCivitaPosition]

lemma relPos_one (μ : ℝ) (s : Phase) :
    relativePosition μ s 1 = 4 * s 0 * s 1 := by
  simp [relativePosition, leviCivitaPosition]

lemma relPos_neg (μ : ℝ) (s : Phase) : relativePosition μ (-s) = relativePosition μ s := by
  funext i; fin_cases i <;> simp [relativePosition, leviCivitaPosition]

lemma relPos_refl (μ : ℝ) (s : Phase) :
    relativePosition μ (jacobiQ₂Reflection s) =
      ![relativePosition μ s 0, -relativePosition μ s 1] := by
  funext i; fin_cases i <;> simp [relativePosition, leviCivitaPosition, jacobiQ₂Reflection]

lemma refl_neg (s : Phase) : jacobiQ₂Reflection (-s) = -jacobiQ₂Reflection s := by
  funext i; fin_cases i <;> simp [jacobiQ₂Reflection]

lemma refl_refl (s : Phase) : jacobiQ₂Reflection (jacobiQ₂Reflection s) = s := by
  funext i; fin_cases i <;> simp [jacobiQ₂Reflection]

lemma jacobi_negRefl (μ : ℝ) (s : Phase) :
    leviCivitaToJacobi μ (-jacobiQ₂Reflection s) =
      jacobiQ₂Reflection (leviCivitaToJacobi μ s) := by
  funext i
  fin_cases i <;>
    simp [leviCivitaToJacobi, leviCivitaPosition, leviCivitaMomentum, jacobiQ₂Reflection,
      zNormSq] <;> ring

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ δ : AntipodalPeriodicTrajectory φ,
      IsGeometricBirkhoffRetrogradeTrajectory φ δ := by
  obtain ⟨_, hinv, _⟩ := antipodal_symmetry μ c hμ0 hμ1 hc
  have hanti := leviCivita_flow_antipodally_equivariant μ c hμ0 hμ1 hc φ hφ
  have hrev := leviCivita_flow_q2_reversible μ c hμ0 hμ1 hc φ hφ
  obtain ⟨x0, τ, hτ, hx0, hx3, hx1, he1, he2, he0, hlow, hmono⟩ :=
    birkhoff_shooting_symmetric_half_orbit μ c hμ0 hμ1 hc φ hφ
  set γ : ℝ → Phase := fun t => ((φ t x0 : LeftEnergyState μ c) : Phase) with hγ
  set ρ := jacobiQ₂Reflection
  -- the two symmetric endpoints
  have hρx0 : ρ (x0 : Phase) = -(x0 : Phase) := by
    funext i; fin_cases i <;> simp [ρ, jacobiQ₂Reflection, hx0, hx3]
  have hρx1 : ρ (γ τ) = γ τ := by
    funext i; fin_cases i <;> simp [ρ, jacobiQ₂Reflection, hγ, he1, he2]
  -- symmetry about `t = 0`
  have hS1 : ∀ t, γ (-t) = -ρ (γ t) := by
    intro t
    set y0 : LeftEnergyState μ c := ⟨-(x0 : Phase), (hinv _).1 x0.2⟩
    have h1 := hrev t x0 y0 (by simp [y0, hρx0])
    have h2 := hanti (-t) x0 y0 rfl
    rw [h2] at h1
    simp only [hγ]
    rw [← h1]; simp
  -- symmetry about `t = τ`
  have hS2 : ∀ t, γ (τ - t) = ρ (γ (τ + t)) := by
    intro t
    set x1 : LeftEnergyState μ c := φ τ x0
    have h := hrev t x1 x1 (by simpa [x1, hγ] using hρx1.symm)
    have ea : φ (-t) x1 = φ (τ - t) x0 := by
      simp only [x1, ← Flow.map_add]; ring_nf
    have eb : φ t x1 = φ (τ + t) x0 := by
      simp only [x1, ← Flow.map_add]; ring_nf
    rw [ea, eb] at h
    exact h
  -- antipodal closing
  have hper : ∀ s, γ (s + 2 * τ) = -γ s := by
    intro s
    have h := hS2 (-(s + τ))
    have e1 : τ - -(s + τ) = s + 2 * τ := by ring
    have e2 : τ + -(s + τ) = -s := by ring
    rw [e1, e2, hS1] at h
    rw [h]
    simp only [ρ]
    rw [refl_neg, refl_refl]
  have hγ0 : γ 0 = (x0 : Phase) := by simp [hγ]
  -- the planar position curve
  set Γ : ℝ → Plane := fun t => relativePosition μ (γ t) with hΓ
  have hΓper : ∀ t, Γ (t + 2 * τ) = Γ t := by
    intro t; simp only [hΓ]; rw [hper, relPos_neg]
  have hΓrefl : ∀ t, Γ (-t) = ![Γ t 0, -Γ t 1] := by
    intro t; simp only [hΓ]; rw [hS1, relPos_neg, relPos_refl]
  have hΓstart1 : Γ 0 1 = 0 := by simp only [hΓ, hγ0, relPos_one, hx0]; ring
  have hΓstart0 : Γ 0 0 < 0 := by
    simp only [hΓ, hγ0, relPos_zero, hx0]
    have : 0 < (x0 : Phase) 1 ^ 2 := by positivity
    linarith
  have hΓend1 : Γ τ 1 = 0 := by
    simp only [hΓ, relPos_one]; simp only [hγ] at he1 ⊢; rw [he1]; ring
  have hΓend0 : 0 < Γ τ 0 := by
    simp only [hΓ, relPos_zero]; simp only [hγ] at he1 he0 ⊢
    rw [he1]
    have : 0 < ((φ τ x0 : LeftEnergyState μ c) : Phase) 0 ^ 2 := by positivity
    linarith
  have hΓlow : ∀ t ∈ Ioo 0 τ, Γ t 1 < 0 := hlow
  have hΓmono : StrictMonoOn (fun t => Γ t 0) (Icc 0 τ) := hmono
  -- second half of the period
  have hΓsecond : ∀ t, Γ t = ![Γ (2 * τ - t) 0, -Γ (2 * τ - t) 1] := by
    intro t
    have := hΓrefl (2 * τ - t)
    have e : -(2 * τ - t) = t - 2 * τ := by ring
    rw [e] at this
    have h2 := hΓper (t - 2 * τ)
    rw [show t - 2 * τ + 2 * τ = t by ring] at h2
    rw [h2]; exact this
  have hΓup : ∀ t ∈ Ioo τ (2 * τ), 0 < Γ t 1 := by
    intro t ht
    have e : Γ t 1 = -Γ (2 * τ - t) 1 := by
      have := congrFun (hΓsecond t) 1
      simpa using this
    rw [e]
    have := hΓlow (2 * τ - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    linarith
  -- the position never meets the primary on one period
  have hΓne : ∀ t ∈ Ico 0 (2 * τ), Γ t ≠ 0 := by
    intro t ht h
    have h0 : Γ t 0 = 0 := by rw [h]; rfl
    have h1 : Γ t 1 = 0 := by rw [h]; rfl
    rcases lt_trichotomy t τ with hlt | heq | hgt
    · rcases eq_or_lt_of_le ht.1 with h0t | h0t
      · rw [← h0t] at h0; linarith
      · linarith [hΓlow t ⟨h0t, hlt⟩]
    · rw [heq] at h0; linarith
    · linarith [hΓup t ⟨hgt, ht.2⟩]
  have hΓper' : Function.Periodic Γ (2 * τ) := hΓper
  have hΓne_all : ∀ t, Γ t ≠ 0 := by
    intro t
    obtain ⟨y, hy, hyt⟩ := hΓper'.exists_mem_Ico₀ (by linarith) t
    rw [hyt]; exact hΓne y hy
  -- the trajectory data
  let δ : AntipodalPeriodicTrajectory φ :=
    { point := x0
      period := 2 * τ
      period_pos := by linarith
      antipodal_closed := by
        have := hper 0
        rw [zero_add, hγ0] at this
        exact this
      prime := by
        intro t ht0 htP
        have hne : Γ t ≠ Γ 0 := by
          intro h
          rcases lt_trichotomy t τ with hlt | heq | hgt
          · have := hΓlow t ⟨ht0, hlt⟩; rw [h] at this; linarith
          · have := hΓend0; rw [← heq, h] at this; linarith
          · have := hΓup t ⟨hgt, htP⟩; rw [h] at this; linarith
        constructor
        · intro h; apply hne; simp only [hΓ, hγ]; rw [h]; simp
        · intro h; apply hne; simp only [hΓ, hγ]; rw [h, relPos_neg]; simp }
  refine ⟨δ, ?_, ?_, ?_, ?_⟩
  · -- collision-free
    intro t
    have h := hΓne_all t
    by_contra hz
    apply h
    have hz' : zNormSq (γ t) = 0 := le_antisymm (not_lt.1 hz) (by unfold zNormSq; positivity)
    unfold zNormSq at hz'
    have a0 : γ t 0 = 0 := by nlinarith [sq_nonneg (γ t 0), sq_nonneg (γ t 1)]
    have a1 : γ t 1 = 0 := by nlinarith [sq_nonneg (γ t 0), sq_nonneg (γ t 1)]
    funext i; fin_cases i
    · simp [hΓ, relPos_zero, a0, a1]
    · simp [hΓ, relPos_one, a0, a1]
  · -- `q₂`-symmetry
    intro t
    show leviCivitaToJacobi μ (γ (-t)) = jacobiQ₂Reflection (leviCivitaToJacobi μ (γ t))
    rw [hS1]; exact jacobi_negRefl μ (γ t)
  · -- simple loop on one period
    intro t1 ht1 t2 ht2 heq
    have heq' : Γ t1 = Γ t2 := heq
    have side : ∀ t ∈ Ico 0 (2 * τ), t ≤ τ → Γ t 1 ≤ 0 := by
      intro t ht htτ
      rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h, hΓstart1]
      · rcases eq_or_lt_of_le htτ with h' | h'
        · rw [h', hΓend1]
        · exact (hΓlow t ⟨h, h'⟩).le
    by_cases h1 : t1 ≤ τ <;> by_cases h2 : t2 ≤ τ
    · exact hΓmono.injOn ⟨ht1.1, h1⟩ ⟨ht2.1, h2⟩ (by show Γ t1 0 = Γ t2 0; rw [heq'])
    · exfalso
      have := hΓup t2 ⟨lt_of_not_ge h2, ht2.2⟩
      have := side t1 ht1 h1
      have e : Γ t1 1 = Γ t2 1 := by rw [heq']
      linarith
    · exfalso
      have := hΓup t1 ⟨lt_of_not_ge h1, ht1.2⟩
      have := side t2 ht2 h2
      have e : Γ t1 1 = Γ t2 1 := by rw [heq']
      linarith
    · have hr1 := hΓsecond t1
      have hr2 := hΓsecond t2
      have e0 : Γ (2 * τ - t1) 0 = Γ (2 * τ - t2) 0 := by
        have := congrFun heq' 0
        rw [hr1, hr2] at this; simpa using this
      have := hΓmono.injOn ⟨by linarith [ht1.2], by linarith [lt_of_not_ge h1]⟩
        ⟨by linarith [ht2.2], by linarith [lt_of_not_ge h2]⟩ e0
      linarith
  · -- winding number one
    have hcont : Continuous Γ := by
      have hφc : Continuous (fun t : ℝ => (φ t x0 : LeftEnergyState μ c)) :=
        φ.continuous continuous_id continuous_const
      have hrp : Continuous (fun s : Phase => relativePosition μ s) := by
        apply continuous_pi; intro i; fin_cases i
        · simp only [relativePosition, leviCivitaPosition]; fun_prop
        · simp only [relativePosition, leviCivitaPosition]; fun_prop
      exact hrp.comp (continuous_subtype_val.comp hφc)
    exact symmetric_half_loop_polar_winding Γ τ hτ hcont hΓper hΓrefl hΓlow
      ⟨hΓstart1, hΓstart0⟩ ⟨hΓend1, hΓend0⟩
