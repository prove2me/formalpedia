-- Prove2me | solution 1 for Dubey1986.Inefficiency.nash_interior_mem_Nstar
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:56:09.480191+00:00
-- url     : https://prove2.me/submissions/ec3dc61f-dca1-4a42-b9e0-8681c9955f78

import Mathlib
import Definitions.Def_Dubey1986_Inefficiency_Setting
import Definitions.Def_Dubey1986_Inefficiency_Derivative

set_option autoImplicit false
open Dubey1986.Inefficiency

theorem solution {n : ℕ} (hn : 2 ≤ n) (k : Fin n → ℕ) (hk : ∀ i, 1 ≤ k i)
    (V : ∀ i, Set (Fin (k i) → ℝ)) (hVo : ∀ i, IsOpen (V i))
    (hSV : ∀ i, simplex (k i) ⊆ V i) (u : Fin n → Strat k → ℝ) (hu : IsGame V u)
    (s : Strat k) (hint : ∀ i, s i ∈ interior (simplex (k i))) (hs : s ∈ NashSet u) :
    Dmap u s ∈ Nstar k := by
  intro i v
  show fderiv ℝ (u i) s (Pi.single i v) = 0
  obtain ⟨w, hw⟩ : ∃ w : Strat k, w = Pi.single i v := ⟨_, rfl⟩
  rw [← hw]
  have hwi : w i = v := by rw [hw]; simp
  have hwj : ∀ j, j ≠ i → w j = 0 := by intro j hj; rw [hw]; simp [hj]
  have hopen : IsOpen (Vset V) := isOpen_set_pi Set.finite_univ (fun i _ => hVo i)
  have hsV : s ∈ Vset V := fun j _ => hSV j (interior_subset (hint j))
  have hdiff : DifferentiableAt ℝ (u i) s :=
    ((hu i).1.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hsV)
  let φ : ℝ → ℝ := fun τ => u i (s + τ • w)
  have hφ : HasDerivAt φ (fderiv ℝ (u i) s w) 0 := by
    have h1 : HasDerivAt (fun τ : ℝ => s + τ • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add s
    have h2 : HasFDerivAt (u i) (fderiv ℝ (u i) s) (s + (0 : ℝ) • w) := by
      simpa using hdiff.hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have hmax : IsLocalMax φ 0 := by
    have hnb : ∀ᶠ τ : ℝ in nhds 0, s i + τ • v ∈ interior (simplex (k i)) := by
      have hc : Continuous (fun τ : ℝ => s i + τ • v) := by fun_prop
      have h0 : s i + (0 : ℝ) • v ∈ interior (simplex (k i)) := by simpa using hint i
      exact hc.continuousAt.eventually (isOpen_interior.mem_nhds h0)
    filter_upwards [hnb] with τ hτ
    have hnash := hs.2 i
    unfold IsTEfficient at hnash
    by_contra hlt
    push Not at hlt
    have hup : update s {i} (s + τ • w) = s + τ • w := by
      funext l
      by_cases hl : l = i
      · subst hl; simp [update]
      · simp [update, hl, hwj l hl]
    have hlt' : u i s < u i (s + τ • w) := by simpa [φ] using hlt
    apply hnash
    refine ⟨s + τ • w, ?_, ?_, ⟨i, Finset.mem_singleton_self i, ?_⟩⟩
    · intro j hj
      rw [Finset.mem_singleton] at hj
      subst hj
      have : (s + τ • w) j = s j + τ • v := by simp [hwi]
      rw [this]
      exact interior_subset hτ
    · intro j hj
      rw [Finset.mem_singleton] at hj
      subst hj
      rw [hup]
      exact le_of_lt hlt'
    · rw [hup]; exact hlt'
  exact hmax.hasDerivAt_eq_zero hφ
