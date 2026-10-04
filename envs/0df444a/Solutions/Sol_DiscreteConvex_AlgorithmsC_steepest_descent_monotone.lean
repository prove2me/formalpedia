-- Prove2me | solution 1 for DiscreteConvex.AlgorithmsC.steepest_descent_monotone
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:09:45.686213+00:00
-- url     : https://prove2.me/submissions/574a9485-4a29-4ff5-9df9-643a2b527046

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_ArgMin
import Definitions.Def_DiscreteConvex_AlgorithmsC_SBF
import Definitions.Def_DiscreteConvex_AlgorithmsC_IsMinimalMinimizerWT
import Definitions.Def_DiscreteConvex_AlgorithmsC_RhoP

set_option autoImplicit false

open DiscreteConvex.AlgorithmsC

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (g : (V → ℤ) → WithTop ℝ) (hg : SBF g) (p pstar : V → ℤ)
    (hpstar : pstar ∈ ArgMin g) (hple : ∀ v, p v ≤ pstar v) (X : Finset V)
    (hX : IsMinimalMinimizerWT (RhoP g p) X) :
    ∀ v, p v + (if v ∈ X then (1:ℤ) else 0) ≤ pstar v := by
  classical
  -- `X'` drops the elements of `X` where `p` already reaches `pstar`.
  set X' : Finset V := X.filter (fun v => p v < pstar v) with hX'
  suffices hsub : X ⊆ X' by
    intro v
    by_cases hv : v ∈ X
    · have := hsub hv
      rw [hX', Finset.mem_filter] at this
      simp only [hv, if_true]
      omega
    · simp only [hv, if_false]
      simpa using hple v
  apply hX.2
  intro Y
  by_cases hgp : g p = ⊤
  · -- `g p = ⊤`: every value of `ρ_p` is `⊤`.
    simp [RhoP, hgp]
  · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hgp
    have hle : RhoP g p X' ≤ RhoP g p X := by
      have hmin : (fun v => p v + (if v ∈ X then (1:ℤ) else 0)) ⊓ pstar =
          (fun v => p v + (if v ∈ X' then (1:ℤ) else 0)) := by
        funext v
        simp only [Pi.inf_apply, hX', Finset.mem_filter]
        by_cases hv : v ∈ X <;> by_cases hlt : p v < pstar v <;> simp [hv, hlt] <;>
          have := hple v <;> omega
      have hsbf := hg (fun v => p v + (if v ∈ X then (1:ℤ) else 0)) pstar
      rw [hmin] at hsbf
      have hstar : g pstar ≤ g ((fun v => p v + (if v ∈ X then (1:ℤ) else 0)) ⊔ pstar) :=
        hpstar _
      have hfin : g pstar ≠ ⊤ := by
        intro h
        have := hpstar p
        rw [h] at this
        exact hgp (top_le_iff.mp this)
      have key : g (fun v => p v + (if v ∈ X' then (1:ℤ) else 0)) ≤
          g (fun v => p v + (if v ∈ X then (1:ℤ) else 0)) := by
        have h2 : g (fun v => p v + (if v ∈ X' then (1:ℤ) else 0)) + g pstar ≤
            g (fun v => p v + (if v ∈ X then (1:ℤ) else 0)) + g pstar := by
          calc g (fun v => p v + (if v ∈ X' then (1:ℤ) else 0)) + g pstar
              ≤ g (fun v => p v + (if v ∈ X' then (1:ℤ) else 0)) +
                  g ((fun v => p v + (if v ∈ X then (1:ℤ) else 0)) ⊔ pstar) := by gcongr
            _ = g ((fun v => p v + (if v ∈ X then (1:ℤ) else 0)) ⊔ pstar) +
                  g (fun v => p v + (if v ∈ X' then (1:ℤ) else 0)) := add_comm _ _
            _ ≤ _ := hsbf
        exact (WithTop.add_le_add_iff_right hfin).mp h2
      unfold RhoP
      rw [← ha]
      by_cases hA : g (fun v => p v + (if v ∈ X then (1:ℤ) else 0)) = ⊤
      · rw [hA]; simp
      · obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hA
        rw [← hb] at key ⊢
        have hB : g (fun v => p v + (if v ∈ X' then (1:ℤ) else 0)) ≠ ⊤ :=
          ne_top_of_le_ne_top WithTop.coe_ne_top key
        obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hB
        rw [← hc] at key ⊢
        have : c ≤ b := WithTop.coe_le_coe.mp key
        have e1 : (c : WithTop ℝ) - (a : WithTop ℝ) = ((c - a : ℝ) : WithTop ℝ) := by norm_cast
        have e2 : (b : WithTop ℝ) - (a : WithTop ℝ) = ((b - a : ℝ) : WithTop ℝ) := by norm_cast
        rw [e1, e2]
        exact WithTop.coe_le_coe.mpr (by linarith)
    exact hle.trans (hX.1 Y)

#print axioms solution
