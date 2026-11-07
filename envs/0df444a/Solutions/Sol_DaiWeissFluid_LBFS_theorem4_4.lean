-- Prove2me | solution 1 for DaiWeissFluid.LBFS.theorem4_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:31:32.115959+00:00
-- url     : https://prove2.me/submissions/807ad2a9-6888-4d96-b651-75eab2a791f6

import Mathlib
import Definitions.Def_DaiWeissFluid_LBFS_FluidModel
import Theorems.Thm_DaiWeissFluid_LBFS_emptying_time

open DaiWeissFluid.LBFS in
theorem solution {I K : ℕ} (L : DaiWeissFluid.LBFS.ReentrantLine I K)
    (hm : ∀ k, 0 < L.m k) (hρ : ∀ i, L.ρ i < 1) :
    DaiWeissFluid.ThreeBuffer.FluidStable (L.IsPrioritySolution Fin.revPerm) := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    refine ⟨1, one_pos, fun Q T _ hQ0 => ?_⟩
    simp at hQ0
  · refine ⟨1 / (L.lamHat - 1), ?_, fun Q T hsol hQ0 t ht k => ?_⟩
    · -- positivity of the emptying time, from `1 < λ̂`
      have k0 : Fin K := ⟨0, hK⟩
      have : Nonempty (Fin I) := ⟨L.σ k0⟩
      obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := L.ρ)
      have hk0 : k0 ∈ L.C (L.σ k0) := by simp [ReentrantLine.C]
      have hρpos : 0 < L.ρ (L.σ k0) :=
        lt_of_lt_of_le (hm k0) (Finset.single_le_sum (f := L.m) (fun k _ => (hm k).le) hk0)
      have hle : L.ρ (L.σ k0) ≤ ⨆ i : Fin I, L.ρ i := le_ciSup (Finite.bddAbove_range _) _
      have hMpos : 0 < ⨆ i : Fin I, L.ρ i := lt_of_lt_of_le hρpos hle
      have hM1 : (⨆ i : Fin I, L.ρ i) < 1 := by rw [← hi₀]; exact hρ i₀
      have hlam : 1 < L.lamHat := by
        show 1 < 1 / ⨆ i : Fin I, L.ρ i
        rw [lt_div_iff₀ hMpos]; linarith
      exact div_pos one_pos (by linarith)
    · exact emptying_time L hm hρ hK Q T hsol t (by rw [hQ0]; exact ht) k
