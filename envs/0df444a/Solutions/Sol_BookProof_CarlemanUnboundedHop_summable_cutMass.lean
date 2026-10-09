-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.summable_cutMass
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:00:31.045979+00:00
-- url     : https://prove2.me/submissions/14fd85b2-23d7-4df3-b3eb-cfe7abef4843

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.summable_cutMass
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop




open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hu : Summable fun n => ‖u n‖ ^ 2) (hΘ0 : ∀ j, 0 ≤ Θ j)
    (hΘsum : Summable Θ) : Summable (fun N => cutMass u Θ N) := by

  set v : ℕ → ℝ := fun n => ‖u n‖ ^ 2 with hv
  have hv0 : ∀ n, 0 ≤ v n := fun n => by positivity
  -- the outgoing layer is a Cauchy product
  have hpart1 : Summable (fun N => ∑ n ∈ range (N + 1), Θ (N - n) * v n) := by
    have hprod : Summable (fun x : ℕ × ℕ => Θ x.1 * v x.2) :=
      hΘsum.mul_of_nonneg hu hΘ0 hv0
    have hanti := summable_sum_mul_antidiagonal_of_summable_mul hprod
    refine hanti.congr fun N => ?_
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [← Finset.sum_range_reflect (fun k => Θ k * v (N - k)) (N + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    congr 2
    all_goals omega
  -- the incoming layer is an injective reindexing of the product family
  have hpart2 : Summable (fun N => ∑' i : ℕ, Θ i * v (i + (N + 1))) := by
    have hprod : Summable (fun x : ℕ × ℕ => Θ x.1 * v x.2) :=
      hΘsum.mul_of_nonneg hu hΘ0 hv0
    have hinj : Function.Injective (fun p : ℕ × ℕ => (p.2, p.2 + p.1 + 1)) := by
      rintro ⟨N, i⟩ ⟨N', i'⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      have : N = N' := by omega
      simp [this]
    have hcomp : Summable (fun p : ℕ × ℕ => Θ p.2 * v (p.2 + p.1 + 1)) := by
      exact hprod.comp_injective hinj
    exact hcomp.prod
  simpa [cutMass, hv] using hpart1.add hpart2
