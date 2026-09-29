-- Prove2me | solution 1 for EulerMascheroni.Mixed.arithmetic_quotient_iff_boundary_algebraic
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T15:05:19.448535+00:00
-- url     : https://prove2.me/submissions/255bc378-63af-4767-8253-c76e4ffb8ca5

import Theorems.Thm_EulerMascheroni_Mixed_algebraic_quotient_boundary
open Filter
open scoped Topology
namespace EulerQuotientAudit
lemma decaying_quotient (f : ℕ → ℂ) (s : ℂ) (hs : HasSum f s) :
    ∃ u : ℕ → ℂ, u 0 = s-f 0 ∧
      (∀ n, u (n+1)=u n-f (n+1)) ∧ Tendsto u atTop (𝓝 0) := by
  refine ⟨fun n => s-∑ k ∈ Finset.range (n+1), f k, ?_, ?_, ?_⟩
  · simp
  · intro n
    dsimp only
    rw [Finset.sum_range_succ]
    ring
  · have ht := hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    simpa using (tendsto_const_nhds (x := s)).sub ht
lemma arithmetic_quotient_iff (f : ℕ → ℂ) (s : ℂ)
    (hf : ∀ n, IsAlgebraic ℚ (f n)) (hs : HasSum f s) :
    IsAlgebraic ℚ s ↔
    ∃ u : ℕ → ℂ, u 0 = s-f 0 ∧
      (∀ n, u (n+1)=u n-f (n+1)) ∧ Tendsto u atTop (𝓝 0) ∧
        ∀ n, IsAlgebraic ℚ (u n) := by
  constructor
  · intro hsa
    obtain ⟨u, hu0, hrec, hlim⟩ := decaying_quotient f s hs
    refine ⟨u,hu0,hrec,hlim,?_⟩
    intro n
    induction n with
    | zero => rw [hu0]; exact hsa.sub (hf 0)
    | succ n ih => rw [hrec]; exact ih.sub (hf (n+1))
  · rintro ⟨u,hu0,hrec,hlim,halg⟩
    exact EulerMascheroni.Mixed.algebraic_quotient_boundary f u s s hu0 hrec hs hlim (hf 0) (halg 0)
end EulerQuotientAudit


theorem solution (f : ℕ → ℂ) (s : ℂ)
    (hf : ∀ n, IsAlgebraic ℚ (f n)) (hs : HasSum f s) :
    IsAlgebraic ℚ s ↔
    ∃ u : ℕ → ℂ, u 0 = s-f 0 ∧
      (∀ n, u (n+1)=u n-f (n+1)) ∧ Tendsto u atTop (𝓝 0) ∧
        ∀ n, IsAlgebraic ℚ (u n) := by
  exact EulerQuotientAudit.arithmetic_quotient_iff f s hf hs

#print axioms solution
