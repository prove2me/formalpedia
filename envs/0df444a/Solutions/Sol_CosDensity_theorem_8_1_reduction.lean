-- Prove2me | solution 1 for CosDensity.theorem_8_1_reduction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T20:56:10.517906+00:00
-- url     : https://prove2.me/submissions/8aaf19e2-08f8-464e-b0be-7f97b3f76af4

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_StreamAlg
import Definitions.Def_CosDensity_OneWayProtocol

open MeasureTheory

namespace Aux_CosDensity_thm81

theorem runFrom_append {E Ω S : Type*} (A : CosDensity.StreamAlg E Ω S) (ω : Ω) (n : ℕ) :
    ∀ (l₁ l₂ : List E) (t : ℕ) (s : S),
      A.runFrom ω n t (l₁ ++ l₂) s = A.runFrom ω n (t + l₁.length) l₂ (A.runFrom ω n t l₁ s) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ t s; simp [CosDensity.StreamAlg.runFrom]
  | cons x xs ih =>
    intro l₂ t s
    simp only [List.cons_append, CosDensity.StreamAlg.runFrom, List.length_cons]
    rw [ih]
    congr 1
    omega

end Aux_CosDensity_thm81

open CosDensity in
theorem solution {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {N : ℕ} (p : ℕ) (ε : ℝ) (pre : (Fin N → Bool) → List E) (suf : Fin N → List E)
    (n₁ n₂ : ℕ) (hpre : ∀ z, (pre z).length = n₁) (hsuf : ∀ q, (suf q).length = n₂)
    (θ : Fin N → ℝ)
    (hsep : ∀ (z : Fin N → Bool) (q : Fin N) (Y : ℝ),
      IsApprox ε (moment p (pre z ++ suf q)) Y → (z q = true ↔ θ q < Y))
    (Ω S : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : StreamAlg E Ω S)
    (hA : ∀ (z : Fin N → Bool) (q : Fin N),
      SucceedsWP μ (fun ω => IsApprox ε (moment p (pre z ++ suf q))
        (A.estimate ω (pre z ++ suf q))) (2 / 3)) :
    ∃ π : OneWayProtocol N Ω S, SolvesIndex μ π := by
  classical
  refine ⟨⟨fun ω z => A.runFrom ω (n₁ + n₂) 0 (pre z) (A.init ω (n₁ + n₂)),
    fun ω s q => decide (θ q < A.out ω (n₁ + n₂) (A.runFrom ω (n₁ + n₂) n₁ (suf q) s))⟩, ?_⟩
  intro z q
  obtain ⟨B, hBm, hBsub, hBμ⟩ := hA z q
  refine ⟨B, hBm, ?_, hBμ⟩
  intro ω hω
  have hgood := hBsub hω
  simp only [Set.mem_setOf_eq] at hgood ⊢
  have hlen : (pre z ++ suf q).length = n₁ + n₂ := by
    rw [List.length_append, hpre, hsuf]
  have hest : A.estimate ω (pre z ++ suf q) =
      A.out ω (n₁ + n₂) (A.runFrom ω (n₁ + n₂) n₁ (suf q)
        (A.runFrom ω (n₁ + n₂) 0 (pre z) (A.init ω (n₁ + n₂)))) := by
    unfold StreamAlg.estimate StreamAlg.run
    rw [hlen, Aux_CosDensity_thm81.runFrom_append, hpre, Nat.zero_add]
  have key := hsep z q _ hgood
  rw [hest] at key
  cases hz : z q
  · rw [hz] at key
    simp only [Bool.false_eq_true, false_iff] at key
    simp [key]
  · rw [hz] at key
    simp only [true_iff] at key
    simp [key]
