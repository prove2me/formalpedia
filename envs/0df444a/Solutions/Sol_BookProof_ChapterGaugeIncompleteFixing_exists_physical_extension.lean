-- Prove2me | solution 1 for BookProof.ChapterGaugeIncompleteFixing.exists_physical_extension
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:32:30.745274+00:00
-- url     : https://prove2.me/submissions/caec4846-740c-4a14-85ae-ca3a6b6fc73f

-- Generated from ChapterGaugeIncompleteFixing.lean — solution of BookProof.ChapterGaugeIncompleteFixing.exists_physical_extension
import Mathlib
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing



open scoped InnerProductSpace

variable {X : Type*}
variable (G : Type*) [Group G] [MulAction G X]

set_option maxHeartbeats 1000000 in
theorem solution {S : Set X}
    (hS : IsComprehensiveGaugeFixing G S) (h : X → ℝ)
    (hrem : ∀ s ∈ S, ∀ t ∈ S, ∀ g : G, g • s = t → h s = h t) :
    ∃ f : X → ℝ, IsPhysicalObservable G f ∧ ∀ s ∈ S, f s = h s := by

  classical
  -- choose, in every gauge equivalence class, a representative inside `S`
  have hrep : ∀ c : Quotient (MulAction.orbitRel G X),
      ∃ s : X, s ∈ S ∧ Quotient.mk (MulAction.orbitRel G X) s = c := by
    intro c
    induction c using Quotient.inductionOn with
    | h x =>
      obtain ⟨s, hsS, g, hg⟩ := hS x
      refine ⟨s, hsS, ?_⟩
      rw [← hg]
      exact (Quotient.sound (MulAction.mem_orbit s g)).symm
  set r : Quotient (MulAction.orbitRel G X) → X := fun c => (hrep c).choose
  have hrS : ∀ c, r c ∈ S := fun c => (hrep c).choose_spec.1
  have hrmk : ∀ c, Quotient.mk (MulAction.orbitRel G X) (r c) = c :=
    fun c => (hrep c).choose_spec.2
  refine ⟨fun x => h (r (Quotient.mk (MulAction.orbitRel G X) x)), ?_, ?_⟩
  · intro g x
    have hq : Quotient.mk (MulAction.orbitRel G X) (g • x)
        = Quotient.mk (MulAction.orbitRel G X) x :=
      Quotient.sound (MulAction.mem_orbit x g)
    simp only [hq]
  · intro s hsS
    have hmk : Quotient.mk (MulAction.orbitRel G X)
        (r (Quotient.mk (MulAction.orbitRel G X) s)) =
        Quotient.mk (MulAction.orbitRel G X) s := hrmk _
    obtain ⟨g, hg⟩ := Quotient.exact hmk
    simp only at hg
    exact (hrem s hsS _ (hrS _) g hg).symm
