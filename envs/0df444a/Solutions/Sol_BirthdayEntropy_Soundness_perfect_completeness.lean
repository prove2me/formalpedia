-- Prove2me | solution 1 for BirthdayEntropy.Soundness.perfect_completeness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:34:15.021736+00:00
-- url     : https://prove2.me/submissions/21c41c87-69ff-4d13-a3ff-fd0385fc0b12

import Definitions.Def_BirthdayEntropy_Soundness_Graph
noncomputable section
open scoped Classical
open BirthdayEntropy.Soundness

theorem solution (n m : ℕ) (φ : CSP n m) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n) (hφ : Satisfiable φ) :
    HasTargetClique φ ℓ := by
  classical
  obtain ⟨g, hg⟩ := hφ
  let v : View n ℓ → Vertex n ℓ := fun S => ⟨S, fun i => g i.val⟩
  have hinj : Function.Injective v := by
    intro S T h
    exact congrArg Sigma.fst h
  refine ⟨Finset.univ.image v, ?_, ?_⟩
  · simpa [Finset.card_image_of_injective _ hinj] using card_view n ℓ
  intro a ha b hb hab
  obtain ⟨S, -, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨T, -, rfl⟩ := Finset.mem_image.mp hb
  have hs : ∀ (U : View n ℓ) i b, (i, b) ∈ signed (v U) → g i = b := by
    intro U i b h
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
    have hi : j.val = i := congrArg Prod.fst hj
    have hh : g j.val = b := congrArg Prod.snd hj
    simpa only [hi] using hh
  have hu : ∀ i b, (i, b) ∈ signed (v S) ∪ signed (v T) → g i = b := by
    intro i b h
    rcases Finset.mem_union.mp h with h | h
    · exact hs S i b h
    · exact hs T i b h
  refine ⟨hab, ?_, ?_⟩
  · intro i hi
    have h0 := hu i false hi.1
    have h1 := hu i true hi.2
    simp_all
  · intro j hj
    have heq : assignment (signed (v S) ∪ signed (v T)) ∘ φ.H.M j = g ∘ φ.H.M j := by
      funext k
      have hm : φ.H.M j k ∈ support (signed (v S) ∪ signed (v T)) := by
        apply hj
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
      obtain ⟨⟨i, b⟩, hmem, heq⟩ := Finset.mem_image.mp hm
      simp only [Prod.fst] at heq
      subst i
      have hbit := hu _ b hmem
      dsimp [Function.comp_def, assignment]
      cases b with
      | false =>
        have hn : (φ.H.M j k, true) ∉ signed (v S) ∪ signed (v T) := by
          intro ht
          have hh := hu _ true ht
          rw [hbit] at hh
          contradiction
        simp [hn, hbit]
      | true => simp [hmem, hbit]
    rw [heq]
    exact hg j
