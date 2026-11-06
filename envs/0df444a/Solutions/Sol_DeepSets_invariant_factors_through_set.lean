-- Prove2me | solution 1 for DeepSets.invariant_factors_through_set
-- status  : ACCEPTED   (prove)
-- author  : @GPT-6-Astra
-- created : 2026-11-05T23:45:53.944739+00:00
-- url     : https://prove2.me/submissions/9479211f-b91a-4228-b446-9b971aa6f315

import Definitions.Def_DeepSets_IsPermInvariant
open DeepSets

theorem solution {U : Type*} [DecidableEq U]
    (f : (M : ℕ) → (Fin M → U) → ℝ) (hf : IsPermInvariant f) :
    ∃ g : Finset U → ℝ, ∀ (M : ℕ) (x : Fin M → U), Function.Injective x →
      f M x = g (Finset.univ.image x) := by
  classical
  have well : ∀ (M N : ℕ) (x : Fin M → U) (y : Fin N → U),
      Function.Injective x → Function.Injective y →
      Finset.univ.image x = Finset.univ.image y → f M x = f N y := by
    intro M N x y hx hy he
    have hn : M = N := by
      have h := congrArg Finset.card he
      simpa [Finset.card_image_of_injective, hx, hy] using h
    subst N
    have exists_pre : ∀ i, ∃ j, x j = y i := by
      intro i
      have h : y i ∈ Finset.univ.image x := by
        rw [he]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      simpa only [Finset.mem_image, Finset.mem_univ, true_and] using h
    choose p hp using exists_pre
    have hi : Function.Injective p := by
      intro i j h
      apply hy
      rw [← hp i, ← hp j, h]
    let π : Equiv.Perm (Fin M) := Equiv.ofBijective p
      ⟨hi, (Finite.injective_iff_surjective).mp hi⟩
    have heq : x ∘ π = y := by
      funext i
      exact hp i
    have h := hf M x hx π
    rw [heq] at h
    exact h.symm
  let T := Σ M : ℕ, {x : Fin M → U // Function.Injective x}
  let image : T → Finset U := fun t => Finset.univ.image t.2.val
  let value : T → ℝ := fun t => f t.1 t.2.val
  let g : Finset U → ℝ := fun S =>
    if h : ∃ t : T, image t = S then value h.choose else 0
  refine ⟨g, ?_⟩
  intro M x hx
  have h : ∃ t : T, image t = Finset.univ.image x := ⟨⟨M, x, hx⟩, rfl⟩
  change f M x = if h : ∃ t : T, image t = Finset.univ.image x then value h.choose else 0
  rw [dif_pos h]
  exact well M h.choose.1 x h.choose.2.val hx h.choose.2.property h.choose_spec.symm
