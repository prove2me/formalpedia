-- Prove2me | solution 1 for BosonicLearn.displacementMatrix_prod_mul
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T18:50:46.770569+00:00
-- url     : https://prove2.me/submissions/4b797e12-d14e-4e79-8455-4db913348599

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Theorems.Thm_BosonicLearn_displacementMatrix_mul

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

noncomputable section

/-- `PP α`: a product over the finite type `α` of absolutely convergent series over `ℕ` is an
absolutely convergent series over the multi-indices `α → ℕ`, with sum the product of the sums. -/
private def PP (α : Type) [Fintype α] : Prop :=
  ∀ (f : α → ℕ → ℂ) (s : α → ℂ),
      (∀ i, Summable fun k => ‖f i k‖) → (∀ i, HasSum (f i) (s i)) →
      Summable (fun w : α → ℕ => ‖∏ i, f i (w i)‖) ∧
      HasSum (fun w : α → ℕ => ∏ i, f i (w i)) (∏ i, s i)

private lemma PP_equiv (α β : Type) [Fintype α] [Fintype β] (e : α ≃ β) (ih : PP α) : PP β := by
  intro f s hn hs
  obtain ⟨h1, h2⟩ := ih (fun i => f (e i)) (fun i => s (e i)) (fun i => hn (e i))
    (fun i => hs (e i))
  let E : (β → ℕ) ≃ (α → ℕ) := Equiv.arrowCongr e.symm (Equiv.refl ℕ)
  have hE : ∀ w : β → ℕ, ∏ i, f (e i) (E w i) = ∏ j, f j (w j) := by
    intro w
    exact Equiv.prod_comp e (fun j => f j (w j))
  have hsE : ∏ i, s (e i) = ∏ j, s j := Equiv.prod_comp e s
  refine ⟨?_, ?_⟩
  · have := (Equiv.summable_iff E).mpr h1
    have hfun : ((fun w : α → ℕ => ‖∏ i, f (e i) (w i)‖) ∘ E) =
        fun w : β → ℕ => ‖∏ j, f j (w j)‖ := by
      funext w
      show ‖∏ i, f (e i) (E w i)‖ = _
      rw [hE]
    rw [hfun] at this
    exact this
  · have := (Equiv.hasSum_iff E).mpr h2
    have hfun : ((fun w : α → ℕ => ∏ i, f (e i) (w i)) ∘ E) =
        fun w : β → ℕ => ∏ j, f j (w j) := by
      funext w
      show ∏ i, f (e i) (E w i) = _
      rw [hE]
    rw [hfun, hsE] at this
    exact this

private lemma PP_empty : PP PEmpty := by
  intro f s _ _
  have h := hasSum_unique (fun w : PEmpty → ℕ => ∏ i, f i (w i))
  have hn := hasSum_unique (fun w : PEmpty → ℕ => ‖∏ i, f i (w i)‖)
  refine ⟨hn.summable, ?_⟩
  convert h using 1
  simp

private lemma PP_option (α : Type) [Fintype α] (ih : PP α) : PP (Option α) := by
  intro f s hn hs
  obtain ⟨h1, h2⟩ := ih (fun i => f (some i)) (fun i => s (some i)) (fun i => hn (some i))
    (fun i => hs (some i))
  let E : (Option α → ℕ) ≃ ℕ × (α → ℕ) := Equiv.piOptionEquivProd (β := fun _ => ℕ)
  have hmulN : Summable fun x : ℕ × (α → ℕ) => ‖f none x.1 * ∏ i, f (some i) (x.2 i)‖ :=
    Summable.mul_norm (f := f none) (g := fun w : α → ℕ => ∏ i, f (some i) (w i)) (hn none) h1
  have hmulS : Summable fun x : ℕ × (α → ℕ) => f none x.1 * ∏ i, f (some i) (x.2 i) :=
    hmulN.of_norm
  have hmul : HasSum (fun x : ℕ × (α → ℕ) => f none x.1 * ∏ i, f (some i) (x.2 i))
      (s none * ∏ i, s (some i)) :=
    HasSum.mul (f := f none) (g := fun w : α → ℕ => ∏ i, f (some i) (w i)) (hs none) h2 hmulS
  have hEw : ∀ w : Option α → ℕ, E w = (w none, fun i => w (some i)) := fun w => rfl
  refine ⟨?_, ?_⟩
  · have h3 := (Equiv.summable_iff E).mpr hmulN
    have hfun : ((fun x : ℕ × (α → ℕ) => ‖f none x.1 * ∏ i, f (some i) (x.2 i)‖) ∘ E) =
        fun w : Option α → ℕ => ‖∏ j, f j (w j)‖ := by
      funext w
      rw [Function.comp_apply, hEw, Fintype.prod_option (fun j => f j (w j))]
    rw [hfun] at h3
    exact h3
  · have h3 := (Equiv.hasSum_iff E).mpr hmul
    have hfun : ((fun x : ℕ × (α → ℕ) => f none x.1 * ∏ i, f (some i) (x.2 i)) ∘ E) =
        fun w : Option α → ℕ => ∏ j, f j (w j) := by
      funext w
      rw [Function.comp_apply, hEw, Fintype.prod_option (fun j => f j (w j))]
    rw [hfun, ← Fintype.prod_option s] at h3
    exact h3

private lemma hasSum_pi_prod (I : Type) [Fintype I] : PP I := by
  refine Fintype.induction_empty_option (P := fun (α : Type) [Fintype α] => PP α) ?_ ?_ ?_ I
  · intro α β _ e ih
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    exact PP_equiv α β e ih
  · exact PP_empty
  · intro α _ ih
    exact PP_option α ih

theorem solution {I : Type} [Fintype I] (a b : I → ℂ) (u v : I → ℕ) :
    Summable (fun w : I → ℕ => ‖∏ j, displacementMatrix (a j) (u j) (w j)‖ *
      ‖∏ j, displacementMatrix (b j) (w j) (v j)‖) ∧
    HasSum (fun w : I → ℕ => (∏ j, displacementMatrix (a j) (u j) (w j)) *
        ∏ j, displacementMatrix (b j) (w j) (v j))
      (∏ j, Complex.exp ((a j * star (b j) - star (a j) * b j) / 2) *
        displacementMatrix (a j + b j) (u j) (v j)) := by
  have key := hasSum_pi_prod I
    (fun j k => displacementMatrix (a j) (u j) k * displacementMatrix (b j) k (v j))
    (fun j => Complex.exp ((a j * star (b j) - star (a j) * b j) / 2) *
        displacementMatrix (a j + b j) (u j) (v j))
    (fun j => by
      have h := (BosonicLearn.displacementMatrix_mul (a j) (b j) (u j) (v j)).1
      simpa only [norm_mul] using h)
    (fun j => (BosonicLearn.displacementMatrix_mul (a j) (b j) (u j) (v j)).2)
  have hfun : ∀ w : I → ℕ,
      ∏ j, displacementMatrix (a j) (u j) (w j) * displacementMatrix (b j) (w j) (v j) =
      (∏ j, displacementMatrix (a j) (u j) (w j)) * ∏ j, displacementMatrix (b j) (w j) (v j) :=
    fun w => Finset.prod_mul_distrib
  refine ⟨?_, ?_⟩
  · have h1 := key.1
    simp only [hfun, norm_mul] at h1
    exact h1
  · have h2 := key.2
    simp only [hfun] at h2
    exact h2
