-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.exists_perm_init_comp_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:26.910149+00:00
-- url     : https://prove2.me/submissions/70ef5776-b985-4e57-a15d-55eeaa568baf

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Multilinear

noncomputable section
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- If `σ (last d) = k`, the first `d` entries of `h ∘ σ` are a permutation of `h` without `h k`. -/
theorem solution {α : Type*} {d : ℕ} (h : Fin (d + 1) → α)
    (σ : Equiv.Perm (Fin (d + 1))) {k : Fin (d + 1)} (hk : σ (Fin.last d) = k) :
    ∃ τ : Equiv.Perm (Fin d), Fin.init (h ∘ σ) = k.removeNth h ∘ τ := by
    have hne : ∀ i : Fin d, σ (Fin.castSucc i) ≠ k := by
      intro i hi
      have heq : σ (Fin.castSucc i) = σ (Fin.last d) := hi.trans hk.symm
      exact (Fin.castSucc_ne_last i) (σ.injective heq)
    let f : Fin d → Fin d := fun i =>
      Classical.choose (Fin.exists_succAbove_eq (hne i))
    have hf : ∀ i : Fin d, k.succAbove (f i) = σ (Fin.castSucc i) := by
      intro i
      dsimp [f]
      exact Classical.choose_spec (Fin.exists_succAbove_eq (hne i))
    have hinj : Function.Injective f := by
      intro i j hij
      apply Fin.castSucc_injective
      apply σ.injective
      calc
        σ (Fin.castSucc i) = k.succAbove (f i) := (hf i).symm
        _ = k.succAbove (f j) := congrArg (k.succAbove) hij
        _ = σ (Fin.castSucc j) := hf j
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, by simp⟩
    let τ : Equiv.Perm (Fin d) := Equiv.ofBijective f hbij
    refine ⟨τ, ?_⟩
    funext i
    change h (σ (Fin.castSucc i)) = h (k.succAbove (f i))
    exact (congrArg h (hf i)).symm
