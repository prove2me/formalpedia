-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_apply_comp_cast_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:42:19.859319+00:00
-- url     : https://prove2.me/submissions/55268283-9456-4ae0-8a6b-a87e92b09af2

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
section Slots
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.extendPerm_castAdd {q r : ℕ} (τ : Equiv.Perm (Fin q)) (i : Fin q) :
    FunctionalInequalities.KLS.LogConcave.PoissonIterate.extendPerm (r := r) τ (Fin.castAdd r i) = Fin.castAdd r (τ i) := by
  simp [FunctionalInequalities.KLS.LogConcave.PoissonIterate.extendPerm, Equiv.permCongr_apply]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.extendPerm_natAdd {q r : ℕ} (τ : Equiv.Perm (Fin q)) (j : Fin r) :
    FunctionalInequalities.KLS.LogConcave.PoissonIterate.extendPerm τ (Fin.natAdd q j) = Fin.natAdd q j := by
  simp [FunctionalInequalities.KLS.LogConcave.PoissonIterate.extendPerm, Equiv.permCongr_apply]
/-- Sums over the permutations of the first `q` positions are sums over `Perm (Fin q)`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_fixingOutside_slots {M : Type*} [AddCommMonoid M] {q r : ℕ}
    (g : Equiv.Perm (Fin (q + r)) → M) :
    ∑ σ ∈ fixingOutside (slots (q + r) 0 q), g σ = ∑ τ : Equiv.Perm (Fin q), g (FunctionalInequalities.KLS.LogConcave.PoissonIterate.extendPerm τ) := by
  classical
  symm
  refine Finset.sum_bij (fun τ _ => FunctionalInequalities.KLS.LogConcave.PoissonIterate.extendPerm τ) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro τ _
    simp only [fixingOutside, Finset.mem_filter, Finset.mem_univ, true_and]
    intro x hx
    induction x using Fin.addCases with
    | left i => exact absurd (by simp [slots]) hx
    | right j => exact extendPerm_natAdd τ j
  · intro τ₁ _ τ₂ _ h
    ext i
    have := congrArg (fun σ : Equiv.Perm (Fin (q + r)) => (σ (Fin.castAdd r i) : ℕ)) h
    simpa [extendPerm_castAdd] using this
  · intro σ hσ
    simp only [fixingOutside, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    have hlt : ∀ i : Fin q, (σ (Fin.castAdd r i) : ℕ) < q := by
      intro i
      by_contra hc
      have hy : σ (Fin.castAdd r i) ∉ slots (q + r) 0 q := by simp [slots, hc]
      have h1 := σ.injective (hσ _ hy)
      have h2 := congrArg Fin.val h1
      simp at h2
      omega
    let f : Fin q → Fin q := fun i => ⟨σ (Fin.castAdd r i), hlt i⟩
    have hf : Function.Injective f := by
      intro i j hij
      have h1 : σ (Fin.castAdd r i) = σ (Fin.castAdd r j) :=
        Fin.ext (by simpa [f] using congrArg Fin.val hij)
      exact Fin.castAdd_injective q r (σ.injective h1)
    refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), Finset.mem_univ _, ?_⟩
    ext x
    induction x using Fin.addCases with
    | left i => simp [extendPerm_castAdd, f]
    | right j =>
      rw [extendPerm_natAdd]
      exact congrArg Fin.val (hσ _ (by simp [slots])).symm
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.card_fixingOutside_slots {q r : ℕ} :
    (fixingOutside (slots (q + r) 0 q)).card = q.factorial := by
  rw [Finset.card_eq_sum_ones, sum_fixingOutside_slots (fun _ => 1)]
  simp [Fintype.card_perm]
/-- `S_q` of a coordinate tensor, read entrywise: the average over the permutations `τ` of the
first `q` indices of `J`, the last `r` indices kept. -/
theorem solution {n N q r : ℕ} (h : N = q + r) (A : FunctionalInequalities.Analysis.Tensor.Coord n N)
    (J : Fin (q + r) → Fin n) :
    FunctionalInequalities.Analysis.Tensor.symmetrize n N q A (J ∘ Fin.cast h) =
      (q.factorial : ℝ)⁻¹ * ∑ τ : Equiv.Perm (Fin q),
        A (Fin.append (J ∘ Fin.castAdd r ∘ τ) (J ∘ Fin.natAdd q) ∘ Fin.cast h) := by
  subst h
  simp only [FunctionalInequalities.Analysis.Tensor.symmetrize, FunctionalInequalities.Analysis.Tensor.blockAverage, FunctionalInequalities.Analysis.Tensor.slotRep, MonoidHom.coe_mk, OneHom.coe_mk,
    PiLp.smul_apply, smul_eq_mul, FunctionalInequalities.KLS.LogConcave.PoissonIterate.card_fixingOutside_slots]
  congr 1
  rw [WithLp.ofLp_sum, Finset.sum_apply, FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_fixingOutside_slots]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [FunctionalInequalities.Analysis.Tensor.slotPerm_apply]
  refine congrArg A.ofLp (funext fun x => ?_)
  induction x using Fin.addCases with
  | left i => simp [FunctionalInequalities.KLS.LogConcave.PoissonIterate.extendPerm_castAdd]
  | right j => simp [FunctionalInequalities.KLS.LogConcave.PoissonIterate.extendPerm_natAdd]
