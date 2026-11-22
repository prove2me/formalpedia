-- Prove2me | solution 1 for DiazModulus.rational_preimage_finrank
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-21T09:04:16.536159+00:00
-- url     : https://prove2.me/submissions/48806162-69f0-41a3-a0ff-a27a370acf83

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_qbar_linearIndependent_complex

open Complex ComplexConjugate

/-! # A rational preimage of the algebraic part of a subspace

Let `z₁, …, z_l` be the columns of `M`, `W` their `Q̄`-span and `Y = W ∩ T`, a finite-dimensional `Q̄`-space.
Take a `Q̄`-basis `y₁, …, y_n` of `Y`. Each `y_k` lies in `W`, so `y_k = Σⱼ c_{k,j} zⱼ = M b_k` with an algebraic
vector `b_k = (c_{k,j})ⱼ`. The `b_k` are `Q̄`-free, because `b ↦ M b` is `Q̄`-linear and sends them to the free
family `y_k`. Being algebraic and `Q̄`-free, they are `ℂ`-free. Put `S = span_ℂ(b₁, …, b_n)`: it is spanned by
algebraic vectors, so it is rational; `M b_k = y_k ∈ T` and `T` is a `ℂ`-subspace, so `M S ⊆ T`; and
`dim_ℂ S = n = dim_Q̄ (W ∩ T)`. -/

open DiazModulus in
theorem solution {d l : ℕ} (M : Matrix (Fin d) (Fin l) ℂ)
    (hker : ∀ b : Fin l → ℂ, (∀ j, b j ∈ Qbar) → M.mulVec b = 0 → b = 0)
    (T : Submodule ℂ (Fin d → ℂ)) :
    ∃ S : Submodule ℂ (Fin l → ℂ),
      Submodule.span ℂ {v : Fin l → ℂ | v ∈ S ∧ ∀ j, v j ∈ Qbar} = S ∧
      (∀ s ∈ S, M.mulVec s ∈ T) ∧
      Module.finrank ℂ ↥S = Module.finrank (↥Qbar)
        ↥(Submodule.span (↥Qbar) (Set.range fun j i => M i j) ⊓ T.restrictScalars (↥Qbar)) := by
  classical
  set Y := Submodule.span (↥Qbar) (Set.range fun j i => M i j) ⊓ T.restrictScalars (↥Qbar) with hY
  have : Module.Finite (↥Qbar) (Submodule.span (↥Qbar) (Set.range fun j i => M i j)) :=
    FiniteDimensional.span_of_finite (↥Qbar) (Set.finite_range _)
  let y := Module.finBasis (↥Qbar) Y
  have hlift : ∀ k, ∃ c : Fin l → ↥Qbar, ∑ j, c j • (fun i => M i j) = (y k : Fin d → ℂ) := fun k =>
    (Submodule.mem_span_range_iff_exists_fun (↥Qbar)).1 (Submodule.mem_inf.1 (y k).2).1
  choose c hc using hlift
  set b : Fin (Module.finrank (↥Qbar) Y) → Fin l → ℂ := fun k j => (c k j : ℂ) with hb
  have hMb : ∀ k, M.mulVec (b k) = (y k : Fin d → ℂ) := by
    intro k
    rw [← hc k]
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Subfield.smul_def, hb, mul_comm]
  have hbQ : LinearIndependent (↥Qbar) b := by
    apply LinearIndependent.of_comp ((M.mulVecLin).restrictScalars (↥Qbar))
    have : ((M.mulVecLin).restrictScalars (↥Qbar)) ∘ b = fun k => (y k : Fin d → ℂ) := by
      funext k
      exact hMb k
    rw [this]
    exact y.linearIndependent.map' Y.subtype (Submodule.ker_subtype Y)
  have hbC : LinearIndependent ℂ b :=
    DiazModulus.qbar_linearIndependent_complex b (fun k j => (c k j).2) hbQ
  refine ⟨Submodule.span ℂ (Set.range b), ?_, ?_, ?_⟩
  · apply le_antisymm
    · exact Submodule.span_le.2 fun v hv => hv.1
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨Submodule.subset_span ⟨k, rfl⟩, fun j => (c k j).2⟩
  · intro s hs
    have hle : Submodule.span ℂ (Set.range b) ≤ T.comap M.mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      show M.mulVecLin (b k) ∈ T
      rw [Matrix.mulVecLin_apply, hMb]
      exact (Submodule.mem_inf.1 (y k).2).2
    exact hle hs
  · rw [finrank_span_eq_card hbC, Fintype.card_fin]
