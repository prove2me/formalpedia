-- Prove2me | solution 1 for DantzigSelector.Sparse.cone_constraint
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T00:54:15.812186+00:00
-- url     : https://prove2.me/submissions/d18b76b2-c663-48a0-9ca7-bbb3d391f42b

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model

set_option autoImplicit false

open CandesTao.Decoding DantzigSelector.Sparse in
theorem solution {p : ℕ} (β h : Fin p → ℝ) (T0 : Finset (Fin p))
    (hβ : SupportedOn β T0) (hle : l1Norm (β + h) ≤ l1Norm β) :
    l1On h T0ᶜ ≤ l1On h T0 := by
  unfold l1Norm at hle
  unfold l1On
  rw [← Finset.sum_add_sum_compl T0 (fun j => |(β + h) j|),
    ← Finset.sum_add_sum_compl T0 (fun j => |β j|)] at hle
  have h1 : ∑ j ∈ T0ᶜ, |(β + h) j| = ∑ j ∈ T0ᶜ, |h j| := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have : β j = 0 := hβ j (Finset.mem_compl.mp hj)
    simp [Pi.add_apply, this]
  have h2 : ∑ j ∈ T0ᶜ, |β j| = 0 := by
    refine Finset.sum_eq_zero (fun j hj => ?_)
    simp [hβ j (Finset.mem_compl.mp hj)]
  have h3 : ∑ j ∈ T0, (|β j| - |h j|) ≤ ∑ j ∈ T0, |(β + h) j| := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    have := abs_sub_abs_le_abs_sub (β j) (-(h j))
    simp only [sub_neg_eq_add, abs_neg] at this
    simpa [Pi.add_apply] using this
  rw [Finset.sum_sub_distrib] at h3
  linarith
