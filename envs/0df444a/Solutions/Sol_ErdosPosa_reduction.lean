-- Prove2me | solution 1 for ErdosPosa.reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:40:59.932061+00:00
-- url     : https://prove2.me/submissions/e0eb90ec-04cc-474d-9012-1f706de20c38

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPPin
public import Definitions.Def_ErdosPosaLib_EPMain
public import Theorems.Thm_ErdosPosa_gEP_spec
public import Theorems.Thm_ErdosPosa_psi_eq_ncard_of_deg023
public import Theorems.Thm_ErdosPosa_IsMax023_fvs_or_pack
public import Theorems.Thm_ErdosPosa_cyc_mono
public import Theorems.Thm_ErdosPosa_exists_isMax023
public import Theorems.Thm_ErdosPosa_packing


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution [Finite V] (G : SimpleGraph V) (j : ℕ) :
    (∃ F : Fin (j + 1) → Set V, Pairwise (fun i i' => Disjoint (F i) (F i')) ∧
      ∀ i, Cyc G (F i)) ∨
    ∃ X : Set V, X.ncard ≤ gEP (j + 1) + j ∧ ¬ Cyc G Xᶜ := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨H, hH⟩ := exists_isMax023 G
  have hpsi := psi_eq_ncard_of_deg023 hH.2.1
  by_cases hbig : (gEP (j + 1) : ℤ) ≤ psi H
  · obtain ⟨F, hF, hFc⟩ := packing gEP gEP_spec (j + 1) H
      (fun v => by rcases hH.2.1 v with h | h | h <;> omega) hbig
    exact Or.inl ⟨F, hF, fun i => cyc_mono (hFc i) hH.1 subset_rfl⟩
  · rcases hH.fvs_or_pack j {v | deg H v = 3}ᶜ (fun v hv => hv) with
      ⟨F, hF, -, hFc⟩ | ⟨Z, hZ, hZc⟩
    · exact Or.inl ⟨F, hF, hFc⟩
    · refine Or.inr ⟨{v | deg H v = 3} ∪ ↑Z, ?_, ?_⟩
      · have := Set.ncard_union_le {v | deg H v = 3} (↑Z : Set V)
        rw [Set.ncard_coe_finset] at this
        omega
      · rw [Set.compl_union, ← Set.sdiff_eq]
        exact hZc
end ErdosPosa
