-- Prove2me | solution 1 for ConstATSP.Gap.singleton_tour_le_ten
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:04:44.385916+00:00
-- url     : https://prove2.me/submissions/a390bee3-a2be-44cc-8aa4-094cde761e7d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ConstATSP_Gap_Graph
import Definitions.Def_ConstATSP_Gap_Instance
import Theorems.Thm_ConstATSP_Gap_theorem_5_1
import Theorems.Thm_ConstATSP_Gap_theorem_4_1

open ConstATSP.Gap

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (I : ConstATSP.Gap.Instance V E) (hI : I.IsValid)
    (hS : I.IsSingleton) :
    ∃ F : E → ℕ, IsTour I.G F ∧ I.wt F ≤ 10 * I.value := by
  have hv0 : vertsOf I.G (0 : E → ℕ) = ∅ := by
    ext v; simp [vertsOf]
  have hsub : IsSubtour I.G (0 : E → ℕ) := by
    refine ⟨fun v => by simp, ?_⟩
    rw [hv0]; intro u hu; simp at hu
  obtain ⟨F, hF, hwt⟩ := theorem_5_1 I hI 0 hsub 2 0 (by norm_num) (theorem_4_1 I hI hS)
  refine ⟨F, hF, le_trans hwt ?_⟩
  have hw0 : I.wt (0 : E → ℕ) = 0 := by simp [Instance.wt]
  have hlb : I.lbCompl 0 = 2 * ∑ v, I.yv v := by
    simp [Instance.lbCompl, Instance.lb, hv0]
  -- every set of L is a proper singleton
  have hL : I.L.filter (fun R => R ⊂ Finset.univ) = I.L := by
    apply Finset.filter_true_of_mem
    intro R hR
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 (hS R hR)
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_univ _, fun h => ?_⟩
    have : Fintype.card V = 1 := by
      rw [← Finset.card_univ, ← h]; simp
    have := hI.1; omega
  have himg : I.L = (Finset.univ.filter (fun v => ({v} : Finset V) ∈ I.L)).image
      (fun v => ({v} : Finset V)) := by
    ext R
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hR
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 (hS R hR)
      exact ⟨v, hR, rfl⟩
    · rintro ⟨v, hv, rfl⟩; exact hv
  have hsum : ∑ v, I.yv v = ∑ R ∈ I.L.filter (fun R => R ⊂ Finset.univ), I.y R := by
    rw [hL]
    conv_rhs => rw [himg]
    rw [Finset.sum_image (fun a _ b _ h => Finset.singleton_injective h)]
    rw [Finset.sum_filter]
    rfl
  have hval : I.value = 2 * ∑ R ∈ I.L.filter (fun R => R ⊂ Finset.univ), I.y R := rfl
  rw [hw0, hlb, hval, hsum]
  linarith
