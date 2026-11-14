-- Prove2me | solution 1 for BCFGJPSSV26.Stable.Partition.costF_S_le_PsiLS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:04:43.673195+00:00
-- url     : https://prove2.me/submissions/d2ce7a72-47bd-4ec8-80b5-8482d9eead4a

module

public import Definitions.Def_BCFGJPSSV26_Stable_Structure_Partition
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_Refined
public import Definitions.Def_BCFGJPSSV26_Stable_LSBound_NiceMaps
import all Definitions.Def_BCFGJPSSV26_Stable_LSBound_NiceMaps
public import Theorems.Thm_BCFGJPSSV26_Stable_costF_le_four_opt
public import Theorems.Thm_BCFGJPSSV26_Stable_refined_ls

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Partition

variable {X : Ctx} {Λ₁ : List (Dummy X.I)} {w₁ : ClientWitness X Λ₁}
  {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {w₂ : ClusterWitness w₁ LS' Λ₂}
  (Q : Partition w₂)

section Maps

variable (H : Hyp X)

end Maps

/-- **The nice cross-free pair** ([BCFGJPSSV26b, Lemma 3.7]). -/
theorem exists_nice_maps (H : Hyp X) :
    ∃ (B : Finset (Fin X.I.m)) (μA μB : Fin X.I.n → Fin X.I.m) (D₀ : Finset (Fin X.I.n)),
      (∀ j, μA j ∈ X.S) ∧ (∀ j, μB j ∈ B) ∧ B.card + (D₀ᶜ.image μA).card ≤ X.I.k ∧
      CrossFreeWrt X.I X.S μA μB D₀ ∧
      X.I.costMap μB D₀ + (X.I.costMap μA univ - X.I.costOn X.S D₀) ≤
        Q.PsiLS + 39 * X.ε * X.opt ∧
      X.I.costMap μA univ + X.I.costMap μB D₀ ≤ 10 * X.opt := by
  classical
  have hv := H.valid
  have hε := H.eps_pos
  have hε' : X.ε ≤ 1 / 201 := X.P.eps_le
  have hopt : 0 ≤ X.opt := H.opt_pos.le
  have hεo := mul_nonneg hε.le hopt
  have hεo' : X.ε * X.opt ≤ X.opt / 201 := by nlinarith
  have hA := Q.costMap_nmA_le H
  have hPsi := Q.nm_PsiLS_le H
  have hS4 : X.I.costF X.S ≤ 4 * X.opt := costF_le_four_opt hv H.k_le_m X.P.hN H.alo
  by_cases hB : (w₁.OLe ∪ Q.OR).Nonempty
  · -- the main case: `B = O_Λᵉ ∪ O_R`, `D₀ = D_Λᵉ ∪ D_R`
    have hBm := Q.costMap_nmBm_le H
    have hD := Q.costOn_sub_costOn_nmD0 H
    have hSD : X.I.costOn X.S (Q.nmD0 H) ≤ X.I.costF X.S := Instance.costOn_le_costF hv _ _
    refine ⟨w₁.OLe ∪ Q.OR, Q.nmA H, Q.nmBm H, Q.nmD0 H, Q.nmA_mem H, Q.nmBm_mem H hB,
      Q.nm_card_size H, Q.nm_crossFree H, ?_, ?_⟩
    · linarith
    · linarith
  · -- no early or remaining cluster: `B = O`, `D₀ = D`, `μB = π_OPT`
    have hE : w₁.OLe ∪ Q.OR = ∅ := not_nonempty_iff_eq_empty.1 hB
    have hΓ : ∀ j, ¬ Q.nmInΓ H j := fun j h ↦ hB ⟨_, h.1⟩
    have hBm : ∀ j, Q.nmBm H j = nmO H j := by
      intro j
      unfold nmBm
      rw [if_neg (hΓ j), if_neg (fun h ↦ hB ⟨_, h⟩), dif_neg hB]
    have hBopt : X.I.costMap (Q.nmBm H) univ = X.opt := by
      have : X.I.costMap (Q.nmBm H) univ = X.I.costF X.O :=
        sum_congr rfl fun j _ ↦ by rw [hBm j, dd_nmO]
      rw [this]
      exact H.isOpt.cost
    have hoptS : X.opt ≤ X.I.costF X.S := Instance.opt_le_costF H.S_nonempty (by rw [H.alo.1])
    rw [hE, sum_empty] at hA
    refine ⟨X.O, Q.nmA H, Q.nmBm H, univ, Q.nmA_mem H, fun j ↦ (hBm j) ▸ nmO_mem H j, ?_, ?_,
      ?_, ?_⟩
    · simp [H.isOpt.card]
    · intro c _ c'
      by_cases hc' : Q.nmSub c' = c
      · right
        right
        intro j hj
        have hjB : Q.nmBm H j = c' := (mem_filter.1 hj).2.1
        refine mem_filter.2 ⟨mem_univ _, ?_⟩
        rw [Q.nmA_of_not H (hΓ j), ← hBm j, hjB, hc']
      · left
        rw [disjoint_left]
        intro j hj hj'
        have hjc : Q.nmA H j = c := (mem_filter.1 hj).2
        have hjB : Q.nmBm H j = c' := (mem_filter.1 hj').2.1
        rw [Q.nmA_of_not H (hΓ j), ← hBm j, hjB] at hjc
        exact hc' hjc
    · rw [hBopt, Instance.costOn_univ]
      linarith
    · rw [hBopt]
      linarith

/-- **The nuanced local-search bound** ([BCFGJPSSV26b, Theorem 3.8]). -/
theorem costF_S_le_PsiLS (H : Hyp X) : X.I.costF X.S ≤ Q.PsiLS + 150 * X.ε * X.opt := by
  obtain ⟨B, μA, μB, D₀, hA, hB, hsize, hcf, hcost, hX⟩ := Q.exists_nice_maps H
  have hS : IsALO X.I (24 * X.P.N) (1 / (X.P.N * X.I.k)) X.S := H.alo
  have h := refined_ls H.valid (by have := X.P.hN; omega) hS hA hB hsize hcf
  have hε : (10 : ℝ) / X.P.N = 10 * X.ε := by
    rw [Ctx.ε, Prm.eps]
    ring
  rw [hε] at h
  have hopt : 0 ≤ X.opt := H.opt_pos.le
  have hεpos := H.eps_pos
  nlinarith

end Partition

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.Partition.costF_S_le_PsiLS := @BCFGJPSSV26.Stable.Partition.costF_S_le_PsiLS
