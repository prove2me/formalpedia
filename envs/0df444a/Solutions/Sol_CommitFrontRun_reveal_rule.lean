-- Prove2me | solution 1 for CommitFrontRun.reveal_rule
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:59:44.824436+00:00
-- url     : https://prove2.me/submissions/00e624e1-6666-401b-81dd-ac23885355a6

import Mathlib
import Definitions.Def_CommitFrontRun_Model_IsEquilibrium

namespace Aux_CommitFrontRun_rr
open CommitFrontRun

variable {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Msg] [DecidableEq Msg] [Nonempty Msg]

def dev (M : Model S Msg) (B : StratB Msg) (s : S) (σ : Msg) (v : ℝ)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) : StratB Msg where
  μ := B.μ
  μ_nonneg := B.μ_nonneg
  μ_sum := B.μ_sum
  fire := fun σ' m => if σ' = σ ∧ m = M.σA s then v else B.fire σ' m
  fire_mem := by
    intro σ' m
    by_cases h : σ' = σ ∧ m = M.σA s
    · simp only [h, and_self, if_true]; exact hv
    · simp only [h, if_false]; exact B.fire_mem σ' m

theorem dev_payoff (M : Model S Msg) (A : StratA S) (B : StratB Msg) (s : S) (σ : Msg) (v : ℝ)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    M.payoffB A (dev M B s σ v hv) = M.payoffB A B +
      M.p s * A.commit s * (M.β * A.reveal s * (B.μ (BCommit.guess σ) *
        (v - B.fire σ (M.σA s)) * (M.q * M.PtB σ (M.σA s) s - M.f))) := by
  unfold Model.payoffB
  have hterm : ∀ s' : S,
      M.p s' * A.commit s' *
        (-M.c * (1 - (dev M B s σ v hv).μ BCommit.none) +
          M.β * A.reveal s' * ∑ σ', (dev M B s σ v hv).μ (BCommit.guess σ') *
            (dev M B s σ v hv).fire σ' (M.σA s') * (M.q * M.PtB σ' (M.σA s') s' - M.f)) =
      M.p s' * A.commit s' *
        (-M.c * (1 - B.μ BCommit.none) +
          M.β * A.reveal s' * ∑ σ', B.μ (BCommit.guess σ') * B.fire σ' (M.σA s') *
            (M.q * M.PtB σ' (M.σA s') s' - M.f)) +
      (if s' = s then M.p s * A.commit s * (M.β * A.reveal s * (B.μ (BCommit.guess σ) *
        (v - B.fire σ (M.σA s)) * (M.q * M.PtB σ (M.σA s) s - M.f))) else 0) := by
    intro s'
    by_cases hs : s' = s
    · subst hs
      have hin : ∑ σ', (dev M B s' σ v hv).μ (BCommit.guess σ') *
            (dev M B s' σ v hv).fire σ' (M.σA s') * (M.q * M.PtB σ' (M.σA s') s' - M.f) =
          ∑ σ', B.μ (BCommit.guess σ') * B.fire σ' (M.σA s') *
            (M.q * M.PtB σ' (M.σA s') s' - M.f) +
          B.μ (BCommit.guess σ) * (v - B.fire σ (M.σA s')) *
            (M.q * M.PtB σ (M.σA s') s' - M.f) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ σ),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ σ)]
        have hrest : ∑ σ' ∈ Finset.univ.erase σ, (dev M B s' σ v hv).μ (BCommit.guess σ') *
            (dev M B s' σ v hv).fire σ' (M.σA s') * (M.q * M.PtB σ' (M.σA s') s' - M.f) =
            ∑ σ' ∈ Finset.univ.erase σ, B.μ (BCommit.guess σ') * B.fire σ' (M.σA s') *
            (M.q * M.PtB σ' (M.σA s') s' - M.f) := by
          apply Finset.sum_congr rfl
          intro σ' hσ'
          have hne : σ' ≠ σ := Finset.ne_of_mem_erase hσ'
          simp [dev, hne]
        rw [hrest]
        simp only [dev, and_self, if_true]
        ring
      rw [hin, if_pos rfl]
      simp only [dev]
      ring
    · have hne : M.σA s' ≠ M.σA s := fun h => hs (M.σA_injective h)
      simp [dev, hne, hs]
  rw [Finset.sum_congr rfl (fun s' _ => hterm s'), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

end Aux_CommitFrontRun_rr

open CommitFrontRun Aux_CommitFrontRun_rr in
theorem solution {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Msg] [DecidableEq Msg] [Nonempty Msg] (M : Model S Msg)
    (A : StratA S) (B : StratB Msg) (hE : M.IsEquilibrium A B) (s : S) (σ : Msg)
    (hpath : 0 < M.p s * A.commit s * A.reveal s * B.μ (BCommit.guess σ)) :
    (M.f < M.q * M.PtB σ (M.σA s) s → B.fire σ (M.σA s) = 1) ∧
      (M.q * M.PtB σ (M.σA s) s < M.f → B.fire σ (M.σA s) = 0) := by
  have hp0 := M.p_nonneg s
  have hc0 := (A.commit_mem s).1
  have hr0 := (A.reveal_mem s).1
  have hm0 := B.μ_nonneg (BCommit.guess σ)
  have hpc : 0 < M.p s * A.commit s := by
    rcases (mul_nonneg hp0 hc0).eq_or_lt with h | h
    · rw [← h] at hpath; simp at hpath
    · exact h
  have hr : 0 < A.reveal s := by
    rcases hr0.eq_or_lt with h | h
    · rw [← h] at hpath; simp at hpath
    · exact h
  have hm : 0 < B.μ (BCommit.guess σ) := by
    rcases hm0.eq_or_lt with h | h
    · rw [← h] at hpath; simp at hpath
    · exact h
  have hβ : 0 < M.β := by
    rcases M.β_nonneg.eq_or_lt with h | h
    · exfalso
      let A' : StratA S := ⟨fun _ => 0, fun _ => 0, fun _ => ⟨le_refl _, zero_le_one⟩,
        fun _ => ⟨le_refl _, zero_le_one⟩⟩
      have h1 := hE.1 A'
      have h2 : M.payoffA A' B = 0 := by
        simp [Model.payoffA, Model.stateValueA, A']
      have h3 : M.payoffA A B < 0 := by
        unfold Model.payoffA Model.stateValueA
        rw [← h]
        have : ∑ s', M.p s' * (A.commit s' * (-M.c + 0 * (A.reveal s' * (-M.c +
            (1 - M.q * B.threat (M.σA s')) * M.PA s')))) =
            ∑ s', -(M.c * (M.p s' * A.commit s')) := by
          apply Finset.sum_congr rfl; intro s' _; ring
        rw [this, Finset.sum_neg_distrib, neg_neg_iff_pos]
        have hnn : ∀ s' ∈ Finset.univ, 0 ≤ M.c * (M.p s' * A.commit s') := fun s' _ =>
          mul_nonneg M.c_pos.le (mul_nonneg (M.p_nonneg s') (A.commit_mem s').1)
        calc (0 : ℝ) < M.c * (M.p s * A.commit s) := mul_pos M.c_pos hpc
          _ ≤ _ := Finset.single_le_sum hnn (Finset.mem_univ s)
      linarith
    · exact h
  have hfm := B.fire_mem σ (M.σA s)
  constructor
  · intro hlt
    have hd := (dev_payoff M A B s σ 1 ⟨zero_le_one, le_refl _⟩).symm.trans_le
      (hE.2 (dev M B s σ 1 ⟨zero_le_one, le_refl _⟩))
    have hK : 0 < M.p s * A.commit s * (M.β * A.reveal s * (B.μ (BCommit.guess σ) *
        (M.q * M.PtB σ (M.σA s) s - M.f))) := by
      have : 0 < M.q * M.PtB σ (M.σA s) s - M.f := by linarith
      positivity
    have : M.p s * A.commit s * (M.β * A.reveal s * (B.μ (BCommit.guess σ) *
        (1 - B.fire σ (M.σA s)) * (M.q * M.PtB σ (M.σA s) s - M.f))) =
        (M.p s * A.commit s * (M.β * A.reveal s * (B.μ (BCommit.guess σ) *
        (M.q * M.PtB σ (M.σA s) s - M.f)))) * (1 - B.fire σ (M.σA s)) := by ring
    rw [this] at hd
    have : 1 - B.fire σ (M.σA s) ≤ 0 := by
      by_contra hc; push_neg at hc
      have := mul_pos hK hc
      linarith
    linarith [hfm.2]
  · intro hlt
    have hd := (dev_payoff M A B s σ 0 ⟨le_refl _, zero_le_one⟩).symm.trans_le
      (hE.2 (dev M B s σ 0 ⟨le_refl _, zero_le_one⟩))
    have hK : 0 < M.p s * A.commit s * (M.β * A.reveal s * (B.μ (BCommit.guess σ) *
        (M.f - M.q * M.PtB σ (M.σA s) s))) := by
      have : 0 < M.f - M.q * M.PtB σ (M.σA s) s := by linarith
      positivity
    have : M.p s * A.commit s * (M.β * A.reveal s * (B.μ (BCommit.guess σ) *
        (0 - B.fire σ (M.σA s)) * (M.q * M.PtB σ (M.σA s) s - M.f))) =
        (M.p s * A.commit s * (M.β * A.reveal s * (B.μ (BCommit.guess σ) *
        (M.f - M.q * M.PtB σ (M.σA s) s)))) * B.fire σ (M.σA s) := by ring
    rw [this] at hd
    have : B.fire σ (M.σA s) ≤ 0 := by
      by_contra hc; push_neg at hc
      have := mul_pos hK hc
      linarith
    linarith [hfm.1]
