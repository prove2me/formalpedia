-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.Run.embed_feasible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:02:42.032326+00:00
-- url     : https://prove2.me/submissions/52fb2e1a-f9f6-420e-8ff1-6bfcc16b51e0

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Trace
public import Definitions.Def_BCFGJPSSV26_Greedy_FRP
public import Definitions.Def_BCFGJPSSV26_Greedy_Embed
import all Definitions.Def_BCFGJPSSV26_Greedy_Embed
public import Theorems.Thm_BCFGJPSSV26_Greedy_Run_Zv_ge_third
public import Theorems.Thm_BCFGJPSSV26_Greedy_Run_noOver_post
public import Theorems.Thm_BCFGJPSSV26_Greedy_Run_noOver_pre
public import Theorems.Thm_BCFGJPSSV26_Greedy_Run_rstar_nonneg

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

namespace Embed

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

end Embed

namespace Run

variable {n m : ℕ} (R : Run n m)

variable (Dg : Finset (Fin n))

variable {Dg}

variable (hne : Dg.Nonempty)
include hne

section

variable {istar : Fin m}

theorem rstar_nonneg_of_kf_le (hF : R.Freezing hne istar) {k : R.DgT Dg} (hk : R.kf hne ≤ k)
    (j : R.DgT Dg) : 0 ≤ R.rstar hne istar j k := by
  rw [R.rstar_of_kf_le hne hF hk]
  split_ifs with h
  · have := R.Zv_ge_third hne hF j h
    have := R.θl_pos hne
    linarith
  · exact le_min (R.Xv_nonneg _ _) ((R.X.d_nonneg _ _).trans (le_max_right _ _))

end

variable {istar : Fin m} (hD : ∀ j ∈ Dg, ρ * R.X.d j istar ≤ R.αs j)
include hD

/-- **[BCFGJPSSV26a, Lemma E.13]**: the facility constraints. -/
theorem fr_facility (k : R.DgT Dg) :
    (∑ j ∈ univ.filter (· < k), bid (R.rstar hne istar j k) (R.X.d j.val istar)) +
      (∑ j ∈ univ.filter (k ≤ ·), bid (R.rstar hne istar k k) (R.X.d j.val istar)) ≤ R.f := by
  rw [R.rstar_diag hne hD k]
  have hs : R.σ k.val < R.len := R.σ_lt _
  rcases hkind : (R.step (R.σ k.val)).kind with a | _
  · by_cases hA : R.IsOp2 (R.σ k.val) a ∧ R.θs (R.σ k.val) < R.αs k.val
    · exact R.facility_op2 hne hD k hA.1 hA.2
    -- `α*_k = θ`: no overbidding before the step
    have hαk : R.αs k.val = R.θs (R.σ k.val) := by
      by_cases h12 : typ1 (R.step (R.σ k.val)).seq = true ∨ a.free = true
      · exact R.emb_αs_of_op_θ rfl hkind h12
      · have hop := R.emb_isOp2_of hkind h12
        exact le_antisymm (not_lt.1 fun h ↦ hA ⟨hop, h⟩) (R.θs_le_αs _)
    have hnot : ¬ (R.Freezing hne istar ∧ (R.kf hne : WithTop (R.DgT Dg)) ≤ k) := by
      rintro ⟨hF, hk⟩
      obtain ⟨hσ, hα⟩ := R.of_kf_le hne (R.freezing_gt hne hF) (WithTop.coe_le_coe.1 hk)
      unfold θl at hα
      rw [← hσ, hαk] at hα
      exact lt_irrefl _ hα
    refine (R.facility_le_sum hne k
      (fun j ↦ bid (mval R.P (R.θs (R.σ k.val)) (R.Dpre (R.σ k.val)) j) (R.X.d j istar))
      (fun j ↦ bid_nonneg _ _) (fun j hjk ↦ ?_) (fun j hkj ↦ ?_)).trans (R.noOver_pre hs istar)
    · rw [R.rstar_coe_of_not hne hnot, r_eq, time_coe]
      refine bid_mono_left ?_ _
      rcases (R.emb_σ_le_of_le hjk.le).lt_or_eq with h | h
      · rw [R.emb_Xv_of_lt h]
        exact le_min (R.emb_inact_before h hs) le_rfl
      · rw [show R.Xv j.val (R.σ k.val) = R.αs j.val from h ▸ R.emb_Xv_self _]
        have h1 := R.αs_le_Dpre j.val
        rw [h] at h1
        exact le_min (hαk ▸ R.emb_αs_le_of_le hjk.le h) h1
    · rw [hαk]
      exact bid_mono_left (le_min le_rfl (R.emb_active_of_le (R.emb_σ_le_of_le hkj)).le) _
  · -- a raise: no overbidding after the step
    have hαk : R.αs k.val = (1 - R.P.δ) * R.Dpre (R.σ k.val) k.val := R.emb_αs_of_raise rfl hkind
    have hD1 : R.Dpre (R.σ k.val + 1) = R.Dpre (R.σ k.val) := R.emb_Dpre_succ_raise hs hkind
    have hnot : ¬ (R.Freezing hne istar ∧ (R.kf hne : WithTop (R.DgT Dg)) ≤ k) := by
      rintro ⟨hF, hk⟩
      obtain ⟨hσ, -⟩ := R.of_kf_le hne (R.freezing_gt hne hF) (WithTop.coe_le_coe.1 hk)
      obtain ⟨a, hop, -⟩ := hF
      have h := hop.1
      rw [← hσ, hkind] at h
      cases h
    have hpost := R.noOver_post hs
    rw [hD1] at hpost
    have hin : ∀ j : R.DgT Dg, R.σ j.val = R.σ k.val →
        (1 - R.P.δ) * R.Dpre (R.σ k.val) j.val ≤ R.θpost (R.σ k.val) := fun j h ↦ by
      have h1 := R.inact_σ j.val
      unfold Inact at h1
      rw [h, hD1] at h1
      exact h1
    refine (R.facility_le_sum hne k
      (fun j ↦ bid (mval R.P (R.θpost (R.σ k.val)) (R.Dpre (R.σ k.val)) j) (R.X.d j istar))
      (fun j ↦ bid_nonneg _ _) (fun j hjk ↦ ?_) (fun j hkj ↦ ?_)).trans (hpost istar)
    · rw [R.rstar_coe_of_not hne hnot, r_eq, time_coe]
      refine bid_mono_left ?_ _
      rcases (R.emb_σ_le_of_le hjk.le).lt_or_eq with h | h
      · rw [R.emb_Xv_of_lt h]
        exact le_min ((R.emb_inact_before h hs).trans (R.emb_θs_le_θpost _)) le_rfl
      · rw [show R.Xv j.val (R.σ k.val) = R.αs j.val from h ▸ R.emb_Xv_self _,
          R.emb_αs_of_raise h hkind]
        exact le_min (hin j h) le_rfl
    · rw [hαk]
      refine bid_mono_left (le_min (hin k rfl) ?_) _
      rcases (R.emb_σ_le_of_le hkj).lt_or_eq with h | h
      · have h1 := R.not_inact_of_lt h
        unfold Inact at h1
        push Not at h1
        rw [hD1] at h1
        have := hin k rfl
        linarith
      · have := R.emb_αs_le_of_le hkj h
        rw [hαk, R.emb_αs_of_raise h.symm hkind] at this
        exact this

set_option linter.unusedSectionVars false in
/-- **[BCFGJPSSV26a, Lemma E.14]**: `r⋆` is antitone in time. -/
theorem fr_mono (j k : R.DgT Dg) (hjk : j ≤ k) :
    R.rstar hne istar j (FRP.nxt k) ≤ R.rstar hne istar j k := by
  have hσ := R.emb_σ_le_of_le hjk
  have hkn : (k : WithTop (R.DgT Dg)) < FRP.nxt k := Embed.coe_lt_nxt k
  have ht : R.σ k.val ≤ R.time (FRP.nxt k) := R.time_mono hkn.le
  by_cases hF : R.Freezing hne istar
  · by_cases hk : R.kf hne ≤ k
    · revert hkn ht
      induction FRP.nxt k using WithTop.recTopCoe with
      | top =>
        intro _ _
        rw [R.rstar_top_of hne hF]
        exact R.rstar_nonneg_of_kf_le hne hF hk j
      | coe k' =>
        intro hkn _
        have hk' : R.kf hne ≤ k' := hk.trans (WithTop.coe_lt_coe.1 hkn).le
        rw [R.rstar_of_kf_le hne hF hk', R.rstar_of_kf_le hne hF hk]
    · rw [R.rstar_coe_of_not hne (fun h' ↦ hk (WithTop.coe_le_coe.1 h'.2))]
      refine (R.rstar_le_r hne j _).trans ?_
      rw [r_eq, r_eq, time_coe]
      exact R.emb_Xv_le_of_le hσ ht (R.time_le_len _)
  · rw [R.rstar_of_not_freezing hne hF, R.rstar_of_not_freezing hne hF, r_eq, r_eq, time_coe]
    exact R.emb_Xv_le_of_le hσ ht (R.time_le_len _)

/-- **[BCFGJPSSV26a, Lemma E.16]**. -/
theorem fr_metric (j l : R.DgT Dg) (k : WithTop (R.DgT Dg)) (hj : (j : WithTop (R.DgT Dg)) < k)
    (hl : (l : WithTop (R.DgT Dg)) < k) :
    R.rstar hne istar j k ≤ R.rstar hne istar l k + R.X.d l.val istar + R.X.d j.val istar := by
  have hC := R.X.dC_le j.val l.val istar
  have hdj := R.X.d_nonneg j.val istar
  have hdl := R.X.d_nonneg l.val istar
  have hσj := R.σ_le_time hj.le
  have hσl := R.σ_le_time hl.le
  have hnn := R.rstar_nonneg hne hD l k
  by_cases hF : R.Freezing hne istar
  · induction k using WithTop.recTopCoe with
    | top =>
      rw [R.rstar_top_of hne hF, R.rstar_top_of hne hF]
      linarith
    | coe k =>
      by_cases hk : R.kf hne ≤ k
      · obtain ⟨a, hop, -⟩ := id hF
        have hs := R.σ_lt (R.kl hne).val
        have hm := R.emb_Zv_metric hop hs (R.σ_le_σkl hne j) (R.σ_le_σkl hne l)
        have hZl := R.rstar_ge_Zv hne hF hk l
        have hmax := R.rstar_le_max hne hF hk j
        rcases le_max_iff.1 hmax with h1 | h1
        · linarith
        · linarith
      · have hnot : ¬ (R.Freezing hne istar ∧ (R.kf hne : WithTop (R.DgT Dg)) ≤ k) :=
          fun h' ↦ hk (WithTop.coe_le_coe.1 h'.2)
        rw [R.rstar_coe_of_not hne hnot, R.rstar_coe_of_not hne hnot, r_eq, r_eq]
        have := R.emb_Xv_metric hσj hσl
        linarith
  · rw [R.rstar_of_not_freezing hne hF, R.rstar_of_not_freezing hne hF, r_eq, r_eq]
    have := R.emb_Xv_metric hσj hσl
    linarith

/-- **The embedding is feasible** for the factor-revealing program, except for the
normalization. -/
theorem embed_feasible :
    FRP.FeasibleOn (R.rstar hne istar) (fun j ↦ R.X.d j.val istar) R.f where
  mono := R.fr_mono hne hD
  tri := R.fr_triangle hne hD
  metric := R.fr_metric hne hD
  facility := R.fr_facility hne hD
  f_nonneg := by
    have := R.fpos
    have := R.good.η_nonneg
    have : (0 : ℚ) ≤ n * R.P.η := by positivity
    linarith
  d_nonneg := fun j ↦ R.X.d_nonneg _ _
  r_nonneg := R.rstar_nonneg hne hD

end Run

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.Run.embed_feasible := @BCFGJPSSV26.Greedy.Run.embed_feasible
