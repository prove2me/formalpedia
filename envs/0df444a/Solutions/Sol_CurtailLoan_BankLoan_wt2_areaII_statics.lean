-- Prove2me | solution 1 for CurtailLoan.BankLoan.wt2_areaII_statics
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T13:49:49.229278+00:00
-- url     : https://prove2.me/submissions/fc4ca6c0-c9b4-4351-b7ce-f12f4d646503
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CurtailLoan_BankLoan_Model
import Theorems.Thm_CurtailLoan_BankLoan_lemma_A7_moreover
import Theorems.Thm_CurtailLoan_BankLoan_proposition_A8_moreover
import Theorems.Thm_CurtailLoan_BankLoan_standing_rootsDefined

open CurtailLoan.BankLoan Set

lemma cl_wu1_nonneg (Q : Params) : 0 ≤ wu1 Q :=
  Real.sInf_nonneg (fun _ hx => hx.1.1.le)

lemma cl_interval_mono (Q₁ Q₂ : Params) (hF : Finv Q₁ = Finv Q₂) (hL : L Q₂ ≤ L Q₁)
    (w : ℝ) (hw : w ∈ Ioo (wu1 Q₁) (wu2 Q₁)) : w ∈ Ioo (wu1 Q₂) (wu2 Q₂) := by
  set A₁ : Set ℝ := {w : ℝ | w ∈ Ioo (0 : ℝ) 1 ∧ L Q₁ < w * Finv Q₁ w} with hA₁
  set A₂ : Set ℝ := {w : ℝ | w ∈ Ioo (0 : ℝ) 1 ∧ L Q₂ < w * Finv Q₂ w} with hA₂
  have sub : A₁ ⊆ A₂ := fun x hx => ⟨hx.1, by rw [← hF]; exact lt_of_le_of_lt hL hx.2⟩
  have hne : A₁.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have h1 : wu1 Q₁ = 0 := by unfold wu1; rw [← hA₁, h, Real.sInf_empty]
    have h2 : wu2 Q₁ = 0 := by unfold wu2; rw [← hA₁, h, Real.sSup_empty]
    have := hw.1; have := hw.2; linarith
  have hbb : BddBelow A₂ := ⟨0, fun x hx => hx.1.1.le⟩
  have hba : BddAbove A₂ := ⟨1, fun x hx => hx.1.2.le⟩
  have e1 : wu1 Q₂ ≤ wu1 Q₁ := csInf_le_csInf hbb hne sub
  have e2 : wu2 Q₁ ≤ wu2 Q₂ := csSup_le_csSup hba hne sub
  exact ⟨lt_of_le_of_lt e1 hw.1, lt_of_lt_of_le hw.2 e2⟩

lemma cl_wt2_mono (Q₁ Q₂ : Params)
    (hsub : ∀ w, w ∈ Ioo (wu1 Q₁) (wu2 Q₁) → Q₁.t ≤ tk Q₁ w →
      w ∈ Ioo (wu1 Q₂) (wu2 Q₂) ∧ Q₂.t ≤ tk Q₂ w) :
    wt2 Q₁ ≤ wt2 Q₂ := by
  set T₁ : Set ℝ := {w : ℝ | w ∈ Ioo (wu1 Q₁) (wu2 Q₁) ∧ Q₁.t ≤ tk Q₁ w} with hT₁
  set T₂ : Set ℝ := {w : ℝ | w ∈ Ioo (wu1 Q₂) (wu2 Q₂) ∧ Q₂.t ≤ tk Q₂ w} with hT₂
  have hnn : 0 ≤ wt2 Q₂ := by
    unfold wt2
    exact Real.sSup_nonneg (fun x hx => le_trans (cl_wu1_nonneg Q₂) hx.1.1.le)
  rcases T₁.eq_empty_or_nonempty with h | h
  · have : wt2 Q₁ = 0 := by unfold wt2; rw [← hT₁, h, Real.sSup_empty]
    rw [this]; exact hnn
  · have hba : BddAbove T₂ := ⟨wu2 Q₂, fun x hx => hx.1.2.le⟩
    exact csSup_le_csSup hba h (fun x hx => hsub x hx.1 hx.2)

lemma cl_tk_le_wmin (Q : Params)
    (h3 : wu1 Q < wmin Q ∧ wmin Q < what Q ∧ StrictMonoOn (tk Q) (Ioc (wu1 Q) (wmin Q)) ∧
      StrictAntiOn (tk Q) (Ico (wmin Q) (wu2 Q)))
    (w : ℝ) (hw : w ∈ Ioo (wu1 Q) (wu2 Q)) : tk Q w ≤ tk Q (wmin Q) := by
  rcases le_or_gt w (wmin Q) with h | h
  · exact h3.2.2.1.monotoneOn ⟨hw.1, h⟩ ⟨h3.1, le_rfl⟩ h
  · exact h3.2.2.2.antitoneOn ⟨le_rfl, lt_trans h hw.2⟩ ⟨h.le, hw.2⟩ h.le

lemma cl_Finv_one (Q : Params) : Finv Q 1 ≤ 0 := by
  unfold Finv
  apply csInf_le ⟨0, fun x hx => hx.1⟩
  refine ⟨le_rfl, ?_⟩
  unfold Fbar
  have := ProbabilityTheory.cdf_nonneg Q.D 0
  linarith

lemma cl_wmin_mem (Q : Params) (hG : Global Q) (hD : RootsDefined Q)
    (h3 : wu1 Q < wmin Q ∧ wmin Q < what Q ∧ StrictMonoOn (tk Q) (Ioc (wu1 Q) (wmin Q)) ∧
      StrictAntiOn (tk Q) (Ico (wmin Q) (wu2 Q))) :
    wmin Q ∈ Ioo (wu1 Q) (wu2 Q) := by
  refine ⟨h3.1, lt_of_lt_of_le h3.2.1 ?_⟩
  have hLpos : 0 < L Q := by
    obtain ⟨-, -, hl, -, -, -, htu, -, -⟩ := hG
    unfold L; linarith
  have hpos : 0 < what Q := lt_of_le_of_lt (cl_wu1_nonneg Q) (lt_trans h3.1 h3.2.1)
  have hle1 : what Q ≤ 1 := by
    unfold what
    exact Real.sSup_le (fun x hx => hx.1.2.le) zero_le_one
  have hlt1 : what Q < 1 := by
    rcases hle1.lt_or_eq with h | h
    · exact h
    · exfalso
      have hD' : L Q < what Q * Finv Q (what Q) := hD
      rw [h, one_mul] at hD'
      have := cl_Finv_one Q
      linarith
  unfold wu2
  exact le_csSup ⟨1, fun x hx => hx.1.2.le⟩ ⟨⟨hpos, hlt1⟩, hD⟩

lemma cl_tkII_le (Q : Params)
    (h3 : wu1 Q < wmin Q ∧ wmin Q < what Q ∧ StrictMonoOn (tk Q) (Ioc (wu1 Q) (wmin Q)) ∧
      StrictAntiOn (tk Q) (Ico (wmin Q) (wu2 Q))) :
    tk Q (wII Q) ≤ tk Q (wmin Q) := by
  unfold wII
  rcases le_total (ws Q) (wmin Q) with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h]
    rcases h.lt_or_eq with h' | h'
    · set S : Set ℝ := {w : ℝ | w ∈ Ioo (wu1 Q) (wu2 Q) ∧
          (wu2 Q - Q.c) * Finv Q (wu2 Q) ≤ (w - Q.c) * wsOrder Q w} with hS
      have hws : ws Q = sInf S := rfl
      rcases S.eq_empty_or_nonempty with he | ⟨e, he⟩
      · rw [hws, he, Real.sInf_empty] at h'
        have := cl_wu1_nonneg Q
        linarith [h3.1]
      · have hle : ws Q ≤ e := by
          rw [hws]; exact csInf_le ⟨wu1 Q, fun x hx => hx.1.1.le⟩ he
        have hmem : ws Q ∈ Ioo (wu1 Q) (wu2 Q) :=
          ⟨lt_trans h3.1 h', lt_of_le_of_lt hle he.1.2⟩
        exact cl_tk_le_wmin Q h3 _ hmem
    · rw [← h']

theorem solution (P : Params) (hR : P.Regular) :
    (∀ u₁ u₂ : ℝ, u₁ < u₂ →
      (∀ x ∈ Set.Icc u₁ u₂, Standing (P.withU x) ∧ AreaII (P.withU x)) →
      wt2 (P.withU u₂) < wt2 (P.withU u₁)) ∧
    (∀ τ₁ τ₂ : ℝ, τ₁ < τ₂ →
      (∀ x ∈ Set.Icc τ₁ τ₂, Standing (P.withTau x) ∧ AreaII (P.withTau x)) →
      wt2 (P.withTau τ₁) < wt2 (P.withTau τ₂)) := by
  obtain ⟨A7u, A7tau, -⟩ := lemma_A7_moreover P hR
  obtain ⟨-, A8u, -, A8tau, -⟩ := proposition_A8_moreover P hR
  refine ⟨?_, ?_⟩
  · intro u₁ u₂ hu hseg
    have hRx : ∀ x : ℝ, (P.withU x).Regular := fun _ => hR
    have hGD : ∀ x ∈ Icc u₁ u₂, Global (P.withU x) ∧ RootsDefined (P.withU x) :=
      fun x hx => ⟨(hseg x hx).1.1, standing_rootsDefined _ (hRx x) (hseg x hx).1⟩
    have h3 : ∀ x ∈ Icc u₁ u₂, _ := fun x hx =>
      (lemma_A7_moreover (P.withU x) (hRx x)).2.2 (hGD x hx).1 (hGD x hx).2
    set m : ℝ := (u₁ + u₂) / 2 with hm
    have hm1 : u₁ < m := by rw [hm]; linarith
    have hm2 : m < u₂ := by rw [hm]; linarith
    have hu₂ : u₂ ∈ Icc u₁ u₂ := ⟨hu.le, le_rfl⟩
    have key : ∀ x ∈ Icc u₁ m, Standing (P.withU x) ∧
        (P.withU x).t < tk (P.withU x) (wmin (P.withU x)) := by
      intro x hx
      have hxI : x ∈ Icc u₁ u₂ := ⟨hx.1, by linarith [hx.2]⟩
      refine ⟨(hseg x hxI).1, ?_⟩
      have hmem2 := cl_wmin_mem _ (hGD u₂ hu₂).1 (hGD u₂ hu₂).2 (h3 u₂ hu₂)
      have hmemx : wmin (P.withU u₂) ∈ Ioo (wu1 (P.withU x)) (wu2 (P.withU x)) :=
        cl_interval_mono (P.withU u₂) (P.withU x) rfl (by show x + P.l - P.tau ≤ u₂ + P.l - P.tau; linarith [hx.2])
          _ hmem2
      have ht2 : (P.withU u₂).t ≤ tk (P.withU u₂) (wII (P.withU u₂)) := (hseg u₂ hu₂).2.2
      have ht2' := cl_tkII_le _ (h3 u₂ hu₂)
      have hA := A7u x u₂ (wmin (P.withU u₂)) (by linarith [hx.2])
        (fun y hy => hGD y ⟨le_trans hxI.1 hy.1, hy.2⟩) hmemx hmem2
      have hx3 := cl_tk_le_wmin _ (h3 x hxI) _ hmemx
      have e : (P.withU x).t = (P.withU u₂).t := rfl
      rw [e]; linarith
    have h1 : wt2 (P.withU m) < wt2 (P.withU u₁) := A8u u₁ m hm1 key
    have h2 : wt2 (P.withU u₂) ≤ wt2 (P.withU m) := by
      apply cl_wt2_mono
      intro w hw ht
      have hwm : w ∈ Ioo (wu1 (P.withU m)) (wu2 (P.withU m)) :=
        cl_interval_mono (P.withU u₂) (P.withU m) rfl (by show m + P.l - P.tau ≤ u₂ + P.l - P.tau; linarith) _ hw
      refine ⟨hwm, ?_⟩
      have hA := A7u m u₂ w hm2
        (fun y hy => hGD y ⟨by linarith [hy.1], hy.2⟩) hwm hw
      have e : (P.withU m).t = (P.withU u₂).t := rfl
      rw [e]; linarith
    linarith
  · intro τ₁ τ₂ hτ hseg
    have hRx : ∀ x : ℝ, (P.withTau x).Regular := fun _ => hR
    have hGD : ∀ x ∈ Icc τ₁ τ₂, Global (P.withTau x) ∧ RootsDefined (P.withTau x) :=
      fun x hx => ⟨(hseg x hx).1.1, standing_rootsDefined _ (hRx x) (hseg x hx).1⟩
    have h3 : ∀ x ∈ Icc τ₁ τ₂, _ := fun x hx =>
      (lemma_A7_moreover (P.withTau x) (hRx x)).2.2 (hGD x hx).1 (hGD x hx).2
    set m : ℝ := (τ₁ + τ₂) / 2 with hm
    have hm1 : τ₁ < m := by rw [hm]; linarith
    have hm2 : m < τ₂ := by rw [hm]; linarith
    have hτ₁ : τ₁ ∈ Icc τ₁ τ₂ := ⟨le_rfl, hτ.le⟩
    have key : ∀ x ∈ Icc m τ₂, Standing (P.withTau x) ∧
        (P.withTau x).t < tk (P.withTau x) (wmin (P.withTau x)) := by
      intro x hx
      have hxI : x ∈ Icc τ₁ τ₂ := ⟨by linarith [hx.1], hx.2⟩
      refine ⟨(hseg x hxI).1, ?_⟩
      have hmem1 := cl_wmin_mem _ (hGD τ₁ hτ₁).1 (hGD τ₁ hτ₁).2 (h3 τ₁ hτ₁)
      have hmemx : wmin (P.withTau τ₁) ∈ Ioo (wu1 (P.withTau x)) (wu2 (P.withTau x)) :=
        cl_interval_mono (P.withTau τ₁) (P.withTau x) rfl
          (by show P.u + P.l - x ≤ P.u + P.l - τ₁; linarith [hx.1]) _ hmem1
      have ht1 : (P.withTau τ₁).t ≤ tk (P.withTau τ₁) (wII (P.withTau τ₁)) := (hseg τ₁ hτ₁).2.2
      have ht1' := cl_tkII_le _ (h3 τ₁ hτ₁)
      have hA := A7tau τ₁ x (wmin (P.withTau τ₁)) (by linarith [hx.1])
        (fun y hy => hGD y ⟨hy.1, le_trans hy.2 hxI.2⟩) hmem1 hmemx
      have hx3 := cl_tk_le_wmin _ (h3 x hxI) _ hmemx
      have e : (P.withTau x).t = (P.withTau τ₁).t := rfl
      rw [e]; linarith
    have h1 : wt2 (P.withTau m) < wt2 (P.withTau τ₂) := A8tau m τ₂ hm2 key
    have h2 : wt2 (P.withTau τ₁) ≤ wt2 (P.withTau m) := by
      apply cl_wt2_mono
      intro w hw ht
      have hwm : w ∈ Ioo (wu1 (P.withTau m)) (wu2 (P.withTau m)) :=
        cl_interval_mono (P.withTau τ₁) (P.withTau m) rfl (by show P.u + P.l - m ≤ P.u + P.l - τ₁; linarith) _ hw
      refine ⟨hwm, ?_⟩
      have hA := A7tau τ₁ m w hm1
        (fun y hy => hGD y ⟨hy.1, by linarith [hy.2]⟩) hw hwm
      have e : (P.withTau m).t = (P.withTau τ₁).t := rfl
      rw [e]; linarith
    linarith
