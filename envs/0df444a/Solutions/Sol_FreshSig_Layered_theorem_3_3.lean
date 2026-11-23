-- Prove2me | solution 1 for FreshSig.Layered.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:53:39.203134+00:00
-- url     : https://prove2.me/submissions/1e64db22-1563-49ee-aa8f-992c1eb22bc8

import Definitions.Def_FreshSig_Layered_Term
import Definitions.Def_FreshSig_Layered_Execution
import Definitions.Def_FreshSig_Layered_EpochScheme
import Definitions.Def_FreshSig_Layered_SigComp
import Theorems.Thm_FreshSig_Layered_lemma_3_1
import Theorems.Thm_FreshSig_Layered_lemma_3_2

open FreshSig.Layered

namespace Aux33

lemma posLT_trans {a b c : Pos} (hab : PosLT a b) (hbc : PosLT b c) : PosLT a c := by
  rcases hab with h1 | ⟨h1, h2⟩ <;> rcases hbc with h3 | ⟨h3, h4⟩
  · exact Or.inl (lt_trans h1 h3)
  · exact Or.inl (h3 ▸ h1)
  · exact Or.inl (h1 ▸ h3)
  · exact Or.inr ⟨h1.trans h3, lt_trans h2 h4⟩

lemma posLE_of_posLT {a b : Pos} (h : PosLT a b) : PosLE a b := Or.inl h

lemma posLT_of_posLT_of_posLE {a b c : Pos} (hab : PosLT a b) (hbc : PosLE b c) : PosLT a c := by
  rcases hbc with hbc | rfl
  · exact posLT_trans hab hbc
  · exact hab

lemma posLE_trans {a b c : Pos} (hab : PosLE a b) (hbc : PosLE b c) : PosLE a c := by
  rcases hab with hab | rfl
  · exact Or.inl (posLT_of_posLT_of_posLE hab hbc)
  · exact hbc

lemma posLT_trichotomy (a b : Pos) : PosLT a b ∨ a = b ∨ PosLT b a := by
  rcases lt_trichotomy a.1 b.1 with h1 | h1 | h1
  · exact Or.inl (Or.inl h1)
  · rcases lt_trichotomy a.2 b.2 with h2 | h2 | h2
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · exact Or.inr (Or.inl (Prod.ext h1 h2))
    · exact Or.inr (Or.inr (Or.inr ⟨h1.symm, h2⟩))
  · exact Or.inr (Or.inr (Or.inl h1))

lemma posLE_fst {a b : Pos} (h : PosLE a b) : a.1 ≤ b.1 := by
  rcases h with (h1 | ⟨h1, _⟩) | rfl <;> omega

lemma correctAt_mono {tr : Execution} {τ₀ i : ℕ} {p q : Pos}
    (hq : CorrectAt tr τ₀ i q) (hτ : PosLE (τ₀, 0) p) (hpq : PosLE p q) :
    CorrectAt tr τ₀ i p :=
  ⟨hτ, fun p' h1 h2 => hq.2 p' h1 (posLE_trans h2 hpq)⟩

lemma correctAt_of_through {tr : Execution} {τ₀ i r : ℕ} {p : Pos}
    (hth : CorrectThrough tr τ₀ i r) (hτ : PosLE (τ₀, 0) p) (hpr : p.1 ≤ r) :
    CorrectAt tr τ₀ i p := by
  refine ⟨hτ, fun p' h1 h2 => hth p' ?_ ?_⟩
  · exact posLE_fst h1
  · exact le_trans (posLE_fst h2) hpr

lemma wf_posLT : WellFounded PosLT := by
  refine ⟨fun ⟨r, k⟩ => ?_⟩
  induction r using Nat.strongRecOn generalizing k with
  | ind r ihr =>
    induction k using Nat.strongRecOn with
    | ind k ihk =>
      refine Acc.intro (r, k) (fun ⟨r', k'⟩ h => ?_)
      rcases h with hr | ⟨rfl, hk⟩
      · exact ihr r' hr k'
      · exact ihk k' hk

lemma mem_prefixEvents_iff {tr : Execution} {p : Pos} {ev : Event} :
    ev ∈ prefixEvents tr p ↔ ∃ q : Pos, PosLT q p ∧ evAt tr q = some ev := by
  simp only [prefixEvents, List.mem_append, List.mem_flatMap, List.mem_range]
  constructor
  · rintro (⟨r, hr, hmem⟩ | hmem)
    · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
      exact ⟨(r, k), Or.inl hr, hk⟩
    · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
      rw [List.getElem?_take] at hk
      split_ifs at hk with hkp
      exact ⟨(p.1, k), Or.inr ⟨rfl, hkp⟩, hk⟩
  · rintro ⟨⟨r, k⟩, hr | ⟨rfl, hk⟩, hev⟩
    · exact Or.inl ⟨r, hr, List.mem_of_getElem? hev⟩
    · refine Or.inr (List.mem_iff_getElem?.mpr ⟨k, ?_⟩)
      rw [List.getElem?_take, if_pos hk]
      exact hev

lemma mem_record_iff {tr : Execution} {p : Pos} {t : Term} :
    t ∈ record tr p ↔ ∃ (q : Pos) (ev : Event), PosLT q p ∧ evAt tr q = some ev ∧ t ∈ ev.terms := by
  simp only [record, mem_prefixEvents_iff]
  constructor
  · rintro ⟨ev, ⟨q, hqp, hev⟩, ht⟩
    exact ⟨q, ev, hqp, hev, ht⟩
  · rintro ⟨q, ev, hqp, hev, ht⟩
    exact ⟨ev, ⟨q, hqp, hev⟩, ht⟩

lemma sub_dy_sig {n : ℕ} {K : Set Term} {t : Term} (hdy : DY n K t) {i : ℕ} {x : Term}
    (hocc : Occurs (Term.sig i x) t) : Term.sig i x ∈ FreshSig.Layered.Sub K := by
  induction hdy with
  | base ht => exact ⟨_, ht, hocc⟩
  | cst _ => cases hocc
  | pid _ => cases hocc
  | tup _ ih =>
    cases hocc with
    | tup ht hocc' => exact ih _ ht hocc'
  | proj _ ht ih => exact ih (Occurs.tup ht hocc)
  | sigId _ _ => cases hocc
  | sigMsg _ ih => exact ih (Occurs.sig _ hocc)
  | leaf _ ih =>
    cases hocc with
    | leaf hocc' => exact ih hocc'
  | root _ _ ih =>
    cases hocc with
    | root ht hocc' => exact ih _ ht hocc'
  | prf _ _ _ ih =>
    cases hocc with
    | prf ht hocc' => exact ih _ ht hocc'

lemma firstIssue_of_sub_record {n : ℕ} {tr : Execution} (hadm : Admissible n tr)
    {p : Pos} {i : ℕ} {x : Term} (hsub : Term.sig i x ∈ FreshSig.Layered.Sub (record tr p)) :
    ∃ e : Pos, FirstIssue tr (Term.sig i x) e ∧ PosLT e p ∧
      evAt tr e = some (Event.signCall i x) := by
  let S : Set Pos := {q | ∃ ev t, evAt tr q = some ev ∧ t ∈ ev.terms ∧ Occurs (Term.sig i x) t}
  obtain ⟨t₀, ht₀, hocc₀⟩ := hsub
  obtain ⟨q₀, ev₀, hq₀p, hev₀, ht₀m⟩ := mem_record_iff.mp ht₀
  have hne : S.Nonempty := ⟨q₀, ev₀, t₀, hev₀, ht₀m, hocc₀⟩
  let e := wf_posLT.min S hne
  have heS : e ∈ S := wf_posLT.min_mem S hne
  have hmin : ∀ q ∈ S, ¬ PosLT q e := fun q hq => wf_posLT.not_lt_min S hq
  have hep : PosLT e p := by
    rcases posLT_trichotomy e q₀ with h | rfl | h
    · exact posLT_trans h hq₀p
    · exact hq₀p
    · exact absurd h (hmin q₀ ⟨ev₀, t₀, hev₀, ht₀m, hocc₀⟩)
  obtain ⟨ev, t, hev, ht, hocc⟩ := heS
  have hnot_used : ∀ u ∈ ev.used, ¬ Occurs (Term.sig i x) u := by
    intro u hu hoccu
    have hdy := (hadm e ev hev).1 u hu
    obtain ⟨t', ht', hocct'⟩ := sub_dy_sig hdy hoccu
    obtain ⟨q', ev', hq'e, hev', ht'm⟩ := mem_record_iff.mp ht'
    exact hmin q' ⟨ev', t', hev', ht'm, hocct'⟩ hq'e
  have hcreated : t ∈ ev.created := by
    simp only [Event.terms, List.mem_append] at ht
    rcases ht with hu | hc
    · exact absurd hocc (hnot_used t hu)
    · exact hc
  have hev_eq : ev = Event.signCall i x := by
    cases ev with
    | gen a =>
      simp only [Event.created, List.mem_singleton] at hcreated
      subst hcreated; cases hocc
    | signCall i' x' =>
      simp only [Event.created, List.mem_singleton] at hcreated
      subst hcreated
      cases hocc with
      | refl => rfl
      | sig _ hocc' =>
        exact absurd hocc' (hnot_used x' (by simp [Event.used]))
    | extCall k' i' x' =>
      simp only [Event.created, List.mem_singleton] at hcreated
      subst hcreated
      cases hocc with
      | ext _ _ hocc' =>
        exact absurd hocc' (hnot_used x' (by simp [Event.used]))
    | handle _ | corrupt _ | nonceInv _ _ | nonceOut _ _ _ | commitInv _ _ _ _
    | commitOut _ _ _ _ _ _ | refreshOut _ _ _ _ | accept _ _ _ _ _ _ =>
      simp [Event.created] at hcreated
  subst hev_eq
  refine ⟨e, ⟨⟨Event.signCall i x, hev, by simp [Event.created]⟩, ?_⟩, hep, hev⟩
  intro p' hp'e ev' hev' hmem
  have ht' : Term.sig i x ∈ ev'.terms := by
    simp only [Event.terms, List.mem_append]
    exact Or.inr hmem
  exact hmin p' ⟨ev', Term.sig i x, hev', ht', Occurs.refl _⟩ hp'e

lemma obtained_posLE {tr : Execution} {τ₀ n : ℕ} {g : Term} {i : ℕ} {ν : Term}
    {L : ℕ → SigComp.LayerOut} :
    ∀ {ℓ : ℕ} {p : Pos}, SigComp.Obtained tr τ₀ n g i ν L ℓ p → PosLE (τ₀, 0) p
  | 0, _, ⟨_, _, hτ, hIO, hOp, _, _⟩ =>
    posLE_trans hτ (posLE_of_posLT (posLT_trans hIO hOp))
  | _ + 1, _, ⟨_, _, hIO, hOp, _, _, hprev⟩ =>
    posLE_trans (obtained_posLE hprev) (posLE_of_posLT (posLT_trans hIO hOp))

lemma obtained_layer {tr : Execution} {τ₀ n : ℕ} {g : Term} {i : ℕ} {ν : Term}
    {L : ℕ → SigComp.LayerOut} {d : ℕ} {p : Pos}
    (h : SigComp.Obtained tr τ₀ n g i ν L d p) {q : ℕ} (hq1 : 1 ≤ q) (hqd : q ≤ d) :
    ∃ pI pO : Pos, PosLE (τ₀, 0) pI ∧ PosLT pI pO ∧ PosLT pO p ∧
      evAt tr pI = some (Event.commitInv i g q (SigComp.refVal n g i ν L (q - 1))) ∧
      evAt tr pO = some (Event.commitOut i g q (L q).V (L q).ρ (L q).π) := by
  induction d generalizing p with
  | zero => omega
  | succ m ihm =>
    obtain ⟨pI, pO, hIO, hOp, hinv, hout, hprev⟩ := h
    rcases Nat.eq_or_lt_of_le hqd with rfl | hlt
    · exact ⟨pI, pO, obtained_posLE hprev, hIO, hOp, hinv, hout⟩
    · obtain ⟨pI', pO', hτ, hIO', hOp', hinv', hout'⟩ := ihm hprev (Nat.le_of_lt_succ hlt)
      exact ⟨pI', pO', hτ, hIO', posLT_trans hOp' (posLT_trans hIO hOp), hinv', hout'⟩

lemma occurs_sig_of_parse {σhat : Term} {i : ℕ} {m σ : Term} {U : List ℕ} {W G : List Term}
    (hp : SigComp.parse σhat = some (i, m, σ, U, W, G)) : Occurs σ σhat := by
  unfold SigComp.parse at hp
  split at hp
  · next ι μ σ' Us W' G' =>
    simp only [Option.map_eq_some_iff] at hp
    obtain ⟨U', _, heq⟩ := hp
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
    exact Occurs.tup (by simp) (Occurs.refl σ)
  · simp at hp

lemma epochUnforgeable_of_sec31 {n d : ℕ} {g : Term} {τ₀ tN tC : ℕ} {tr : Execution}
    (hM : SigComp.Sec31 n d g τ₀ tN tC tr) {j : ℕ} (hj : j < n) :
    (sigComp n).EpochUnforgeableAt d g τ₀ tr j := by
  intro p i m σhat q hcorr hacc_ev
  obtain ⟨pR, Rj, Aj, _, hcorrR, houtR, hver⟩ :=
    hM.verification j hj p i m σhat q hcorr hacc_ev
  change SigComp.verify n d g j i m σhat Rj q at hver
  have hver_orig := hver
  obtain ⟨σ, U, W, G, _, hparse, _, _, _, _, hroots, _, _, _, _, ⟨ρ₀, hρ₀, hsigv⟩, _, _⟩ := hver
  rw [SigVerify] at hsigv
  subst hsigv
  have hocc_sig : Occurs (Term.sig i (SigComp.statement g m ρ₀)) σhat :=
    occurs_sig_of_parse hparse
  have hdy_σhat : DY n (record tr p) σhat :=
    (hM.admissible p (Event.accept j g i m σhat q) hacc_ev).1 σhat (by simp [Event.used])
  have hsub : Term.sig i (SigComp.statement g m ρ₀) ∈ FreshSig.Layered.Sub (record tr p) :=
    sub_dy_sig hdy_σhat hocc_sig
  obtain ⟨e, hfi, hep, hev⟩ := firstIssue_of_sub_record hM.admissible hsub
  refine ⟨SigComp.statement g m ρ₀, hocc_sig, e, hfi, ?_, posLE_of_posLT hep, ?_⟩
  · rcases posLT_trichotomy (τ₀, 0) e with hlt | heq | hlt
    · exact Or.inl hlt
    · exact Or.inr heq
    · exfalso
      have hnot_before :=
        lemma_3_2 n d g τ₀ tN tC tr hM j hj pR Rj Aj hcorrR houtR
          i m σhat q hver_orig
          (Term.sig i (SigComp.statement g m ρ₀)) U W G hparse ρ₀ hρ₀
      apply hnot_before
      refine ⟨SigComp.statement g m ρ₀, ?_, Occurs.tup (by simp) (Occurs.refl ρ₀)⟩
      exact mem_record_iff.mpr ⟨e, Event.signCall i (SigComp.statement g m ρ₀), hlt, hev,
        by simp [Event.terms, Event.used]⟩
  · refine ⟨SigComp.statement g m ρ₀, List.replicate (d + 1) ρ₀, hev, ?_⟩
    have hr₀ : IsRoot n d ρ₀ := by
      have := hroots 0 ρ₀ hρ₀
      simpa using this
    change SigComp.signStatement n d g i m (List.replicate (d + 1) ρ₀) = _
    simp [SigComp.signStatement, hr₀]

end Aux33

theorem solution (n d : ℕ) (g : Term) (τ₀ tN tC : ℕ) :
    (sigComp n).CorrectA2 n ∧
    (∀ tr : Execution, SigComp.Sec31 n d g τ₀ tN tC tr →
      (sigComp n).RefreshCorrectIn n d g τ₀ tr ∧
      (∀ i < n, CorrectThrough tr τ₀ i (τ₀ + SigComp.tref tN tC d) →
        ∃ (p : Pos) (R : List Term) (A : List FwdRecord), p.1 = τ₀ + SigComp.tref tN tC d ∧
          evAt tr p = some (Event.refreshOut i g R A) ∧ (sigComp n).wellFormedLists d R A) ∧
      (∀ j < n, (sigComp n).EpochUnforgeableAt d g τ₀ tr j) ∧
      (∀ j < n, ∀ k < n, ∀ (pj pk : Pos) (Rj Rk : List Term) (Aj Ak : List FwdRecord),
        CorrectAt tr τ₀ j pj → evAt tr pj = some (Event.refreshOut j g Rj Aj) →
        CorrectAt tr τ₀ k pk → evAt tr pk = some (Event.refreshOut k g Rk Ak) →
        ∀ q : ℕ, 1 ≤ q → q ≤ d →
          ((sigComp n).Compat Rj Aj q k Rk ↔ SigComp.Delivered tr τ₀ g q k j))) ∧
    (sigComp n).Realised n (SigComp.Sec31 n d g τ₀ tN tC) d g τ₀ (SigComp.tref tN tC d) := by
  have h31 := lemma_3_1 n
  refine ⟨h31.1, ?_, ?_⟩
  · intro tr hM
    have hM31 := h31.2 d g τ₀ tN tC tr hM
    exact ⟨hM31.1, hM31.2.1, fun j hj => Aux33.epochUnforgeable_of_sec31 hM hj, hM31.2.2⟩
  · refine ⟨h31.1, fun tr hM => ?_⟩
    have hM31 := h31.2 d g τ₀ tN tC tr hM
    refine ⟨?_, hM31.1, ?_, fun j hj => Aux33.epochUnforgeable_of_sec31 hM hj⟩
    · intro i hi hth
      obtain ⟨p, R, A, hp1, hev, _⟩ := hM31.2.1 i hi hth
      exact ⟨p, R, A, by omega, by omega, hev⟩
    · intro j hj k hk _ hth_k pj pk Rj Rk Aj Ak hcorr_j hout_j hcorr_k hout_k q i m σhat _ hfwd
      obtain ⟨_, hq1, hqd, _, a, v, _, _, hAj, ha1, _, _⟩ :=
        h31.1.2.2.2 d g j k i m σhat Rj Aj q hj hfwd
      obtain ⟨hpj_round, νj, Lj, hObt_j, _, rfl⟩ :=
        (hM.refresh j hj).out_step pj Rj Aj hcorr_j hout_j
      obtain ⟨_, νk, Lk, hObt_k, _, _⟩ :=
        (hM.refresh k hk).out_step pk Rk Ak hcorr_k hout_k
      obtain ⟨pIj, pOj, hτIj, hpIjOj, hpOjpj, hinv_j, hout_oj⟩ :=
        Aux33.obtained_layer hObt_j hq1 hqd
      obtain ⟨pIk, _, hτIk, hpIkOk, hpOkpk, hinv_k, _⟩ :=
        Aux33.obtained_layer hObt_k hq1 hqd
      have hcorr_pIj : CorrectAt tr τ₀ j pIj :=
        Aux33.correctAt_mono hcorr_j hτIj
          (Aux33.posLE_of_posLT (Aux33.posLT_trans hpIjOj hpOjpj))
      have hcorr_pOj : CorrectAt tr τ₀ j pOj :=
        Aux33.correctAt_mono hcorr_j
          (Aux33.posLE_trans hτIj (Aux33.posLE_of_posLT hpIjOj))
          (Aux33.posLE_of_posLT hpOjpj)
      have hcorr_pIk : CorrectAt tr τ₀ k pIk :=
        Aux33.correctAt_mono hcorr_k hτIk
          (Aux33.posLE_of_posLT (Aux33.posLT_trans hpIkOk hpOkpk))
      have hpOj_round : pOj.1 ≤ τ₀ + SigComp.tref tN tC d := by
        have := Aux33.posLE_fst (Aux33.posLE_of_posLT hpOjpj)
        omega
      have hcorr_k_pOj : CorrectAt tr τ₀ k pOj :=
        Aux33.correctAt_of_through hth_k
          (Aux33.posLE_trans hτIj (Aux33.posLE_of_posLT hpIjOj)) hpOj_round
      have hOK := hM.commitment.guarantees j hj pIj pOj q _ (Lj q).V (Lj q).ρ (Lj q).π
        hcorr_pIj hinv_j hpIjOj hcorr_pOj hout_oj
      have hvk_or := hOK.2.2.2.1 k hk pIk _ hcorr_pIk hinv_k hcorr_k_pOj
      have hAj_eq : (SigComp.listsA Lj d)[q - 1]? = some ((Lj q).V, (Lj q).π) := by
        have hqlt : q - 1 < d := by omega
        have hqeq : q - 1 + 1 = q := by omega
        simp [SigComp.listsA, hqlt, hqeq]
      rw [hAj_eq] at hAj
      injection hAj with ha_eq
      rw [← ha_eq] at ha1
      have hV_eq : (Lj q).V[k]? = some (some (SigComp.refVal n g k νk Lk (q - 1))) := by
        rcases hvk_or with h1 | h2
        · exact h1
        · rw [ha1] at h2; cases h2
      have hDel : SigComp.Delivered tr τ₀ g q k j :=
        ⟨pIk, pOj, _, (Lj q).V, (Lj q).ρ, (Lj q).π, hcorr_pIk, hinv_k, hcorr_pOj, hout_oj, hV_eq⟩
      exact (hM31.2.2 j hj k hk pj pk Rj _ _ Ak hcorr_j hout_j hcorr_k hout_k q hq1 hqd).mpr hDel
