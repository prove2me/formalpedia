-- Prove2me | solution 1 for FreshSig.Layered.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:55:05.470845+00:00
-- url     : https://prove2.me/submissions/caf580bf-7201-4491-bb51-89759ae9a28c

import Definitions.Def_FreshSig_Layered_Term
import Definitions.Def_FreshSig_Layered_Execution
import Definitions.Def_FreshSig_Layered_EpochScheme
import Definitions.Def_FreshSig_Layered_SigComp

open FreshSig.Layered

namespace Aux32

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

lemma correctAt_mono {tr : Execution} {τ₀ i : ℕ} {p q : Pos}
    (hq : CorrectAt tr τ₀ i q) (hτ : PosLE (τ₀, 0) p) (hpq : PosLE p q) :
    CorrectAt tr τ₀ i p :=
  ⟨hτ, fun p' h1 h2 => hq.2 p' h1 (posLE_trans h2 hpq)⟩

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

lemma record_mono {tr : Execution} {p q : Pos} (hpq : PosLE p q) :
    record tr p ⊆ record tr q := by
  intro t ⟨ev, hev, ht⟩
  obtain ⟨r, hrp, hevr⟩ := mem_prefixEvents_iff.mp hev
  exact ⟨ev, mem_prefixEvents_iff.mpr ⟨r, posLT_of_posLT_of_posLE hrp hpq, hevr⟩, ht⟩

lemma occurs_trans {a b c : Term} (hab : Occurs a b) (hbc : Occurs b c) : Occurs a c := by
  induction hbc with
  | refl => exact hab
  | tup ht _ ih => exact Occurs.tup ht (ih hab)
  | sigId k x => cases hab; exact Occurs.sigId k x
  | sig k _ ih => exact Occurs.sig k (ih hab)
  | extId k₁ k₂ x => cases hab; exact Occurs.extId k₁ k₂ x
  | ext k₁ k₂ _ ih => exact Occurs.ext k₁ k₂ (ih hab)
  | leaf _ ih => exact Occurs.leaf (ih hab)
  | root ht _ ih => exact Occurs.root ht (ih hab)
  | prf ht _ ih => exact Occurs.prf ht (ih hab)

lemma obtained_posLE {tr : Execution} {τ₀ n : ℕ} {g : Term} {i : ℕ} {ν : Term}
    {L : ℕ → SigComp.LayerOut} :
    ∀ {ℓ : ℕ} {p : Pos}, SigComp.Obtained tr τ₀ n g i ν L ℓ p → PosLE (τ₀, 0) p
  | 0, _, ⟨_, _, hτ, hIO, hOp, _, _⟩ =>
    posLE_trans hτ (posLE_of_posLT (posLT_trans hIO hOp))
  | _ + 1, _, ⟨_, _, hIO, hOp, _, _, hprev⟩ =>
    posLE_trans (obtained_posLE hprev) (posLE_of_posLT (posLT_trans hIO hOp))

lemma obtained_zero {tr : Execution} {τ₀ n : ℕ} {g : Term} {i : ℕ} {ν : Term}
    {L : ℕ → SigComp.LayerOut} :
    ∀ {ℓ : ℕ} {p : Pos}, SigComp.Obtained tr τ₀ n g i ν L ℓ p →
      ∃ pI pO : Pos, PosLE (τ₀, 0) pI ∧ PosLT pI pO ∧ PosLT pO p ∧
        evAt tr pI = some (Event.nonceInv i g) ∧
        evAt tr pO = some (Event.nonceOut i g (some ν))
  | 0, _, h => h
  | _ + 1, _, ⟨_, _, hIO, hOp, _, _, hprev⟩ => by
    obtain ⟨pI₀, pO₀, hτ, hIO₀, hOp₀, hinv, hout⟩ := obtained_zero hprev
    exact ⟨pI₀, pO₀, hτ, hIO₀, posLT_trans hOp₀ (posLT_trans hIO hOp), hinv, hout⟩

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

lemma occurs_path {U : List ℕ} {W G : List Term} {h : ℕ} {ρ₀ : Term} (hW₀ : W[0]? = some ρ₀)
    (hchain : ∀ a < h, ∃ (u : ℕ) (ρ ρ' γ : Term), U[a + 1]? = some u ∧ W[a]? = some ρ ∧
      W[a + 1]? = some ρ' ∧ G[a]? = some γ ∧ OpenVerify ρ u (some ρ') (some γ)) :
    ∀ k ≤ h, ∀ ρk : Term, W[k]? = some ρk → Occurs ρk ρ₀ := by
  intro k hk
  induction k with
  | zero =>
    intro ρk hWk
    rw [hW₀] at hWk
    injection hWk with heq
    exact heq ▸ Occurs.refl ρ₀
  | succ a iha =>
    intro ρk hWk
    obtain ⟨u, ρ, ρ', γ, _, hWa, hWa1, _, ⟨ℓ, V, hroot, hVu, _⟩⟩ :=
      hchain a (Nat.lt_of_succ_le hk)
    rw [hWk] at hWa1
    injection hWa1 with hρ'
    subst hρ'
    subst hroot
    have hstep : Occurs ρk (Term.root ℓ V) :=
      Occurs.root (List.mem_of_getElem? hVu) (Occurs.refl ρk)
    exact occurs_trans hstep (iha (Nat.le_of_succ_le hk) _ hWa)

lemma occurs_refVal {n d : ℕ} {g : Term} {τ₀ tN tC : ℕ} {tr : Execution}
    (hM : SigComp.Sec31 n d g τ₀ tN tC tr) {j : ℕ} (hj : j < n) {pR : Pos}
    (hcorr : CorrectAt tr τ₀ j pR) {ν : Term} {L : ℕ → SigComp.LayerOut}
    (hObt : SigComp.Obtained tr τ₀ n g j ν L d pR) :
    ∀ ℓ ≤ d, Occurs (SigComp.refVal n g j ν L 0) (SigComp.refVal n g j ν L ℓ) := by
  intro ℓ hℓ
  induction ℓ with
  | zero => exact Occurs.refl _
  | succ m ihm =>
    obtain ⟨pI, pO, hτI, hpIO, hpOR, hinv, hout⟩ :=
      obtained_layer hObt (Nat.succ_pos m) hℓ
    have hcorrI : CorrectAt tr τ₀ j pI :=
      correctAt_mono hcorr hτI (posLE_of_posLT (posLT_trans hpIO hpOR))
    have hcorrO : CorrectAt tr τ₀ j pO :=
      correctAt_mono hcorr (posLE_trans hτI (posLE_of_posLT hpIO)) (posLE_of_posLT hpOR)
    have hOK := hM.commitment.guarantees j hj pI pO (m + 1) _ (L (m + 1)).V (L (m + 1)).ρ
      (L (m + 1)).π hcorrI hinv hpIO hcorrO hout
    have hρ_eq : (L (m + 1)).ρ = Term.root (m + 1) (L (m + 1)).V := hOK.1
    have hself : (L (m + 1)).V[j]? = some (some (SigComp.refVal n g j ν L m)) := hOK.2.2.2.2.1
    have hstep : Occurs (SigComp.refVal n g j ν L m) (SigComp.refVal n g j ν L (m + 1)) := by
      change Occurs (SigComp.refVal n g j ν L m) (L (m + 1)).ρ
      rw [hρ_eq]
      exact Occurs.root (List.mem_of_getElem? hself) (Occurs.refl _)
    exact occurs_trans (ihm (Nat.le_of_succ_le hℓ)) hstep

lemma occurs_nonce_refVal0 {n : ℕ} {g : Term} {j : ℕ} (hj : j < n) {ν : Term}
    {L : ℕ → SigComp.LayerOut} :
    Occurs ν (SigComp.refVal n g j ν L 0) := by
  have hmem : some (leafOf g ν) ∈ SigComp.baseVec n g j ν := by
    simp only [SigComp.baseVec, List.mem_map, List.mem_range]
    exact ⟨j, hj, by simp⟩
  exact Occurs.root hmem (Occurs.leaf (Occurs.tup (by simp) (Occurs.refl ν)))

end Aux32

theorem solution (n d : ℕ) (g : Term) (τ₀ tN tC : ℕ) (tr : Execution)
    (hM : SigComp.Sec31 n d g τ₀ tN tC tr)
    (j : ℕ) (hj : j < n) (pR : Pos) (Rj : List Term) (Aj : List FwdRecord)
    (hcorr : CorrectAt tr τ₀ j pR) (hout : evAt tr pR = some (Event.refreshOut j g Rj Aj))
    (i : ℕ) (m σhat : Term) (q : ℕ) (hacc : SigComp.verify n d g j i m σhat Rj q)
    (σ : Term) (U : List ℕ) (W G : List Term)
    (hparse : SigComp.parse σhat = some (i, m, σ, U, W, G))
    (ρ₀ : Term) (hρ₀ : W[0]? = some ρ₀) :
    ¬ OccursBefore tr (τ₀, 0) ρ₀ := by
  obtain ⟨σ', U', W', G', h, hparse', _, _, _, _, _, _, _, hhd, hqd, _, hchain, ⟨ρh, hWh, hRjq⟩⟩ :=
    hacc
  rw [hparse] at hparse'
  obtain ⟨rfl, rfl, rfl, rfl⟩ : σ = σ' ∧ U = U' ∧ W = W' ∧ G = G' := by
    injection hparse' with heq
    simp only [Prod.mk.injEq] at heq
    exact ⟨heq.2.2.1, heq.2.2.2.1, heq.2.2.2.2.1, heq.2.2.2.2.2⟩
  have hocc_ρh_ρ₀ : Occurs ρh ρ₀ :=
    Aux32.occurs_path hρ₀ hchain h (le_refl h) ρh hWh
  obtain ⟨_, νj, Lj, hObt, rfl, _⟩ := (hM.refresh j hj).out_step pR Rj Aj hcorr hout
  have hqd_le : q ≤ d := by omega
  have hRj_eq : (SigComp.listsR n g j νj Lj d)[q]? = some (SigComp.refVal n g j νj Lj q) := by
    have hqlt : q < d + 1 := by omega
    simp [SigComp.listsR, hqlt]
  rw [hRj_eq] at hRjq
  injection hRjq with hρh_eq
  subst hρh_eq
  have hocc_r0_rq : Occurs (SigComp.refVal n g j νj Lj 0) (SigComp.refVal n g j νj Lj q) :=
    Aux32.occurs_refVal hM hj hcorr hObt q hqd_le
  have hocc_ν_r0 : Occurs νj (SigComp.refVal n g j νj Lj 0) :=
    Aux32.occurs_nonce_refVal0 hj
  have hocc_ν_ρ₀ : Occurs νj ρ₀ :=
    Aux32.occurs_trans hocc_ν_r0 (Aux32.occurs_trans hocc_r0_rq hocc_ρh_ρ₀)
  obtain ⟨pI₀, pO₀, hτI₀, hpIO₀, hpOR₀, hinv₀, hout₀⟩ := Aux32.obtained_zero hObt
  have hcorrI₀ : CorrectAt tr τ₀ j pI₀ :=
    Aux32.correctAt_mono hcorr hτI₀ (Aux32.posLE_of_posLT (Aux32.posLT_trans hpIO₀ hpOR₀))
  have hcorrO₀ : CorrectAt tr τ₀ j pO₀ :=
    Aux32.correctAt_mono hcorr
      (Aux32.posLE_trans hτI₀ (Aux32.posLE_of_posLT hpIO₀))
      (Aux32.posLE_of_posLT hpOR₀)
  obtain ⟨tν, htν, hnonce⟩ := hM.nonce.freshness j hj pI₀ pO₀ (some νj) hcorrI₀ hinv₀ hpIO₀ hcorrO₀ hout₀
  injection htν with htν_eq
  subst htν_eq
  intro ⟨b, hb_rec, hocc_ρ₀_b⟩
  apply hnonce
  refine ⟨b, DY.base (Aux32.record_mono hτI₀ hb_rec), Aux32.occurs_trans hocc_ν_ρ₀ hocc_ρ₀_b⟩
