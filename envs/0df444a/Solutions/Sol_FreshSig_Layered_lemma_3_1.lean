-- Prove2me | solution 1 for FreshSig.Layered.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:56:53.438428+00:00
-- url     : https://prove2.me/submissions/d283a784-4f3c-43dd-a969-5681c1326fb5

import Definitions.Def_FreshSig_Layered_Term
import Definitions.Def_FreshSig_Layered_Execution
import Definitions.Def_FreshSig_Layered_EpochScheme
import Definitions.Def_FreshSig_Layered_SigComp

open FreshSig.Layered

namespace Aux31

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

lemma posLE_fst {a b : Pos} (h : PosLE a b) : a.1 ≤ b.1 := by
  rcases h with (h1 | ⟨h1, _⟩) | rfl <;> omega

lemma posLE_of_fst_eq {p : Pos} {τ₀ : ℕ} (h : τ₀ ≤ p.1) : PosLE (τ₀, 0) p := by
  rcases Nat.eq_or_lt_of_le h with heq | hlt
  · rcases Nat.eq_zero_or_pos p.2 with hp2 | hp2
    · exact Or.inr (Prod.ext heq hp2.symm)
    · exact Or.inl (Or.inr ⟨heq, hp2⟩)
  · exact Or.inl (Or.inl hlt)

lemma correctAt_mono {tr : Execution} {τ₀ i : ℕ} {p q : Pos}
    (hq : CorrectAt tr τ₀ i q) (hτ : PosLE (τ₀, 0) p) (hpq : PosLE p q) :
    CorrectAt tr τ₀ i p :=
  ⟨hτ, fun p' h1 h2 => hq.2 p' h1 (posLE_trans h2 hpq)⟩

lemma correctAt_of_through {tr : Execution} {τ₀ i r : ℕ} {p : Pos}
    (hth : CorrectThrough tr τ₀ i r) (hτ : τ₀ ≤ p.1) (hpr : p.1 ≤ r) :
    CorrectAt tr τ₀ i p := by
  refine ⟨posLE_of_fst_eq hτ, fun p' h1 h2 => hth p' ?_ ?_⟩
  · exact posLE_fst h1
  · exact le_trans (posLE_fst h2) hpr

lemma correctThrough_mono {tr : Execution} {τ₀ i r₁ r₂ : ℕ}
    (h : CorrectThrough tr τ₀ i r₂) (hle : r₁ ≤ r₂) : CorrectThrough tr τ₀ i r₁ :=
  fun p' h1 h2 => h p' h1 (le_trans h2 hle)

lemma parsePids_map_pid : ∀ (U : List ℕ), SigComp.parsePids (U.map Term.pid) = some U
  | [] => rfl
  | u :: us => by simp [SigComp.parsePids, parsePids_map_pid us]

lemma parse_mk (i : ℕ) (m σ : Term) (U : List ℕ) (W G : List Term) :
    SigComp.parse (SigComp.mk i m σ U W G) = some (i, m, σ, U, W, G) := by
  simp [SigComp.mk, SigComp.parse, parsePids_map_pid]

lemma getLast?_eq_of_getElem? : ∀ (U : List ℕ) (h j : ℕ),
    U.length = h + 1 → U[h]? = some j → U.getLast? = some j
  | [], _, _, hlen, _ => by simp at hlen
  | [x], 0, j, _, hx => by simpa using hx
  | [_], _ + 1, _, hlen, _ => by simp at hlen
  | _ :: _ :: _, 0, _, hlen, _ => by simp at hlen
  | _ :: y :: zs, h + 1, j, hlen, hx => by
    have hlen' : (y :: zs).length = h + 1 := by
      simp only [List.length_cons] at hlen ⊢
      omega
    have hx' : (y :: zs)[h]? = some j := by simpa using hx
    simpa using getLast?_eq_of_getElem? (y :: zs) h j hlen' hx'

lemma getD_eq_of_getElem? {α : Type} : ∀ (l : List α) (k : ℕ) (x d : α),
    l[k]? = some x → l.getD k d = x
  | [], _, _, _, h => by simp at h
  | _ :: _, 0, x, _, h => by simp at h; exact h
  | _ :: as, k + 1, x, d, h => getD_eq_of_getElem? as k x d (by simpa using h)

lemma lt_length_of_getElem?_some {α : Type} : ∀ (l : List α) (k : ℕ) (x : α),
    l[k]? = some x → k < l.length
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, _ => Nat.succ_pos _
  | _ :: as, k + 1, x, h => Nat.succ_lt_succ (lt_length_of_getElem?_some as k x (by simpa using h))

lemma localCorrectness (n : ℕ) : (sigComp n).LocalCorrectness n := by
  intro d g i m R hi hR
  obtain ⟨hRlen, hRroots⟩ := hR
  have hdlt : d < R.length := by omega
  have hr : R[d]? = some (R[d]'hdlt) := List.getElem?_eq_getElem hdlt
  set r := R[d]'hdlt
  have hr_root : IsRoot n d r := hRroots d r hr
  set σ₀ := Term.sig i (SigComp.statement g m r)
  set σhat := SigComp.mk i m σ₀ [i] [r] []
  refine ⟨σhat, ?_, ?_, ?_⟩
  · change SigComp.sign n d g i m R = some σhat
    simp [SigComp.sign, hr, hr_root, σhat, σ₀]
  · change (SigComp.info d σhat).map SigInfo.depth = some d
    simp [SigComp.info, parse_mk, σhat]
  · change SigComp.verify n d g i i m σhat R d
    refine ⟨σ₀, [i], [r], [], 0, parse_mk i m σ₀ [i] [r] [], rfl, rfl, rfl, ?_, ?_,
      rfl, rfl, Nat.zero_le d, (Nat.sub_zero d).symm, ⟨r, rfl, rfl⟩, ?_, ⟨r, rfl, hr⟩⟩
    · intro u hu
      simp only [List.mem_singleton] at hu
      exact hu ▸ hi
    · intro a ρ ha
      cases a with
      | zero =>
        simp at ha
        exact ha ▸ hr_root
      | succ a' => simp at ha
    · intro a ha; omega

lemma forwardability (n : ℕ) : (sigComp n).Forwardability n := by
  intro d g q i j k m σhat Rj Aj Rk _ hk hq1 hqd hcompat hver
  obtain ⟨_, r, a, v, π, hRjq, hAjq, _, ha1, ha2, hRk, hv_root, hopen_v⟩ := hcompat
  have hver_orig : SigComp.verify n d g j i m σhat Rj q := hver
  obtain ⟨σ, U, W, G, h, hparse, hUlen, hWlen, hGlen, hUn, hWroots, hU0, _, hhd, hqdh,
    ⟨ρ₀, hW0, hsig⟩, hchain, ⟨ρh, hWh, hRjq'⟩⟩ := hver
  rw [hRjq] at hRjq'
  injection hRjq' with hρh_eq
  subst hρh_eq
  set σ' := SigComp.mk i m σ (U ++ [k]) (W ++ [v]) (G ++ [π])
  refine ⟨σ', ?_, ?_, ?_⟩
  · change SigComp.forward n d g j k i m σhat Rj Aj q = some σ'
    simp [SigComp.forward, hparse, hq1, hqd, hver_orig, hAjq, hRjq, ha1, ha2, hv_root, hopen_v, σ']
  · change SigComp.info d σ' = some ⟨i, m, k, q - 1⟩
    simp [SigComp.info, parse_mk, hGlen, σ']
    omega
  · change SigComp.verify n d g k i m σ' Rk (q - 1)
    have hUlen' : (U ++ [k]).length = (h + 1) + 1 := by simp [hUlen]
    have hWlen' : (W ++ [v]).length = (h + 1) + 1 := by simp [hWlen]
    have hGlen' : (G ++ [π]).length = h + 1 := by simp [hGlen]
    have hWh1 : (W ++ [v])[h + 1]? = some v := by
      rw [List.getElem?_append_right (by omega)]
      simp [hWlen]
    refine ⟨σ, U ++ [k], W ++ [v], G ++ [π], h + 1,
      parse_mk i m σ (U ++ [k]) (W ++ [v]) (G ++ [π]),
      hUlen', hWlen', hGlen', ?_, ?_, ?_, ?_, by omega, by omega,
      ⟨ρ₀, ?_, hsig⟩, ?_, ⟨v, hWh1, hRk⟩⟩
    · intro u hu
      simp only [List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact hUn u hu
      · exact hk
    · intro idx ρ hidx
      rcases lt_or_ge idx W.length with hlt | hge
      · rw [List.getElem?_append_left hlt] at hidx
        exact hWroots idx ρ hidx
      · rw [List.getElem?_append_right hge] at hidx
        have hsub : idx - W.length = 0 := by
          have := lt_length_of_getElem?_some [v] (idx - W.length) ρ hidx
          simp at this
          omega
        rw [hsub] at hidx
        simp at hidx
        subst hidx
        have hdidx : d - idx = q - 1 := by omega
        exact hdidx ▸ hv_root
    · rw [List.getElem?_append_left (by omega)]
      exact hU0
    · rw [List.getElem?_append_right (by omega)]
      simp [hUlen]
    · rw [List.getElem?_append_left (by omega)]
      exact hW0
    · intro idx hidx
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hidx) with hlt | rfl
      · obtain ⟨u, ρ, ρ', γ, hUu, hWρ, hWρ', hGγ, hop⟩ := hchain idx hlt
        refine ⟨u, ρ, ρ', γ, ?_, ?_, ?_, ?_, hop⟩
        · rw [List.getElem?_append_left (by omega)]; exact hUu
        · rw [List.getElem?_append_left (by omega)]; exact hWρ
        · rw [List.getElem?_append_left (by omega)]; exact hWρ'
        · rw [List.getElem?_append_left (by omega)]; exact hGγ
      · refine ⟨k, r, v, π, ?_, ?_, hWh1, ?_, hopen_v⟩
        · rw [List.getElem?_append_right (by omega)]; simp [hUlen]
        · rw [List.getElem?_append_left (by omega)]; exact hWh
        · rw [List.getElem?_append_right (by omega)]; simp [hGlen]

lemma rejection (n : ℕ) : (sigComp n).Rejection n := by
  refine ⟨?_, ?_⟩
  · intro d g j i m σhat R q hver
    obtain ⟨σ, U, W, G, h, hparse, hUlen, _, hGlen, _, _, _, hUh, hhd, hqdh, _, _, _⟩ := hver
    have hlast : U.getLast? = some j := getLast?_eq_of_getElem? U h j hUlen hUh
    have hinfo : SigComp.info d σhat = some ⟨i, m, j, q⟩ := by
      simp [SigComp.info, hparse, hlast, hGlen, hqdh]
    change (SigComp.info d σhat).map SigInfo.holder = some j ∧
      (SigComp.info d σhat).map SigInfo.depth = some q ∧ q ≤ d
    simp [hinfo]
    omega
  · intro d g j k i m σhat R A q _ hfwd
    change SigComp.forward n d g j k i m σhat R A q ≠ none at hfwd
    unfold SigComp.forward at hfwd
    split at hfwd
    · exact absurd rfl hfwd
    · next ι μ σ U W G _ =>
      split_ifs at hfwd with hcond
      · rcases hcond with ⟨hq1, hqd, hver⟩
        cases hA : A[q - 1]? with
        | none => rw [hA] at hfwd; exact absurd rfl hfwd
        | some a =>
          rw [hA] at hfwd
          cases hR : R[q]? with
          | none => rw [hR] at hfwd; exact absurd rfl hfwd
          | some r =>
            rw [hR] at hfwd; dsimp only at hfwd
            cases ha1 : a.1[k]? with
            | none => rw [ha1] at hfwd; exact absurd rfl hfwd
            | some opt_v =>
              cases opt_v with
              | none => rw [ha1] at hfwd; exact absurd rfl hfwd
              | some v =>
                rw [ha1] at hfwd
                cases ha2 : a.2[k]? with
                | none => rw [ha2] at hfwd; exact absurd rfl hfwd
                | some opt_π =>
                  cases opt_π with
                  | none => rw [ha2] at hfwd; exact absurd rfl hfwd
                  | some π =>
                    rw [ha2] at hfwd; dsimp only at hfwd
                    split_ifs at hfwd with hve
                    · exact ⟨hver, hq1, hqd, r, a, v, π, rfl, rfl, ha1, ha2, hve⟩
                    · exact absurd rfl hfwd
      · exact absurd rfl hfwd

lemma isRoot_baseVec (n : ℕ) (g : Term) (i : ℕ) (ν : Term) (L : ℕ → SigComp.LayerOut) :
    IsRoot n 0 (SigComp.refVal n g i ν L 0) := by
  refine IsRoot.zero (SigComp.baseVec n g i ν) (by simp [SigComp.baseVec]) ?_
  intro t ht
  simp only [SigComp.baseVec, List.mem_map, List.mem_range] at ht
  obtain ⟨k, _, hk⟩ := ht
  split_ifs at hk
  simp only [Option.some.injEq] at hk
  exact ⟨Term.tup [g, ν], hk.symm⟩

lemma wfRecord_of_commitOutputOK {n : ℕ} {tr : Execution} {τ₀ : ℕ} {g : Term} {i m : ℕ}
    {v : Term} {V : List (Option Term)} {ρ : Term} {π : List (Option Term)} {pO : Pos}
    (hOK : CommitOutputOK n tr τ₀ g i (m + 1) v V ρ π pO) :
    IsRoot n (m + 1) ρ ∧ SigComp.WFRecord n (m + 1) ρ (V, π) := by
  obtain ⟨hρ, hπlen, ⟨hVlen, hVtyp⟩, _, _, hopen⟩ := hOK
  have hr_root : IsRoot n (m + 1) ρ := by
    rw [hρ]
    exact IsRoot.succ m V hVlen (fun t ht => (hVtyp t ht).2 (Nat.succ_pos m))
  refine ⟨hr_root, hr_root, hVlen, ?_, ?_⟩
  · intro k vk hVk
    exact (hVtyp vk (List.mem_of_getElem? hVk)).2 (Nat.succ_pos m)
  · intro k vk hVk
    have hk : k < n := by
      have := lt_length_of_getElem?_some V k (some vk) hVk
      omega
    have hop := hopen k hk
    have hVgetD : V.getD k none = some vk := getD_eq_of_getElem? V k (some vk) none hVk
    rw [hVgetD] at hop
    have hkπ : k < π.length := by omega
    have hπk : π[k]? = some (π[k]'hkπ) := List.getElem?_eq_getElem hkπ
    have hπgetD : π.getD k none = π[k]'hkπ := getD_eq_of_getElem? π k (π[k]'hkπ) none hπk
    rw [hπgetD] at hop
    obtain ⟨ℓ', V', hρ', hV'k, hprf⟩ := hop
    exact ⟨Term.prf ℓ' V' k, hprf ▸ hπk, ℓ', V', hρ', hV'k, rfl⟩

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

lemma refVal_congr {n : ℕ} {g : Term} {i : ℕ} {ν : Term} {L L' : ℕ → SigComp.LayerOut}
    {m : ℕ} (h : ∀ x ≤ m, L' x = L x) :
    SigComp.refVal n g i ν L' m = SigComp.refVal n g i ν L m := by
  cases m with
  | zero => rfl
  | succ k => simp [SigComp.refVal, h (k + 1) (le_refl _)]

lemma obtained_congr {tr : Execution} {τ₀ n : ℕ} {g : Term} {i : ℕ} {ν : Term}
    {L L' : ℕ → SigComp.LayerOut} :
    ∀ {ℓ : ℕ} (_h : ∀ x ≤ ℓ, L' x = L x) {p : Pos},
      SigComp.Obtained tr τ₀ n g i ν L ℓ p → SigComp.Obtained tr τ₀ n g i ν L' ℓ p
  | 0, _, _, hObt => hObt
  | m + 1, h, _, ⟨pI, pO, hIO, hOp, hinv, hout, hprev⟩ => by
    have hm : ∀ x ≤ m, L' x = L x := fun x hx => h x (Nat.le_succ_of_le hx)
    have href : SigComp.refVal n g i ν L' m = SigComp.refVal n g i ν L m := refVal_congr hm
    have hLm1 : L' (m + 1) = L (m + 1) := h (m + 1) (le_refl _)
    exact ⟨pI, pO, hIO, hOp, href ▸ hinv, hLm1 ▸ hout, obtained_congr hm hprev⟩

lemma refreshCorrectIn {n d : ℕ} {g : Term} {τ₀ tN tC : ℕ} {tr : Execution}
    (hM : SigComp.Sec31 n d g τ₀ tN tC tr) :
    (sigComp n).RefreshCorrectIn n d g τ₀ tr := by
  intro i hi p R A hcorr hout
  obtain ⟨_, ν, L, hObt, rfl, rfl⟩ := (hM.refresh i hi).out_step p R A hcorr hout
  have hlayer_wf : ∀ m : ℕ, m + 1 ≤ d →
      IsRoot n (m + 1) (L (m + 1)).ρ ∧
        SigComp.WFRecord n (m + 1) (L (m + 1)).ρ ((L (m + 1)).V, (L (m + 1)).π) := by
    intro m hm
    obtain ⟨pI, pO, hτI, hpIO, hpOp, hinv, houtO⟩ :=
      obtained_layer hObt (Nat.succ_pos m) hm
    have hcorrI : CorrectAt tr τ₀ i pI :=
      correctAt_mono hcorr hτI (posLE_of_posLT (posLT_trans hpIO hpOp))
    have hcorrO : CorrectAt tr τ₀ i pO :=
      correctAt_mono hcorr (posLE_trans hτI (posLE_of_posLT hpIO)) (posLE_of_posLT hpOp)
    exact wfRecord_of_commitOutputOK
      (hM.commitment.guarantees i hi pI pO (m + 1) _ (L (m + 1)).V (L (m + 1)).ρ (L (m + 1)).π
        hcorrI hinv hpIO hcorrO houtO)
  refine ⟨⟨by simp [SigComp.listsR], ?_⟩, by simp [SigComp.listsA], ?_⟩
  · intro ℓ r hRℓ
    have hℓlt : ℓ < d + 1 := by
      have := lt_length_of_getElem?_some (SigComp.listsR n g i ν L d) ℓ r hRℓ
      simpa [SigComp.listsR] using this
    have hRℓ' : (SigComp.listsR n g i ν L d)[ℓ]? = some (SigComp.refVal n g i ν L ℓ) := by
      simp [SigComp.listsR, hℓlt]
    rw [hRℓ'] at hRℓ
    injection hRℓ with hr_eq
    subst hr_eq
    cases ℓ with
    | zero => exact isRoot_baseVec n g i ν L
    | succ m => exact (hlayer_wf m (Nat.le_of_lt_succ hℓlt)).1
  · intro ℓ r a hℓ1 hRℓ hAℓ
    have hℓsub_lt : ℓ - 1 < d := by
      have := lt_length_of_getElem?_some (SigComp.listsA L d) (ℓ - 1) a hAℓ
      simpa [SigComp.listsA] using this
    have hℓlt : ℓ < d + 1 := by omega
    obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
    have hmlt : m < d := by omega
    have hRℓ' : (SigComp.listsR n g i ν L d)[m + 1]? = some (L (m + 1)).ρ := by
      simp [SigComp.listsR, SigComp.refVal, hℓlt]
    have hAℓ' : (SigComp.listsA L d)[m]? = some ((L (m + 1)).V, (L (m + 1)).π) := by
      simp [SigComp.listsA, hmlt]
    rw [hRℓ'] at hRℓ
    simp only [Nat.add_sub_cancel] at hAℓ
    rw [hAℓ'] at hAℓ
    injection hRℓ with hr_eq
    injection hAℓ with ha_eq
    subst hr_eq; subst ha_eq
    exact (hlayer_wf m (Nat.le_of_lt_succ hℓlt)).2

lemma obtained_through_layers {n d : ℕ} {g : Term} {τ₀ tN tC : ℕ} {tr : Execution}
    (hM : SigComp.Sec31 n d g τ₀ tN tC tr) {i : ℕ} (hi : i < n)
    (hth : CorrectThrough tr τ₀ i (τ₀ + SigComp.tref tN tC d)) :
    ∀ ℓ ≤ d, ∃ (ν : Term) (L : ℕ → SigComp.LayerOut),
      SigComp.Obtained tr τ₀ n g i ν L ℓ (τ₀ + tN + ℓ * tC + 1, 0) := by
  intro ℓ hℓ
  induction ℓ with
  | zero =>
    have hth0 : CorrectThrough tr τ₀ i τ₀ :=
      correctThrough_mono hth (by simp [SigComp.tref])
    obtain ⟨pI, hpI1, hinv⟩ := (hM.refresh i hi).nonce_exists hth0
    have hcorrI : CorrectAt tr τ₀ i pI :=
      correctAt_of_through hth0 (by omega) (by omega)
    have hthN : CorrectThrough tr τ₀ i (pI.1 + tN) :=
      correctThrough_mono hth (by simp [SigComp.tref]; omega)
    obtain ⟨pO, ν, hpIO, hpO1, hout⟩ := hM.nonce.termination i hi pI hcorrI hinv hthN
    refine ⟨ν, fun _ => ⟨[], LF, []⟩, pI, pO, posLE_of_fst_eq (by omega), hpIO, ?_, hinv, hout⟩
    exact Or.inl (by simp; omega)
  | succ m ihm =>
    obtain ⟨ν, L, hObt_m⟩ := ihm (Nat.le_of_succ_le hℓ)
    have hlr_eq : SigComp.layerRound τ₀ tN tC (m + 1) = τ₀ + tN + m * tC := by
      simp [SigComp.layerRound]
    have hle_m : m * tC ≤ d * tC := Nat.mul_le_mul_right tC (Nat.le_of_succ_le hℓ)
    have hle_tref : (m + 1) * tC ≤ d * tC := Nat.mul_le_mul_right tC hℓ
    have hth_lr : CorrectThrough tr τ₀ i (SigComp.layerRound τ₀ tN tC (m + 1)) :=
      correctThrough_mono hth (by simp [SigComp.tref, hlr_eq]; omega)
    obtain ⟨pI, hpI1, hObt_pI, hinv⟩ :=
      (hM.refresh i hi).layer_exists (m + 1) ν L (Nat.succ_pos m) hℓ hth_lr
        (hlr_eq.symm ▸ hObt_m)
    have hcorrI : CorrectAt tr τ₀ i pI :=
      correctAt_of_through hth_lr (by omega) (by omega)
    have hthC : CorrectThrough tr τ₀ i (pI.1 + tC) := by
      refine correctThrough_mono hth ?_
      have : pI.1 + tC = τ₀ + tN + (m + 1) * tC := by
        rw [hpI1, hlr_eq]
        ring
      simp [SigComp.tref]
      omega
    obtain ⟨pO, V, ρ, π, hpIO, hpO1, hout⟩ :=
      hM.commitment.termination i hi pI (m + 1) _ hcorrI hinv hthC
    let L' : ℕ → SigComp.LayerOut := fun x => if x = m + 1 then ⟨V, ρ, π⟩ else L x
    have hL'_eq : ∀ x ≤ m, L' x = L x := by
      intro x hx
      simp [L', show x ≠ m + 1 by omega]
    have hObt_pI' : SigComp.Obtained tr τ₀ n g i ν L' m pI :=
      obtained_congr hL'_eq hObt_pI
    have href' : SigComp.refVal n g i ν L' m = SigComp.refVal n g i ν L m :=
      refVal_congr hL'_eq
    have hL'_succ : L' (m + 1) = ⟨V, ρ, π⟩ := by simp [L']
    have hpO_lt : PosLT pO (τ₀ + tN + (m + 1) * tC + 1, 0) := by
      refine Or.inl ?_
      have : pI.1 + tC = τ₀ + tN + (m + 1) * tC := by
        rw [hpI1, hlr_eq]
        ring
      simp
      omega
    exact ⟨ν, L', pI, pO, hpIO, hpO_lt, href' ▸ hinv, hL'_succ ▸ hout, hObt_pI'⟩

end Aux31

theorem solution (n : ℕ) :
    (sigComp n).CorrectA2 n ∧
    ∀ (d : ℕ) (g : Term) (τ₀ tN tC : ℕ) (tr : Execution), SigComp.Sec31 n d g τ₀ tN tC tr →
      (sigComp n).RefreshCorrectIn n d g τ₀ tr ∧
      (∀ i < n, CorrectThrough tr τ₀ i (τ₀ + SigComp.tref tN tC d) →
        ∃ (p : Pos) (R : List Term) (A : List FwdRecord), p.1 = τ₀ + SigComp.tref tN tC d ∧
          evAt tr p = some (Event.refreshOut i g R A) ∧ (sigComp n).wellFormedLists d R A) ∧
      (∀ j < n, ∀ k < n, ∀ (pj pk : Pos) (Rj Rk : List Term) (Aj Ak : List FwdRecord),
        CorrectAt tr τ₀ j pj → evAt tr pj = some (Event.refreshOut j g Rj Aj) →
        CorrectAt tr τ₀ k pk → evAt tr pk = some (Event.refreshOut k g Rk Ak) →
        ∀ q : ℕ, 1 ≤ q → q ≤ d →
          ((sigComp n).Compat Rj Aj q k Rk ↔ SigComp.Delivered tr τ₀ g q k j)) := by
  refine ⟨⟨Aux31.localCorrectness n, Aux31.forwardability n, Aux31.rejection n⟩, ?_⟩
  intro d g τ₀ tN tC tr hM
  have hrefCorr := Aux31.refreshCorrectIn hM
  refine ⟨hrefCorr, ?_, ?_⟩
  · intro i hi hth
    obtain ⟨ν, L, hObt_d⟩ := Aux31.obtained_through_layers hM hi hth d (le_refl d)
    have htref_eq : τ₀ + tN + d * tC = τ₀ + SigComp.tref tN tC d := by
      simp [SigComp.tref]; omega
    obtain ⟨p, hp1, _, hout⟩ :=
      (hM.refresh i hi).out_exists ν L hth (htref_eq ▸ hObt_d)
    have hcorr_p : CorrectAt tr τ₀ i p :=
      Aux31.correctAt_of_through hth (by omega) (by omega)
    exact ⟨p, _, _, hp1, hout, hrefCorr i hi p _ _ hcorr_p hout⟩
  · intro j hj k hk pj pk Rj Rk Aj Ak hcorr_j hout_j hcorr_k hout_k q hq1 hqd
    have hwf_j := hrefCorr j hj pj Rj Aj hcorr_j hout_j
    obtain ⟨_, νj, Lj, hObt_j, rfl, rfl⟩ := (hM.refresh j hj).out_step pj Rj Aj hcorr_j hout_j
    obtain ⟨_, νk, Lk, hObt_k, rfl, rfl⟩ := (hM.refresh k hk).out_step pk Rk Ak hcorr_k hout_k
    obtain ⟨pIj, pOj, hτIj, hpIjOj, hpOjpj, _, hout_oj⟩ :=
      Aux31.obtained_layer hObt_j hq1 hqd
    obtain ⟨pIk, _, hτIk, hpIkOk, hpOkpk, hinv_k, _⟩ :=
      Aux31.obtained_layer hObt_k hq1 hqd
    have hcorr_pOj : CorrectAt tr τ₀ j pOj :=
      Aux31.correctAt_mono hcorr_j
        (Aux31.posLE_trans hτIj (Aux31.posLE_of_posLT hpIjOj))
        (Aux31.posLE_of_posLT hpOjpj)
    have hcorr_pIk : CorrectAt tr τ₀ k pIk :=
      Aux31.correctAt_mono hcorr_k hτIk
        (Aux31.posLE_of_posLT (Aux31.posLT_trans hpIkOk hpOkpk))
    have hRjq : (SigComp.listsR n g j νj Lj d)[q]? = some (Lj q).ρ := by
      have hqlt : q < d + 1 := by omega
      obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
      simp [SigComp.listsR, SigComp.refVal, hqlt]
    have hAjq : (SigComp.listsA Lj d)[q - 1]? = some ((Lj q).V, (Lj q).π) := by
      have hqlt : q - 1 < d := by omega
      have hqeq : q - 1 + 1 = q := by omega
      simp [SigComp.listsA, hqlt, hqeq]
    have hRkq : (SigComp.listsR n g k νk Lk d)[q - 1]? = some (SigComp.refVal n g k νk Lk (q - 1)) := by
      have hqlt : q - 1 < d + 1 := by omega
      simp [SigComp.listsR, hqlt]
    constructor
    · rintro ⟨_, r, a, v, _, hRjq', hAjq', _, ha1, _, hRkq', _⟩
      rw [hAjq] at hAjq'
      rw [hRkq] at hRkq'
      injection hAjq' with ha_eq
      injection hRkq' with hv_eq
      rw [← ha_eq] at ha1
      rw [← hv_eq] at ha1
      exact ⟨pIk, pOj, _, (Lj q).V, (Lj q).ρ, (Lj q).π, hcorr_pIk, hinv_k, hcorr_pOj, hout_oj, ha1⟩
    · rintro ⟨pk', pj', vk, V, ρ, π, hcorr_k', hinv_k', hcorr_j', hout_j', hVk⟩
      have hpj_eq : pOj = pj' :=
        hM.commitment.single_output j hj pOj pj' q (Lj q).V V (Lj q).ρ ρ (Lj q).π π
          hcorr_pOj hcorr_j' hout_oj hout_j'
      subst hpj_eq
      rw [hout_oj] at hout_j'
      injection hout_j' with hev_j
      injection hev_j with _ _ _ hV_eq hρ_eq hπ_eq
      subst hV_eq; subst hρ_eq; subst hπ_eq
      have hpk_eq : pIk = pk' :=
        (hM.refresh k hk).layer_unique pIk pk' q _ vk hcorr_pIk hcorr_k' hinv_k hinv_k'
      subst hpk_eq
      rw [hinv_k] at hinv_k'
      injection hinv_k' with hev_k
      injection hev_k with _ _ _ hvk_eq
      subst hvk_eq
      have hwf_rec : SigComp.WFRecord n q (Lj q).ρ ((Lj q).V, (Lj q).π) :=
        hwf_j.2.2 q (Lj q).ρ ((Lj q).V, (Lj q).π) hq1 hRjq hAjq
      have hv_root : IsRoot n (q - 1) (SigComp.refVal n g k νk Lk (q - 1)) :=
        hwf_rec.2.2.1 k _ hVk
      obtain ⟨πk, hπk, hopk⟩ := hwf_rec.2.2.2 k _ hVk
      exact ⟨by omega, (Lj q).ρ, ((Lj q).V, (Lj q).π), _, πk,
        hRjq, hAjq, hwf_rec, hVk, hπk, hRkq, hv_root, hopk⟩
