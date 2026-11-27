-- Prove2me | solution 1 for FakeUserRanking.FORC.Supplement.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:25:58.092308+00:00
-- url     : https://prove2.me/submissions/cf509a49-0ba6-4095-bbf3-371b3883af0c

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_Supplement_FAR
import Definitions.Def_FakeUserRanking_FORC_Supplement_EventE
import Definitions.Def_FakeUserRanking_FORC_Supplement_Gamma

open FakeUserRanking
open FakeUserRanking.FORC
open FakeUserRanking.FORC.Supplement

/-- Lemma 4 (Necessary Conditions for an Incorrect Ordering), p. 22, pathwise: on every trajectory
in `E`, if the ranking FAR displays in Lean round `t` (paper round `t + 1`) puts product `i` at a
better position than product `j < i` (paper: `i > j`), then some product `k ≤ j` has (a) no edge
`(i, k)` in the graph after paper round `t`, (b) `η_{i,t} ≤ η_{k,t}` and (c) `η_{i,t} < γ_{k,i}`. -/
theorem solution (n T F : ℕ) (hn : 1 ≤ n) (hT : 1 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (tb : List (Fin 1 × Obs n) → Finset (Fin n) → Fin n)
    (htb : ∀ h S, S.Nonempty → tb h S ∈ S)
    (fb : List (Fin 1 × Obs n) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n 1) (hE : eventE inst T F tb fb τ)
    (t : Fin T) (j i : Fin n) (hji : j < i)
    (hord : (ranking (far n T F tb fb) τ t).symm i < (ranking (far n T F tb fb) τ t).symm j) :
    ∃ k : Fin n, k ≤ j ∧
      (i, k) ∉ (farStateAt n T F tb fb τ t).graph ∧
      (farStateAt n T F tb fb τ t).cnt i ≤ (farStateAt n T F tb fb τ t).cnt k ∧
      ((farStateAt n T F tb fb τ t).cnt i : ℝ) < gamma13 T F inst k i := by
        classical
        have hA : ∀ (h : List (Fin 1 × Obs n)) (acc : List (Fin 1 × Obs n) × FarState n),
            (h.foldl (fun (acc : List (Fin 1 × Obs n) × FarState n) (x : Fin 1 × Obs n) =>
              (acc.1 ++ [x], acc.2.update n T F (farRank tb fb acc.1 acc.2) x.2)) acc).1 = acc.1 ++ h := by
          intro h
          induction h with
          | nil => intro acc; simp
          | cons x h ih => intro acc; simp [List.foldl_cons, ih]
        have hB : ∀ (h : List (Fin 1 × Obs n)) (x : Fin 1 × Obs n),
            farState n T F tb fb (h ++ [x]) =
              (farState n T F tb fb h).update n T F (farRank tb fb h (farState n T F tb fb h)) x.2 := by
          intro h x
          unfold farState
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hA]
          simp
        have hC : ∀ s (hs : s < T), algHist τ (s + 1) = algHist τ s ++ [((τ ⟨s, hs⟩).1, (τ ⟨s, hs⟩).2.2)] := by
          intro s hs
          unfold algHist
          rw [List.take_add_one]
          simp [hs]
        have hUpd : ∀ (st : FarState n) π o (e : Fin n × Fin n),
            e ∈ (st.update n T F π o).graph ↔ e ∈ st.graph ∨ farEdgeCond n T F (st.update n T F π o) e.1 e.2 := by
          intro st π o e
          simp only [FarState.update, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          rfl
        have hSucc : ∀ s, s < T → ∀ e : Fin n × Fin n, e ∈ (farStateAt n T F tb fb τ (s+1)).graph ↔
            e ∈ (farStateAt n T F tb fb τ s).graph ∨ farEdgeCond n T F (farStateAt n T F tb fb τ (s+1)) e.1 e.2 := by
          intro s hs e
          unfold farStateAt
          rw [hC s hs, hB]
          exact hUpd _ _ _ e
        have h0 : farStateAt n T F tb fb τ 0 = FarState.init := by
          simp [farStateAt, algHist, farState]
        set Lg := Real.log (2 * n * T / farDelta n T) with hLg
        have hLpos : 0 < Lg := by
          rw [hLg]
          apply Real.log_pos
          have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
          have hT' : (1:ℝ) ≤ T := by exact_mod_cast hT
          unfold farDelta
          rw [div_div_eq_mul_div, div_one]
          nlinarith [mul_le_mul hn' hT' zero_le_one (by linarith)]
        have hRadPos : ∀ (st : FarState n) (a : Fin n), 0 < st.cnt a → 0 < farRadius n T F st a := by
          intro st a ha
          unfold farRadius
          have hc : (0:ℝ) < st.cnt a := by exact_mod_cast ha
          have h1 : 0 < Real.sqrt (Lg / st.cnt a) := Real.sqrt_pos.2 (div_pos hLpos hc)
          have h2 : 0 ≤ (F:ℝ) / st.cnt a := by positivity
          rw [← hLg]; linarith
        have hEdge : ∀ s, 1 ≤ s → s ≤ T → ∀ a b : Fin n,
            farEdgeCond n T F (farStateAt n T F tb fb τ s) a b → b < a := by
          intro s hs1 hs2 a b hc
          obtain ⟨ha, hb, hineq⟩ := hc
          have Ea := hE s hs1 hs2 a
          have Eb := hE s hs1 hs2 b
          have wa : farWindow n T F (farStateAt n T F tb fb τ s) a = farRadius n T F (farStateAt n T F tb fb τ s) a := by
            unfold farWindow; rw [if_neg (Nat.pos_iff_ne_zero.1 ha)]
          have wb : farWindow n T F (farStateAt n T F tb fb τ s) b = farRadius n T F (farStateAt n T F tb fb τ s) b := by
            unfold farWindow; rw [if_neg (Nat.pos_iff_ne_zero.1 hb)]
          rw [wa] at Ea; rw [wb] at Eb
          have hra := hRadPos _ a ha
          have hrb := hRadPos _ b hb
          have hab : a ≠ b := by
            rintro rfl; linarith
          have hle : inst.μ a ≤ inst.μ b := by linarith [Ea.2, Eb.1]
          rcases lt_trichotomy a b with h | h | h
          · have := hμ h; linarith
          · exact absurd h hab
          · exact h
        have hDown : ∀ s, s ≤ T → ∀ a b : Fin n, (a, b) ∈ (farStateAt n T F tb fb τ s).graph → b < a := by
          intro s
          induction s with
          | zero => intro _ a b h; rw [h0] at h; simp [FarState.init] at h
          | succ s ih =>
            intro hs a b h
            rcases (hSucc s (by omega) (a, b)).1 h with h | h
            · exact ih (by omega) a b h
            · exact hEdge (s+1) (by omega) hs a b h
        set G := (farStateAt n T F tb fb τ t).graph with hG
        set η := (farStateAt n T F tb fb τ t).cnt with hη
        set tb' := tb (algHist τ t) with htb'
        have hDt : ∀ a b : Fin n, (a, b) ∈ G → b < a := hDown t (le_of_lt t.2)
        have hPeel : ∀ m (S : Finset (Fin n)), S.card = m → ∃ l, peel tb' η G m S = some l ∧ l.Nodup ∧
            (∀ x, x ∈ l ↔ x ∈ S) ∧ l.length = m ∧
            ∀ p q (hpq : p < q) (hq : q < l.length), ∃ k, k ≤ l[q] ∧ (l[p], k) ∉ G ∧ η l[p] ≤ η k := by
          intro m
          induction m with
          | zero =>
            intro S hS
            rw [Finset.card_eq_zero] at hS
            subst hS
            refine ⟨[], rfl, List.nodup_nil, by simp, rfl, ?_⟩
            intro p q hpq hq; simp at hq
          | succ m ih =>
            intro S hS
            have hne : S.Nonempty := by rw [← Finset.card_pos, hS]; omega
            set cands := S.filter (fun x => ∀ y ∈ S, (x, y) ∉ G) with hcands
            set best := cands.filter (fun x => ∀ y ∈ cands, η x ≤ η y) with hbest
            have hk0 : S.min' hne ∈ cands := by
              rw [hcands, Finset.mem_filter]
              refine ⟨Finset.min'_mem S hne, ?_⟩
              intro y hy hyG
              have := hDt _ _ hyG
              have := Finset.min'_le S y hy
              exact absurd this (not_le.2 ‹_›)
            have hbne : best.Nonempty := by
              obtain ⟨x, hx, hxm⟩ := Finset.exists_min_image cands η ⟨_, hk0⟩
              exact ⟨x, by rw [hbest, Finset.mem_filter]; exact ⟨hx, hxm⟩⟩
            have hx : tb' best ∈ best := htb _ _ hbne
            set x := tb' best with hxdef
            have hxc : x ∈ cands := (Finset.mem_filter.1 hx).1
            have hxS : x ∈ S := (Finset.mem_filter.1 hxc).1
            obtain ⟨l', hl'1, hl'2, hl'3, hl'4, hl'5⟩ := ih (S.erase x) (by rw [Finset.card_erase_of_mem hxS, hS]; rfl)
            have hpeq : peel tb' η G (m+1) S = some (x :: l') := by
              rw [peel]
              show (if x ∈ best then (peel tb' η G m (S.erase x)).map (List.cons x) else none) = _
              rw [if_pos hx, hl'1]; rfl
            refine ⟨x :: l', hpeq, ?_, ?_, ?_, ?_⟩
            · refine List.nodup_cons.2 ⟨?_, hl'2⟩
              intro hm
              have := (hl'3 x).1 hm
              simp at this
            · intro y
              rw [List.mem_cons, hl'3 y, Finset.mem_erase]
              constructor
              · rintro (rfl | ⟨_, h⟩)
                · exact hxS
                · exact h
              · intro hy
                by_cases hyx : y = x
                · left; exact hyx
                · right; exact ⟨hyx, hy⟩
            · simp [hl'4]
            · intro p q hpq hq
              cases q with
              | zero => omega
              | succ q =>
                cases p with
                | zero =>
                  have hq' : q < l'.length := by simpa using hq
                  have hyS : l'[q] ∈ S := Finset.mem_of_mem_erase ((hl'3 _).1 (List.getElem_mem hq'))
                  refine ⟨S.min' hne, ?_, ?_, ?_⟩
                  · simpa using Finset.min'_le S _ hyS
                  · simp only [List.getElem_cons_zero]
                    exact (Finset.mem_filter.1 hxc).2 _ (Finset.min'_mem S hne)
                  · simp only [List.getElem_cons_zero]
                    exact (Finset.mem_filter.1 hx).2 _ hk0
                | succ p =>
                  have hq' : q < l'.length := by simpa using hq
                  obtain ⟨k, hk1, hk2, hk3⟩ := hl'5 p q (by omega) hq'
                  exact ⟨k, by simpa using hk1, by simpa using hk2, by simpa using hk3⟩
        have hNoCyc : ¬ HasCycle G := by
          rintro ⟨a, ha⟩
          have key : ∀ x y, Relation.TransGen (fun a b => (a, b) ∈ G) x y → y < x := by
            intro x y h
            induction h with
            | single h => exact hDt _ _ h
            | tail _ h ih => exact lt_trans (hDt _ _ h) ih
          exact lt_irrefl _ (key a a ha)
        obtain ⟨l, hl1, hl2, hl3, hl4, hl5⟩ := hPeel n Finset.univ (by simp)
        have hrank : ranking (far n T F tb fb) τ t = listPerm l hl2 (fun x => (hl3 x).2 (Finset.mem_univ x)) hl4 := by
          show graphRankSelect tb' (fb (algHist τ t)) η G = _
          unfold graphRankSelect
          rw [if_neg hNoCyc, hl1]
          simp only
          rw [dif_pos ⟨hl2, fun x => (hl3 x).2 (Finset.mem_univ x), hl4⟩]
        rw [hrank] at hord
        set P := listPerm l hl2 (fun x => (hl3 x).2 (Finset.mem_univ x)) hl4 with hP
        have hPapp : ∀ a : Fin n, P a = l[a.val]'(by rw [hl4]; exact a.2) := by
          intro a
          rw [hP]; unfold listPerm
          simp [List.Nodup.getEquivOfForallMemList_apply]
        have hi : l[(P.symm i).val]'(by rw [hl4]; exact (P.symm i).2) = i := by
          rw [← hPapp]; simp
        have hj : l[(P.symm j).val]'(by rw [hl4]; exact (P.symm j).2) = j := by
          rw [← hPapp]; simp
        obtain ⟨k, hk1, hk2, hk3⟩ := hl5 (P.symm i).val (P.symm j).val hord (by rw [hl4]; exact (P.symm j).2)
        rw [hi] at hk2 hk3
        rw [hj] at hk1
        refine ⟨k, hk1, hk2, hk3, ?_⟩
        have hki : k < i := lt_of_le_of_lt hk1 hji
        have hΔ : 0 < inst.μ k - inst.μ i := by linarith [hμ hki]
        set Δ := inst.μ k - inst.μ i with hΔdef
        have hgam : gamma13 T F inst k i = max (64 * Lg / Δ ^ 2) (8 * (F : ℝ) / Δ) := rfl
        rw [hgam]
        by_contra hcon
        push Not at hcon
        have hg1 : 64 * Lg / Δ ^ 2 ≤ (η i : ℝ) := le_trans (le_max_left _ _) hcon
        have hg2 : 8 * (F : ℝ) / Δ ≤ (η i : ℝ) := le_trans (le_max_right _ _) hcon
        have hgpos : 0 < 64 * Lg / Δ ^ 2 := by positivity
        have hik : (η i : ℝ) ≤ η k := by exact_mod_cast hk3
        have hrad : ∀ a : Fin n, 64 * Lg / Δ ^ 2 ≤ (η a : ℝ) → 8 * (F : ℝ) / Δ ≤ (η a : ℝ) →
            farRadius n T F (farStateAt n T F tb fb τ t) a ≤ Δ / 4 := by
          intro a h1 h2
          have hc : (0:ℝ) < η a := lt_of_lt_of_le hgpos h1
          unfold farRadius
          rw [← hLg]
          change Real.sqrt (Lg / (η a : ℝ)) + (F:ℝ) / (η a : ℝ) ≤ Δ / 4
          have hΔ2 : 0 < Δ ^ 2 := by positivity
          rw [div_le_iff₀ hΔ2] at h1
          rw [div_le_iff₀ hΔ] at h2
          have s1 : Real.sqrt (Lg / (η a : ℝ)) ≤ Δ / 8 := by
            rw [Real.sqrt_le_iff]
            refine ⟨by positivity, ?_⟩
            rw [div_le_iff₀ hc]; nlinarith
          have s2 : (F:ℝ) / (η a : ℝ) ≤ Δ / 8 := by
            rw [div_le_iff₀ hc]; nlinarith
          linarith
        have hk' : 64 * Lg / Δ ^ 2 ≤ (η k : ℝ) := le_trans hg1 hik
        have hk'' : 8 * (F : ℝ) / Δ ≤ (η k : ℝ) := le_trans hg2 hik
        have hipos : 0 < η i := by
          have : (0:ℝ) < η i := lt_of_lt_of_le hgpos hg1
          exact_mod_cast this
        obtain ⟨tv, ht⟩ := t
        cases tv with
        | zero =>
          have : η i = 0 := by rw [hη]; simp only [h0, FarState.init]
          omega
        | succ s =>
          apply hk2
          rw [hG, hSucc s (by omega)]
          right
          have Ei := hE (s+1) (by omega) (by omega) i
          have Ek := hE (s+1) (by omega) (by omega) k
          have hkpos : 0 < η k := lt_of_lt_of_le hipos hk3
          have wi : farWindow n T F (farStateAt n T F tb fb τ (s+1)) i = farRadius n T F (farStateAt n T F tb fb τ (s+1)) i := by
            unfold farWindow; rw [if_neg (Nat.pos_iff_ne_zero.1 hipos)]
          have wk : farWindow n T F (farStateAt n T F tb fb τ (s+1)) k = farRadius n T F (farStateAt n T F tb fb τ (s+1)) k := by
            unfold farWindow; rw [if_neg (Nat.pos_iff_ne_zero.1 hkpos)]
          rw [wi] at Ei; rw [wk] at Ek
          have ri := hrad i hg1 hg2
          have rk := hrad k hk' hk''
          refine ⟨hipos, hkpos, ?_⟩
          linarith [Ei.1, Ek.2]
