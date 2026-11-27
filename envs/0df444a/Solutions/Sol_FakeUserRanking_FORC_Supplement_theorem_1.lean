-- Prove2me | solution 1 for FakeUserRanking.FORC.Supplement.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:25:01.073824+00:00
-- url     : https://prove2.me/submissions/60273e2e-da06-4569-9e4c-3bb5609b7743

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Supplement_UCB

open FakeUserRanking
open FakeUserRanking.FORC
open FakeUserRanking.FORC.Supplement

/-- Theorem 1 (Non-Robustness of UCB to Fake Users), p. 14: there is a two-product instance with
`μ₁ > μ₂` and absolute constants `C`, `c > 0`, `T₀` such that for every horizon `T ≥ T₀` and every
tie-breaking rule of UCB, some deterministic adaptive fake-user policy with fakeness budget
`F ≤ C (log T)²` makes UCB's regret at least `c T`. -/
theorem solution :
    ∃ inst : Instance 2, StrictAnti inst.μ ∧
    ∃ C c T₀ : ℝ, 0 < c ∧ ∀ T : ℕ, T₀ ≤ T →
      ∀ tb : List (Fin 1 × Obs 2) → Fin 2,
      ∃ F : ℕ, (F : ℝ) ≤ C * Real.log T ^ 2 ∧
      ∃ a : List (PubStep 2) → Action 2,
        WithinBudget F (fun h => PMF.pure (a h)) ∧
        c * T ≤ regret inst (fun h => PMF.pure (a h)) (ucb T tb) T := by
          set_option maxHeartbeats 4000000 in
          let inst : Instance 2 := ⟨![1, 1/2], by intro i; fin_cases i <;> norm_num, ![1, 1],
            by intro i; fin_cases i <;> norm_num⟩
          have hanti : StrictAnti inst.μ := by
            intro i j hij
            fin_cases i <;> fin_cases j <;> simp_all [inst] <;> norm_num
          refine ⟨inst, hanti, 34, 1/8, 40000, by norm_num, ?_⟩
          intro T hT tb
          have hT1 : (1 : ℝ) ≤ T := by linarith
          set L := Real.log T with hL
          have hL1 : 1 ≤ L := by
            rw [hL]
            have : Real.exp 1 ≤ (T : ℝ) := by
              have := Real.exp_one_lt_d9; linarith
            calc (1:ℝ) = Real.log (Real.exp 1) := by simp
              _ ≤ Real.log T := Real.log_le_log (Real.exp_pos 1) this
          set f : ℕ := ⌈16 * L⌉₊ with hf
          have hf1 : 16 * L ≤ f := Nat.le_ceil _
          have hf2 : (f : ℝ) < 16 * L + 1 := Nat.ceil_lt_add_one (by linarith)
          let act : ℕ → Action 2 := fun k =>
            if k < f then some (Sum.inr 1) else if k < 2 * f then some (Sum.inl 1) else none
          let a : List (PubStep 2) → Action 2 := fun h => act h.length
          refine ⟨2 * f, ?_, a, ?_, ?_⟩
          · push_cast; nlinarith
          · intro h hh
            have hlen : 2 * f ≤ h.length := le_trans hh (List.length_filter_le _ _)
            simp only [a, act]
            rw [if_neg (by omega), if_neg (by omega)]
          -- main estimate
          set P : Adversary 2 := fun h => PMF.pure (a h) with hP
          have H1 : ∀ (N : ℕ) (τ : Fin N → Step 2 1) (x : Step 2 1) (s : ℕ), s ≤ N →
              algHist (Fin.snoc τ x : Fin (N+1) → Step 2 1) s = algHist τ s := by
            intro N τ x s hs
            unfold algHist
            rw [List.ofFn_succ_last]
            simp only [Fin.snoc_castSucc]
            rw [List.take_append_of_le_length (by simpa using hs)]
          have H2 : ∀ (A : Alg 2 1) (N : ℕ) (τ : Fin N → Step 2 1) (x : Step 2 1) (s : ℕ), s ≤ N →
              pubHist A (Fin.snoc τ x : Fin (N+1) → Step 2 1) s = pubHist A τ s := by
            intro A N τ x s hs
            unfold pubHist
            rw [List.ofFn_succ_last]
            rw [List.take_append_of_le_length (by simpa using hs)]
            congr 2
            funext i
            simp only [ranking, Fin.snoc_castSucc, Fin.val_castSucc]
            rw [H1 N τ x i i.2.le]
          have H3 : ∀ (A : Alg 2 1) (N : ℕ) (τ : Fin N → Step 2 1) (x : Step 2 1) (i : Fin N),
              stepW inst P A (Fin.snoc τ x : Fin (N+1) → Step 2 1) i.castSucc = stepW inst P A τ i := by
            intro A N τ x i
            simp only [stepW, ranking, Fin.snoc_castSucc, Fin.val_castSucc]
            rw [H1 N τ x i i.2.le, H2 A N τ x i i.2.le]
          have Hlen : ∀ (A : Alg 2 1) (N : ℕ) (τ : Fin N → Step 2 1), (pubHist A τ N).length = N := by
            intro A N τ; simp [pubHist]
          have Hfull : ∀ (N : ℕ) (τ : Fin N → Step 2 1) (x : Step 2 1),
              algHist (Fin.snoc τ x : Fin (N+1) → Step 2 1) (N+1) = algHist τ N ++ [(x.1, x.2.2)] := by
            intro N τ x
            unfold algHist
            rw [List.ofFn_succ_last]
            simp [Fin.snoc_castSucc, Fin.snoc_last]
            rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp)]
          have Hlast : ∀ (A : Alg 2 1) (N : ℕ) (τ : Fin N → Step 2 1) (x : Step 2 1),
              stepW inst P A (Fin.snoc τ x : Fin (N+1) → Step 2 1) (Fin.last N) =
                A.w (algHist τ N) x.1 * (P (pubHist A τ N) x.2.1).toReal *
                  obsW inst (A.rank (algHist τ N) x.1) x.2.1 x.2.2 := by
            intro A N τ x
            simp only [stepW, ranking, Fin.snoc_last, Fin.val_last]
            rw [H1 N τ x N le_rfl, H2 A N τ x N le_rfl]
          have Hchain : ∀ (A : Alg 2 1) (N : ℕ) (G : (Fin (N+1) → Step 2 1) → ℝ),
              expect inst P A (N+1) G = ∑ τ : Fin N → Step 2 1, trajW inst P A N τ *
                ∑ x : Step 2 1, stepW inst P A (Fin.snoc τ x : Fin (N+1) → Step 2 1) (Fin.last N) *
                  G (Fin.snoc τ x) := by
            intro A N G
            unfold expect
            rw [← (Fin.snocEquiv (fun _ => Step 2 1)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
            refine Finset.sum_congr rfl (fun τ _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun x _ => ?_)
            simp only [Fin.snocEquiv, Equiv.coe_fn_mk, trajW]
            rw [Fin.prod_univ_castSucc]
            simp only [H3]
            ring
          have Hker : ∀ (A : Alg 2 1), (∀ h l, A.w h l = 1) → ∀ N (G : (Fin (N+1) → Step 2 1) → ℝ),
              expect inst P A (N+1) G = ∑ τ : Fin N → Step 2 1, trajW inst P A N τ *
                ∑ o : Obs 2, obsW inst (A.rank (algHist τ N) 0) (act N) o *
                  G (Fin.snoc τ ((0 : Fin 1), act N, o)) := by
            intro A hw N G
            rw [Hchain]
            refine Finset.sum_congr rfl (fun τ _ => ?_)
            refine congrArg (trajW inst P A N τ * ·) ?_
            simp only [Hlast, hw, one_mul]
            simp only [hP, a, Hlen]
            rw [Fintype.sum_prod_type, Fintype.sum_unique]
            rw [Fintype.sum_prod_type]
            simp only [PMF.pure_apply]
            rw [Finset.sum_eq_single (act N)]
            · simp [Fin.default_eq_zero]
            · intro b _ hb; simp [hb]
            · simp
          have Hrw : ∀ N (τ : Fin N → Step 2 1) (x : Step 2 1),
              reward (Fin.snoc τ x : Fin (N+1) → Step 2 1) = reward τ + realClick x := by
            intro N τ x
            simp only [reward, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
          have Hreach : ∀ π : Equiv.Perm (Fin 2), reach inst π 0 = 1 ∧ reach inst π 1 = 0 := by
            intro π
            constructor
            · simp only [reach]; rw [show Finset.Iio (0 : Fin 2) = ∅ by decide]; simp
            · simp only [reach]
              rw [show Finset.Iio (1 : Fin 2) = {0} by decide]
              simp [inst]
          have HrealSum : ∀ (π : Equiv.Perm (Fin 2)) (g : Obs 2 → ℝ), ∑ o : Obs 2, realW inst π o * g o =
              inst.μ (π 0) * g (0, true) + (1 - inst.μ (π 0)) * g (0, false) := by
            intro π g
            rw [Fintype.sum_prod_type, Fin.sum_univ_two]
            simp only [Fintype.sum_bool, realW, (Hreach π).1, (Hreach π).2]
            simp [inst]
          have Hobs1 : ∀ (π : Equiv.Perm (Fin 2)) (b : Action 2), ∑ o : Obs 2, obsW inst π b o = 1 := by
            intro π b
            rcases b with _ | s
            · have := HrealSum π (fun _ => 1); simp only [mul_one] at this
              simp only [obsW]; rw [this]; ring
            · simp [obsW]
          have Eopt' : ∀ N, expect inst P (optAlg 2) N (fun _ => 1) = 1 ∧
              expect inst P (optAlg 2) N reward = ((N - 2 * f : ℕ) : ℝ) := by
            intro N
            induction N with
            | zero => simp [expect, trajW, reward]
            | succ N ih =>
              have hw : ∀ h l, (optAlg 2).w h l = 1 := fun _ _ => rfl
              constructor
              · rw [Hker _ hw]
                have h1 := ih.1; unfold expect at h1; simp only [mul_one] at h1
                simp only [mul_one, Hobs1]; exact h1
              · rw [Hker _ hw]
                simp only [Hrw, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
                simp only [Hobs1, one_mul]
                have hc : ∀ τ : Fin N → Step 2 1, ∑ o : Obs 2, obsW inst ((optAlg 2).rank (algHist τ N) 0)
                    (act N) o * realClick ((0 : Fin 1), act N, o) = if 2 * f ≤ N then 1 else 0 := by
                  intro τ
                  by_cases hN : 2 * f ≤ N
                  · have : act N = none := by simp only [act]; rw [if_neg (by omega), if_neg (by omega)]
                    rw [this, if_pos hN]
                    simp only [obsW]
                    rw [HrealSum]
                    simp [realClick, optAlg, inst]
                  · rw [if_neg hN]
                    apply Finset.sum_eq_zero
                    intro o _
                    have : act N ≠ none := by
                      simp only [act]; split_ifs <;> simp_all <;> omega
                    simp [realClick, this]
                simp only [hc]
                rw [← Finset.sum_mul]
                have h1 := ih.1; unfold expect at h1; simp only [mul_one] at h1
                rw [h1]
                have h2 := ih.2; unfold expect at h2
                rw [h2, one_mul]
                split_ifs with hN
                · rw [show N + 1 - 2 * f = N - 2 * f + 1 by omega]; push_cast; ring
                · rw [show N + 1 - 2 * f = N - 2 * f by omega]; ring
          have Eopt : ∀ N, 2 * f ≤ N → expect inst P (optAlg 2) N reward = (N : ℝ) - 2 * f := by
            intro N hN; rw [(Eopt' N).2, Nat.cast_sub hN]; push_cast; ring
          have Eucb : ∀ N, 2 * f ≤ N →
              expect inst P (ucb T tb) N reward ≤ (13/18 : ℝ) * ((N : ℝ) - 2 * f) := by
            classical
            have hw1 : ∀ h l, (ucb T tb).w h l = 1 := fun _ _ => rfl
            have Etot : ∀ N, expect inst P (ucb T tb) N (fun _ => 1) = 1 := by
              intro N
              induction N with
              | zero => simp [expect, trajW]
              | succ N ih =>
                rw [Hker _ hw1]
                unfold expect at ih; simp only [mul_one] at ih
                simp only [mul_one, Hobs1]; exact ih
            have Hst : ∀ (h : List (Fin 1 × Obs 2)) (x : Fin 1 × Obs 2), ucbState T tb (h ++ [x]) =
                (ucbState T tb h).update (ucbRankOf T tb h (ucbState T tb h)) x.2 := by
              have key : ∀ h : List (Fin 1 × Obs 2), (h.foldl (fun (acc : List (Fin 1 × Obs 2) × UcbState)
                  (x : Fin 1 × Obs 2) => (acc.1 ++ [x], acc.2.update (ucbRankOf T tb acc.1 acc.2) x.2))
                  ([], UcbState.init)).1 = h := by
                intro h
                induction h using List.reverseRecOn with
                | nil => rfl
                | append_singleton l y ih => rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
              intro h x
              simp only [ucbState, List.foldl_append, List.foldl_cons, List.foldl_nil]
              rw [key h]
            let rk : List (Fin 1 × Obs 2) → Equiv.Perm (Fin 2) := fun h => ucbRankOf T tb h (ucbState T tb h)
            let bad : List (Fin 1 × Obs 2) → Prop := fun h =>
              ∃ j, 2 * f ≤ j ∧ j ≤ h.length ∧ rk (h.take j) 0 = 0
            let bad' : List (Fin 1 × Obs 2) → Prop := fun h =>
              ∃ j, 2 * f ≤ j ∧ j < h.length ∧ rk (h.take j) 0 = 0
            let Φ : UcbState → ℝ := fun st => (2/3 : ℝ) ^ ((4 * (st.clk 1 : ℤ)) - st.cnt 1)
            let Ψ : List (Fin 1 × Obs 2) → ℝ := fun h => if bad h then 1 else Φ (ucbState T tb h)
            let Inv : ℕ → List (Fin 1 × Obs 2) → Prop := fun N h =>
              (¬ bad' h → (ucbState T tb h).clk 0 = 0 ∧ min N f ≤ (ucbState T tb h).cnt 0) ∧
              (N ≤ 2 * f → (ucbState T tb h).cnt 1 = N ∧ (ucbState T tb h).clk 1 = N - f)
            have hf0 : 1 ≤ f := by exact_mod_cast (show (1:ℝ) ≤ f by linarith)
            have two : ∀ k : Fin 2, k ≠ 0 → k = 1 := by decide
            have two' : ∀ k : Fin 2, k ≠ 1 → k = 0 := by decide
            have htf : ∀ t : Fin 2, topFirst t 0 = t := by
              intro t; fin_cases t <;> simp [topFirst]
            have hperm : ∀ π : Equiv.Perm (Fin 2), π 0 ≠ 0 → π 0 = 1 ∧ π.symm 0 = 1 ∧ π.symm 1 = 0 := by
              intro π h
              have h0 : π 0 = 1 := two _ h
              have h1 : π 1 ≠ 1 := by
                intro h'; have := π.injective (h'.trans h0.symm); exact absurd this (by decide)
              have h1' : π 1 = 0 := two' _ h1
              refine ⟨h0, ?_, ?_⟩
              · rw [← h1', Equiv.symm_apply_apply]
              · rw [← h0, Equiv.symm_apply_apply]
            have Ktop : ∀ (h : List (Fin 1 × Obs 2)) (st : UcbState), st.clk 0 = 0 → f ≤ st.cnt 0 →
                ucbRankOf T tb h st 0 = 0 → 4 * st.clk 1 < st.cnt 1 := by
              intro h st h0 h1 hr
              by_contra hcon
              push_neg at hcon
              have hc0 : (f : ℝ) ≤ (st.cnt 0 : ℝ) := by exact_mod_cast h1
              have hidx0 : ucbIndex T st 0 = ((Real.sqrt (L / st.cnt 0) : ℝ) : WithTop ℝ) := by
                rw [ucbIndex, if_neg (by omega), h0]; simp [hL]
              have hs0 : Real.sqrt (L / st.cnt 0) ≤ 1/4 := by
                rw [show (1/4 : ℝ) = Real.sqrt (1/16) by
                  rw [show (1/16:ℝ) = (1/4)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
                apply Real.sqrt_le_sqrt
                rw [div_le_iff₀ (by linarith)]; linarith
              have hlt : ucbIndex T st 0 < ucbIndex T st 1 := by
                rw [hidx0]
                by_cases hn : st.cnt 1 = 0
                · rw [ucbIndex, if_pos hn]; exact WithTop.coe_lt_top _
                · rw [ucbIndex, if_neg hn, WithTop.coe_lt_coe]
                  have hn' : (0:ℝ) < st.cnt 1 := by exact_mod_cast Nat.pos_of_ne_zero hn
                  have hq : (1/4 : ℝ) ≤ (st.clk 1 : ℝ) / st.cnt 1 := by
                    rw [le_div_iff₀ hn']
                    have : (st.cnt 1 : ℝ) ≤ 4 * st.clk 1 := by exact_mod_cast hcon
                    linarith
                  have hp : 0 < Real.sqrt (Real.log T / st.cnt 1) :=
                    Real.sqrt_pos.mpr (div_pos (by rw [← hL]; linarith) hn')
                  rw [← hL] at hp ⊢
                  linarith
              unfold ucbRankOf at hr
              rw [htf, if_neg (not_lt.mpr hlt.le), if_pos hlt] at hr
              exact absurd hr (by decide)
            have Halen : ∀ N (τ : Fin N → Step 2 1), (algHist τ N).length = N := by
              intro N τ; simp [algHist]
            have Hinv : ∀ N (h : List (Fin 1 × Obs 2)) (l : Fin 1) (o : Obs 2), h.length = N → Inv N h →
                obsW inst (rk h) (act N) o ≠ 0 → Inv (N+1) (h ++ [(l, o)]) := by
              intro N h l o hlen hI hne
              obtain ⟨hI1, hI2⟩ := hI
              have hS : ucbState T tb (h ++ [(l,o)]) = (ucbState T tb h).update (rk h) o := Hst h (l, o)
              have hbad' : ¬ bad' (h ++ [(l,o)]) → ¬ bad' h ∧ (2 * f ≤ N → rk h 0 ≠ 0) := by
                intro hb
                constructor
                · rintro ⟨j, hj1, hj2, hj3⟩
                  apply hb
                  refine ⟨j, hj1, by simp; omega, ?_⟩
                  rwa [List.take_append_of_le_length hj2.le]
                · intro hN hr
                  apply hb
                  refine ⟨N, hN, by simp; omega, ?_⟩
                  rw [List.take_append_of_le_length hlen.ge, List.take_of_length_le hlen.le]; exact hr
              show (¬ bad' (h ++ [(l,o)]) → (ucbState T tb (h ++ [(l,o)])).clk 0 = 0 ∧
                  min (N+1) f ≤ (ucbState T tb (h ++ [(l,o)])).cnt 0) ∧
                (N + 1 ≤ 2 * f → (ucbState T tb (h ++ [(l,o)])).cnt 1 = N + 1 ∧
                  (ucbState T tb (h ++ [(l,o)])).clk 1 = N + 1 - f)
              rw [hS]
              rcases lt_or_ge N f with hN | hN
              · have hact : act N = some (Sum.inr 1) := by simp only [act]; rw [if_pos hN]
                rw [hact] at hne
                have ho : o = (1, false) := by
                  simp only [obsW, fakeObs] at hne; by_contra hc; exact hne (if_neg hc)
                subst ho
                have hnb : ¬ bad' h := by rintro ⟨j, hj1, hj2, -⟩; omega
                obtain ⟨hc0, hn0⟩ := hI1 hnb
                obtain ⟨hn1, hk1⟩ := hI2 (by omega)
                have hle : ∀ k : Fin 2, k ≤ 1 := by decide
                simp only [UcbState.update, hle, if_true, Bool.false_eq_true, false_and, if_false]
                exact ⟨fun _ => ⟨hc0, by omega⟩, fun _ => ⟨by omega, by omega⟩⟩
              rcases lt_or_ge N (2 * f) with hN2 | hN2
              · have hact : act N = some (Sum.inl 1) := by
                  simp only [act]; rw [if_neg (by omega), if_pos hN2]
                rw [hact] at hne
                have ho : o = ((rk h).symm 1, true) := by
                  simp only [obsW, fakeObs] at hne; by_contra hc; exact hne (if_neg hc)
                subst ho
                have hnb : ¬ bad' h := by rintro ⟨j, hj1, hj2, -⟩; omega
                obtain ⟨hc0, hn0⟩ := hI1 hnb
                obtain ⟨hn1, hk1⟩ := hI2 (by omega)
                have h01 : (0 : Fin 2) ≠ 1 := by decide
                simp only [UcbState.update, le_refl, if_true, Equiv.apply_symm_apply, true_and, h01,
                  if_false]
                refine ⟨fun _ => ⟨hc0, ?_⟩, fun _ => ⟨by omega, by omega⟩⟩
                split_ifs <;> omega
              · have hact : act N = none := by
                  simp only [act]; rw [if_neg (by omega), if_neg (by omega)]
                rw [hact] at hne
                rcases o with ⟨j, c⟩
                have ho1 : j = 0 := by
                  by_contra hj
                  have hj1 : j = 1 := two j hj
                  subst hj1
                  apply hne
                  cases c <;> simp [obsW, realW, (Hreach _).2]
                subst ho1
                refine ⟨fun hb => ?_, fun h' => by omega⟩
                obtain ⟨hnb, hr⟩ := hbad' hb
                obtain ⟨hc0, hn0⟩ := hI1 hnb
                obtain ⟨hπ0, hs, -⟩ := hperm _ (hr hN2)
                have h01 : (0 : Fin 2) ≠ 1 := by decide
                have h10 : ¬ ((1 : Fin 2) ≤ 0) := by decide
                simp only [UcbState.update, hs, hπ0, h10, if_false, h01, and_false]
                exact ⟨hc0, by omega⟩
            have HtrajSnoc : ∀ N (σ : Fin N → Step 2 1) x, trajW inst P (ucb T tb) (N+1) (Fin.snoc σ x) =
                trajW inst P (ucb T tb) N σ *
                  stepW inst P (ucb T tb) (Fin.snoc σ x : Fin (N+1) → Step 2 1) (Fin.last N) := by
              intro N σ x; unfold trajW; rw [Fin.prod_univ_castSucc]; simp only [H3]
            have HPN : ∀ N (σ : Fin N → Step 2 1), P (pubHist (ucb T tb) σ N) = PMF.pure (act N) := by
              intro N σ; simp only [hP, a, Hlen]
            have Hsupp : ∀ N (τ : Fin N → Step 2 1), trajW inst P (ucb T tb) N τ ≠ 0 →
                Inv N (algHist τ N) := by
              intro N
              induction N with
              | zero =>
                intro τ _
                rw [show algHist τ 0 = [] by simp [algHist]]
                exact ⟨fun _ => ⟨rfl, by simp⟩, fun _ => ⟨rfl, by simp [ucbState, UcbState.init]⟩⟩
              | succ N ih =>
                intro τ hτ
                obtain ⟨σ, x, rfl⟩ : ∃ σ x, τ = Fin.snoc σ x :=
                  ⟨Fin.init τ, τ (Fin.last N), (Fin.snoc_init_self τ).symm⟩
                rcases x with ⟨l, b, o⟩
                rw [HtrajSnoc, Hlast, HPN] at hτ
                have h1 : trajW inst P (ucb T tb) N σ ≠ 0 := left_ne_zero_of_mul hτ
                have h2 := right_ne_zero_of_mul hτ
                have h3 := right_ne_zero_of_mul (left_ne_zero_of_mul h2)
                have h4 := right_ne_zero_of_mul h2
                have hb : b = act N := by
                  by_contra hc
                  apply h3
                  simp [PMF.pure_apply, hc]
                subst hb
                rw [Hfull]
                exact Hinv N _ l o (Halen _ σ) (ih σ h1) h4
            have Hobsnn : ∀ π b o, 0 ≤ obsW inst π b o := by
              intro π b o
              rcases b with _ | s
              · rcases o with ⟨j, c⟩
                have hμ := inst.μ_mem (π 0)
                have two2 : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
                rcases two2 j with rfl | rfl <;> cases c <;>
                  simp [obsW, realW, (Hreach π).1, (Hreach π).2]
                all_goals first | exact hμ.1 | exact mul_nonneg (by linarith [hμ.2]) (inst.q_mem 0).1
              · simp only [obsW]; split_ifs <;> norm_num
            have Hnn : ∀ N (τ : Fin N → Step 2 1), 0 ≤ trajW inst P (ucb T tb) N τ := by
              intro N τ; unfold trajW; apply Finset.prod_nonneg; intro s _; unfold stepW
              exact mul_nonneg (mul_nonneg (by rw [hw1]; norm_num) ENNReal.toReal_nonneg) (Hobsnn _ _ _)
            have HΨnn : ∀ h, 0 ≤ Ψ h := by
              intro h; simp only [Ψ, Φ]; split_ifs
              · norm_num
              · exact zpow_nonneg (by norm_num) _
            have HbadExt : ∀ h x, bad h → bad (h ++ [x]) := by
              rintro h x ⟨j, hj1, hj2, hj3⟩
              exact ⟨j, hj1, by simp; omega, by rwa [List.take_append_of_le_length hj2]⟩
            have HΨstep : ∀ N (h : List (Fin 1 × Obs 2)), h.length = N → 2 * f ≤ N → Inv N h →
                ∑ o : Obs 2, obsW inst (rk h) none o * Ψ (h ++ [((0:Fin 1), o)]) ≤ Ψ h := by
              intro N h hlen hN hI
              by_cases hb : bad h
              · have : ∀ o : Obs 2, Ψ (h ++ [((0:Fin 1), o)]) = 1 := fun o => if_pos (HbadExt h _ hb)
                simp only [this, mul_one, Hobs1]
                rw [show Ψ h = 1 from if_pos hb]
              · have hnb' : ¬ bad' h := fun ⟨j, h1, h2, h3⟩ => hb ⟨j, h1, h2.le, h3⟩
                obtain ⟨hc0, hn0⟩ := hI.1 hnb'
                have hr : rk h 0 ≠ 0 := fun hr =>
                  hb ⟨N, hN, hlen.ge, by rw [List.take_of_length_le hlen.le]; exact hr⟩
                obtain ⟨hπ0, hπs, hπs1⟩ := hperm _ hr
                have hmin : min N f = f := by omega
                rw [hmin] at hn0
                set st := ucbState T tb h with hst
                have key : ∀ c : Bool, Ψ (h ++ [((0:Fin 1), ((0:Fin 2), c))]) ≤
                    Φ st * (if c then (2/3 : ℝ)^3 else 3/2) := by
                  intro c
                  have hS : ucbState T tb (h ++ [((0:Fin 1), ((0:Fin 2), c))]) =
                      st.update (rk h) (0, c) := Hst h _
                  have h10 : ¬ ((1 : Fin 2) ≤ 0) := by decide
                  have h01 : (0 : Fin 2) ≠ 1 := by decide
                  have e0c : (st.update (rk h) (0,c)).cnt 0 = st.cnt 0 := by
                    simp [UcbState.update, hπs, h10]
                  have e0k : (st.update (rk h) (0,c)).clk 0 = 0 := by
                    simp [UcbState.update, hπ0, hc0, h01]
                  have e1c : (st.update (rk h) (0,c)).cnt 1 = st.cnt 1 + 1 := by
                    simp [UcbState.update, hπs1]
                  have e1k : (st.update (rk h) (0,c)).clk 1 = st.clk 1 + (if c then 1 else 0) := by
                    cases c <;> simp [UcbState.update, hπ0]
                  have hexp : Φ (st.update (rk h) (0,c)) = Φ st * (if c then (2/3 : ℝ)^3 else 3/2) := by
                    simp only [Φ]
                    rw [e1k, e1c]; cases c
                    · simp only [Bool.false_eq_true, if_false, add_zero]
                      rw [show (4 * (st.clk 1:ℤ) - ((st.cnt 1 + 1 : ℕ) : ℤ)) =
                        (4 * st.clk 1 - st.cnt 1) + (-1) by push_cast; ring, zpow_add₀ (by norm_num)]
                      norm_num
                    · simp only [if_true]
                      rw [show (4 * ((st.clk 1 + 1 : ℕ) :ℤ) - ((st.cnt 1 + 1 : ℕ) : ℤ)) =
                        (4 * st.clk 1 - st.cnt 1) + 3 by push_cast; ring, zpow_add₀ (by norm_num)]
                      norm_num
                  rw [← hexp]
                  simp only [Ψ]
                  split_ifs with hb2
                  · obtain ⟨j, hj1, hj2, hj3⟩ := hb2
                    simp only [List.length_append, List.length_singleton] at hj2
                    have hjN : j = N + 1 := by
                      by_contra hne
                      apply hb
                      refine ⟨j, hj1, by omega, ?_⟩
                      rwa [List.take_append_of_le_length (by omega)] at hj3
                    subst hjN
                    rw [List.take_of_length_le (by simp; omega)] at hj3
                    have hlt := Ktop _ _ (by rw [hS, e0k]) (by rw [hS, e0c]; exact hn0) hj3
                    rw [hS] at hlt
                    apply one_le_zpow_of_nonpos₀ (by norm_num) (by norm_num)
                    have : (4 * ((st.update (rk h) (0,c)).clk 1 : ℤ)) < (st.update (rk h) (0,c)).cnt 1 := by
                      exact_mod_cast hlt
                    omega
                  · rw [hS]
                have e := HrealSum (rk h) (fun o => Ψ (h ++ [((0:Fin 1), o)]))
                beta_reduce at e
                simp only [obsW]
                rw [e, hπ0]
                have k1 := key true
                have k2 := key false
                simp only [if_true, Bool.false_eq_true, if_false] at k1 k2
                rw [show Ψ h = Φ st from if_neg hb]
                have hΦ : 0 ≤ Φ st := zpow_nonneg (by norm_num) _
                have hμ1 : inst.μ 1 = 1/2 := by simp [inst]
                rw [hμ1]
                nlinarith
            have Hrstep : ∀ N (h : List (Fin 1 × Obs 2)) (r : ℝ), h.length = N → 2 * f ≤ N →
                ∑ o : Obs 2, obsW inst (rk h) none o *
                  (r + realClick (((0:Fin 1), (none : Action 2), o) : Step 2 1)) ≤ r + 1/2 + Ψ h / 2 := by
              intro N h r hlen hN
              have e := HrealSum (rk h) (fun o => r + realClick (((0:Fin 1), (none : Action 2), o) : Step 2 1))
              beta_reduce at e
              simp only [obsW]
              rw [e]
              have hΨ := HΨnn h
              by_cases hr : rk h 0 = 0
              · have hb : bad h := ⟨N, hN, hlen.ge, by rw [List.take_of_length_le hlen.le]; exact hr⟩
                rw [show Ψ h = 1 from if_pos hb, hr]; simp [realClick, inst]; linarith
              · rw [(hperm _ hr).1]; simp [realClick, inst]; linarith
            have Hreal : ∀ N, 2 * f ≤ N → ∀ G : (Fin (N+1) → Step 2 1) → ℝ,
                expect inst P (ucb T tb) (N+1) G = ∑ τ : Fin N → Step 2 1, trajW inst P (ucb T tb) N τ *
                  ∑ o : Obs 2, obsW inst (rk (algHist τ N)) none o * G (Fin.snoc τ ((0:Fin 1), none, o)) := by
              intro N hN G
              have hact : act N = none := by
                simp only [act]; rw [if_neg (by omega), if_neg (by omega)]
              rw [Hker _ hw1]; simp only [hact]; rfl
            have Hfake : ∀ N, N ≤ 2 * f → expect inst P (ucb T tb) N reward = 0 := by
              intro N
              induction N with
              | zero => intro _; simp [expect, reward]
              | succ N ih =>
                intro hN
                rw [Hker _ hw1]
                have hne : act N ≠ none := by
                  simp only [act]
                  split_ifs with h1 h2
                  · simp
                  · simp
                  · omega
                have h0 : ∀ o : Obs 2, realClick (((0:Fin 1), act N, o) : Step 2 1) = 0 := by
                  intro o; simp [realClick, hne]
                simp only [Hrw, h0, add_zero, ← Finset.sum_mul, Hobs1, one_mul]
                have := ih (by omega); unfold expect at this; exact this
            have Hconst : ∀ N (c : ℝ), expect inst P (ucb T tb) N (fun _ => c) = c := by
              intro N c
              have := Etot N; unfold expect at this ⊢; simp only [mul_one] at this
              rw [← Finset.sum_mul, this, one_mul]
            have Hbase : ∀ h : List (Fin 1 × Obs 2), h.length = 2 * f → Inv (2 * f) h → Ψ h ≤ 4/9 := by
              intro h hlen hI
              obtain ⟨hn1, hk1⟩ := hI.2 le_rfl
              have hnb' : ¬ bad' h := by rintro ⟨j, h1, h2, -⟩; omega
              obtain ⟨hc0, hn0⟩ := hI.1 hnb'
              have hmin : min (2*f) f = f := by omega
              rw [hmin] at hn0
              have hnb : ¬ bad h := by
                rintro ⟨j, h1, h2, h3⟩
                have hj : j = 2 * f := by omega
                subst hj
                rw [List.take_of_length_le hlen.le] at h3
                have := Ktop h (ucbState T tb h) hc0 hn0 h3
                omega
              simp only [Ψ, if_neg hnb, Φ]
              rw [hn1, hk1]
              rw [show (4 * ((2*f - f : ℕ) : ℤ) - ((2*f : ℕ):ℤ)) = ((2*f : ℕ) : ℤ) by omega, zpow_natCast]
              calc (2/3:ℝ)^(2*f) ≤ (2/3)^2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
                _ = 4/9 := by norm_num
            have Hmain : ∀ K, expect inst P (ucb T tb) (2*f+K) (fun τ => Ψ (algHist τ (2*f+K))) ≤ 4/9 ∧
                expect inst P (ucb T tb) (2*f+K) reward ≤ 13/18 * K := by
              intro K
              induction K with
              | zero =>
                refine ⟨?_, by rw [Hfake _ (by omega)]; simp⟩
                calc expect inst P (ucb T tb) (2*f+0) (fun τ => Ψ (algHist τ (2*f+0)))
                    ≤ expect inst P (ucb T tb) (2*f+0) (fun _ => 4/9) := by
                      unfold expect
                      apply Finset.sum_le_sum; intro τ _
                      by_cases hw : trajW inst P (ucb T tb) (2*f+0) τ = 0
                      · rw [hw]; simp
                      apply mul_le_mul_of_nonneg_left _ (Hnn _ _)
                      exact Hbase _ (Halen _ τ) (Hsupp _ τ hw)
                  _ = 4/9 := Hconst _ _
              | succ K ih =>
                obtain ⟨ih1, ih2⟩ := ih
                have hN : 2 * f ≤ 2 * f + K := by omega
                rw [show 2 * f + (K+1) = (2*f+K) + 1 by omega]
                constructor
                · rw [Hreal _ hN]
                  calc _ ≤ ∑ τ : Fin (2*f+K) → Step 2 1, trajW inst P (ucb T tb) (2*f+K) τ *
                        Ψ (algHist τ (2*f+K)) := by
                        apply Finset.sum_le_sum; intro τ _
                        by_cases hw : trajW inst P (ucb T tb) (2*f+K) τ = 0
                        · rw [hw]; simp
                        apply mul_le_mul_of_nonneg_left _ (Hnn _ _)
                        simp only [Hfull]
                        exact HΨstep _ _ (Halen _ τ) hN (Hsupp _ τ hw)
                    _ ≤ 4/9 := ih1
                · rw [Hreal _ hN]
                  have hsplit : ∀ τ : Fin (2*f+K) → Step 2 1, trajW inst P (ucb T tb) (2*f+K) τ *
                      (reward τ + 1/2 + Ψ (algHist τ (2*f+K)) / 2) =
                      trajW inst P (ucb T tb) (2*f+K) τ * reward τ +
                      trajW inst P (ucb T tb) (2*f+K) τ * (1/2) +
                      (trajW inst P (ucb T tb) (2*f+K) τ * Ψ (algHist τ (2*f+K))) * (1/2) :=
                    fun τ => by ring
                  calc _ ≤ ∑ τ : Fin (2*f+K) → Step 2 1, trajW inst P (ucb T tb) (2*f+K) τ *
                        (reward τ + 1/2 + Ψ (algHist τ (2*f+K)) / 2) := by
                        apply Finset.sum_le_sum; intro τ _
                        apply mul_le_mul_of_nonneg_left _ (Hnn _ _)
                        simp only [Hrw]
                        exact Hrstep _ _ _ (Halen _ τ) hN
                    _ ≤ 13/18 * ((K + 1 : ℕ) : ℝ) := by
                        simp only [hsplit, Finset.sum_add_distrib, ← Finset.sum_mul]
                        have e1 := Etot (2*f+K)
                        unfold expect at e1 ih1 ih2
                        simp only [mul_one] at e1
                        rw [e1]; push_cast; linarith
            intro N hN
            obtain ⟨K, rfl⟩ : ∃ K, N = 2 * f + K := ⟨N - 2*f, by omega⟩
            have := (Hmain K).2
            push_cast; linarith
          have hlogT : L ≤ 2 * Real.sqrt T := by
            have := Real.log_le_rpow_div (x := (T:ℝ)) (by linarith) (by norm_num : (0:ℝ) < 1/2)
            rw [← Real.sqrt_eq_rpow] at this; linarith
          have hsq : 200 ≤ Real.sqrt T := by
            rw [show (200:ℝ) = Real.sqrt 40000 by rw [show (40000:ℝ) = 200^2 by norm_num, Real.sqrt_sq (by norm_num)]]
            exact Real.sqrt_le_sqrt (by linarith)
          have hsqT : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt (by linarith)
          have hfT : 2 * (f:ℝ) ≤ T / 2 := by nlinarith
          have hfN : 2 * f ≤ T := by
            have : ((2 * f : ℕ) : ℝ) ≤ T := by push_cast; linarith
            exact_mod_cast this
          unfold regret
          rw [Eopt T hfN]
          have := Eucb T hfN
          nlinarith
