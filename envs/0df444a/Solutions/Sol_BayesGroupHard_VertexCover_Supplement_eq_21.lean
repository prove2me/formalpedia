-- Prove2me | solution 1 for BayesGroupHard.VertexCover.Supplement.eq_21
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:27:46.115336+00:00
-- url     : https://prove2.me/submissions/adbd8074-5e1e-447b-ad3b-e23bd3304542

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Supplement_Network

open BayesGroupHard
open BayesGroupHard.VertexCover
open BayesGroupHard.VertexCover.Supplement

open Finset

/-- (21), p. 32: on a signal profile realising the history (19), agent `i`'s information set at
time two consists of the profiles with her own signal whose informative part lies in `Σ`; her
log-belief ratio is the log of the ratio of the likelihood sums over `Σ`; `(0,1,…,1) ∈ Σ`, it is
the only profile of `Σ` with `s_κ = 0`, and the profiles of `Σ` with `s_κ = 1` are exactly the
exact covers. -/
theorem solution {n : ℕ} (X : RXC3 n) (s : XAgent n → Bool) (hs : Observed X s) :
    rInfo (xcNet X) 2 observer s =
      univ.filter (fun s' => s' observer = s observer ∧ project s' ∈ sigma X) ∧
    rLog (xcNet X) 2 observer s = Real.log (coreMass X true / coreMass X false) ∧
    baseProfile n ∈ sigma X ∧
    (∀ v : Fin n → Bool, (false, v) ∈ sigma X ↔ v = fun _ => true) ∧
    (∀ v : Fin n → Bool, (true, v) ∈ sigma X ↔ ExactCover X (selected (true, v))) := by
      classical
      have L : ∀ (A : Finset (XAgent n)) (s₀ : XAgent n → Bool) (θ : Bool),
          ∑ s' ∈ univ.filter (fun s' => ∀ a ∈ A, s' a = s₀ a), jointProb (xcNet X) θ s' =
            ∏ a ∈ A, sig (xcNet X) a θ (s₀ a) := by
        intro A s₀ θ
        rw [Finset.sum_filter]
        have h1 : ∀ s' : XAgent n → Bool,
            (if ∀ a ∈ A, s' a = s₀ a then jointProb (xcNet X) θ s' else 0)
              = ∏ a, (if a ∈ A ∧ s' a ≠ s₀ a then 0 else sig (xcNet X) a θ (s' a)) := by
          intro s'
          split_ifs with h
          · unfold jointProb
            refine Finset.prod_congr rfl (fun a _ => ?_)
            rw [if_neg]
            rintro ⟨ha, hne⟩
            exact hne (h a ha)
          · push_neg at h
            obtain ⟨a, ha, hne⟩ := h
            symm
            exact Finset.prod_eq_zero (Finset.mem_univ a) (if_pos ⟨ha, hne⟩)
        rw [Finset.sum_congr rfl (fun s' _ => h1 s')]
        rw [← Fintype.prod_sum (fun a b => if a ∈ A ∧ b ≠ s₀ a then (0:ℝ) else sig (xcNet X) a θ b)]
        rw [← Finset.univ_inter A, ← Finset.prod_ite_mem]
        refine Finset.prod_congr rfl (fun a _ => ?_)
        rw [Fintype.sum_bool]
        by_cases ha : a ∈ A
        · rw [if_pos ha]
          cases h : s₀ a <;> simp [ha]
        · rw [if_neg ha]
          simp [ha, sig]
      have hpost : ∀ (A : Finset (XAgent n)) (s₀ : XAgent n → Bool),
          post (xcNet X) true (univ.filter (fun s' => ∀ a ∈ A, s' a = s₀ a)) =
            (∏ a ∈ A, sig (xcNet X) a true (s₀ a)) /
              ((∏ a ∈ A, sig (xcNet X) a true (s₀ a)) + ∏ a ∈ A, sig (xcNet X) a false (s₀ a)) := by
        intro A s₀
        unfold post
        rw [Fintype.sum_bool, L, L, ← mul_add, mul_div_mul_left _ _ (by norm_num)]
      have hsigT : ∀ j θ b, sig (xcNet X) (tau j) θ b =
          if b then (if θ then 1/2 else 1/3) else 1 - (if θ then 1/2 else 1/3) := by
        intro j θ b; rfl
      have hsigK : ∀ θ b, sig (xcNet X) kappa θ b =
          if b then (if θ then 7/12 else 7/27) else 1 - (if θ then 7/12 else 7/27) := by
        intro θ b; rfl
      have hsigE : ∀ e θ b, sig (xcNet X) (epsilon e) θ b = 1/2 := by
        intro e θ b; cases b <;> simp [sig, xcNet, epsilon] <;> norm_num
      have hsigO : ∀ θ b, sig (xcNet X) observer θ b = 1/2 := by
        intro θ b; cases b <;> simp [sig, xcNet, observer] <;> norm_num
      -- time-zero reports
      have hR0 : ∀ k s', report (xcNet X) 0 k s' =
          sig (xcNet X) k true (s' k) / (sig (xcNet X) k true (s' k) + sig (xcNet X) k false (s' k)) := by
        intro k s'
        have : rInfo (xcNet X) 0 k s' = univ.filter (fun s'' => ∀ a ∈ ({k} : Finset _), s'' a = s' a) := by
          ext s''; simp [rInfo, rInfoUsing]
        unfold report belief
        rw [this, hpost]
        simp
      have hR0E : ∀ e s', report (xcNet X) 0 (epsilon e) s' = 1/2 := by
        intro e s'; rw [hR0, hsigE, hsigE]; norm_num
      have hR0O : ∀ s', report (xcNet X) 0 observer s' = 1/2 := by
        intro s'; rw [hR0, hsigO, hsigO]; norm_num
      have hR0K : ∀ s' s'', report (xcNet X) 0 kappa s' = report (xcNet X) 0 kappa s'' ↔
          s' kappa = s'' kappa := by
        intro s' s''
        rw [hR0, hR0, hsigK, hsigK, hsigK, hsigK]
        cases s' kappa <;> cases s'' kappa <;> norm_num
      have hR0T : ∀ j s' s'', report (xcNet X) 0 (tau j) s' = report (xcNet X) 0 (tau j) s'' ↔
          s' (tau j) = s'' (tau j) := by
        intro j s' s''
        rw [hR0, hR0, hsigT, hsigT, hsigT, hsigT]
        cases s' (tau j) <;> cases s'' (tau j) <;> norm_num
      have hRU1 : ∀ j s', reportsUpTo (xcNet X) 1 0 j s' = report (xcNet X) 0 j s' := by
        intro j s'; rfl
      have hRU2 : ∀ τ j s', τ < 2 → reportsUpTo (xcNet X) 2 τ j s' = report (xcNet X) τ j s' := by
        intro τ j s' hτ
        interval_cases τ <;> rfl
      have hnbrE : ∀ e, (xcNet X).nbr (epsilon e) = insert (epsilon e) (insert kappa
          ((univ.filter (fun j => e ∈ X.sets j)).image tau)) := fun e => rfl
      have hnbrO : (xcNet X).nbr observer = insert observer (univ.image epsilon) := rfl
      have hI1E : ∀ e s', rInfo (xcNet X) 1 (epsilon e) s' =
          univ.filter (fun s'' => ∀ a ∈ (xcNet X).nbr (epsilon e), s'' a = s' a) := by
        intro e s'
        ext s''
        simp only [rInfo, rInfoUsing, mem_filter, mem_univ, true_and, Nat.lt_one_iff, forall_eq, hRU1]
        rw [hnbrE]
        simp only [Finset.forall_mem_insert, Finset.forall_mem_image, hR0E, hR0K, hR0T]
        simp
      have hR1E : ∀ e s', (report (xcNet X) 1 (epsilon e) s' = 243/371 ↔
          2 * bit (s' kappa) + ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (s' (tau j)) = 3) := by
        intro e s'
        set T := univ.filter (fun j => e ∈ X.sets j) with hTdef
        set k := #(T.filter (fun j => s' (tau j) = true)) with hkdef
        set k' := #(T.filter (fun j => ¬ s' (tau j) = true)) with hk'def
        have hT : ∀ θ : Bool, ∏ j ∈ T, sig (xcNet X) (tau j) θ (s' (tau j)) =
            (if θ then (1:ℝ)/2 else 1/3) ^ k * (1 - if θ then (1:ℝ)/2 else 1/3) ^ k' := by
          intro θ; simp only [hsigT]; rw [prod_ite, prod_const, prod_const]
        have hbit : ∑ j ∈ T, bit (s' (tau j)) = k := by
          simp only [bit]; rw [sum_boole]; rfl
        have hk : k + k' = 3 := by
          rw [hkdef, hk'def, card_filter_add_card_filter_not, hTdef, X.regular e]
        have hprod : ∀ θ, ∏ a ∈ (xcNet X).nbr (epsilon e), sig (xcNet X) a θ (s' a) =
            1/2 * (sig (xcNet X) kappa θ (s' kappa) *
              ((if θ then (1:ℝ)/2 else 1/3) ^ k * (1 - if θ then (1:ℝ)/2 else 1/3) ^ k')) := by
          intro θ
          rw [hnbrE, prod_insert (by simp [epsilon, kappa, tau]), prod_insert (by simp [kappa, tau]),
            prod_image (by intro x _ y _ h; exact Sum.inl_injective h), hT, hsigE]
        unfold report belief
        rw [hI1E, hpost, hprod, hprod, hbit, hsigK, hsigK]
        generalize s' kappa = b
        clear_value k k'
        obtain rfl : k' = 3 - k := by omega
        have : k ≤ 3 := by omega
        interval_cases k <;> cases b <;> norm_num [bit]
      have hR1O : ∀ s', report (xcNet X) 1 observer s' = 1/2 := by
        intro s'
        have : rInfo (xcNet X) 1 observer s' =
            univ.filter (fun s'' => ∀ a ∈ ({observer} : Finset _), s'' a = s' a) := by
          ext s''
          simp only [rInfo, rInfoUsing, mem_filter, mem_univ, true_and, Nat.lt_one_iff, forall_eq, hRU1]
          rw [hnbrO]
          simp [Finset.forall_mem_insert, Finset.forall_mem_image, hR0O, hR0E]
        unfold report belief
        rw [this, hpost, prod_singleton, prod_singleton, hsigO, hsigO]
        norm_num
      have hP1 : rInfo (xcNet X) 2 observer s =
          univ.filter (fun s' => s' observer = s observer ∧ project s' ∈ sigma X) := by
        ext s'
        simp only [rInfo, rInfoUsing, mem_filter, mem_univ, true_and]
        refine and_congr_right (fun _ => ?_)
        rw [hnbrO]
        simp only [Finset.forall_mem_insert, Finset.forall_mem_image, mem_univ, true_implies]
        have hsig : project s' ∈ sigma X ↔ ∀ e, 2 * bit (s' kappa) +
            ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (s' (tau j)) = 3 := by
          simp [sigma, project]
        rw [hsig]
        constructor
        · rintro ⟨_, h⟩ e
          have := @h e 1 (by norm_num)
          rw [hRU2 _ _ _ (by norm_num), hRU2 _ _ _ (by norm_num), (hs e).2] at this
          exact (hR1E e s').1 this
        · intro h
          refine ⟨fun τ hτ => ?_, fun ⦃e⦄ τ hτ => ?_⟩
          · rw [hRU2 _ _ _ hτ, hRU2 _ _ _ hτ]
            interval_cases τ
            · rw [hR0O, hR0O]
            · rw [hR1O, hR1O]
          · rw [hRU2 _ _ _ hτ, hRU2 _ _ _ hτ]
            interval_cases τ
            · rw [hR0E, hR0E]
            · rw [(hs e).2]; exact (hR1E e s').2 (h e)
      have hbitsum : ∀ (T : Finset (Fin n)) (v : Fin n → Bool),
          ∑ j ∈ T, bit (v j) = #(T.filter (fun j => v j = true)) := by
        intro T v; simp only [bit]; rw [sum_boole]; rfl
      have hP3 : baseProfile n ∈ sigma X := by
        simp [sigma, baseProfile, bit, X.regular]
      have hP4 : ∀ v : Fin n → Bool, (false, v) ∈ sigma X ↔ v = fun _ => true := by
        intro v
        have hm : (false, v) ∈ sigma X ↔ ∀ e, 2 * bit false +
            ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (v j) = 3 := by
          simp [sigma]
        rw [hm]
        constructor
        · intro h
          funext j
          obtain ⟨e, he⟩ : (X.sets j).Nonempty := by
            rw [← card_pos, X.triple]; norm_num
          have h1 := h e
          rw [hbitsum] at h1
          have h2 : #((univ.filter (fun j => e ∈ X.sets j)).filter (fun j => v j = true)) =
              #(univ.filter (fun j => e ∈ X.sets j)) := by
            rw [X.regular e]; simpa [bit] using h1
          exact Finset.filter_card_eq h2 j (by simp [he])
        · rintro rfl e
          simp [bit, X.regular]
      have hP5 : ∀ v : Fin n → Bool, (true, v) ∈ sigma X ↔ ExactCover X (selected (true, v)) := by
        intro v
        have hm : (true, v) ∈ sigma X ↔ ∀ e, 2 * bit true +
            ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (v j) = 3 := by
          simp [sigma]
        rw [hm]
        unfold ExactCover selected
        refine forall_congr' (fun e => ?_)
        rw [hbitsum, filter_filter, filter_filter]
        have : (univ.filter (fun j => e ∈ X.sets j ∧ v j = true)) =
            (univ.filter (fun j => (true, v).2 j = true ∧ e ∈ X.sets j)) := by
          ext j; simp [and_comm]
        rw [this]
        simp only [bit, if_true]
        omega
      have hjp : ∀ θ (s' : XAgent n → Bool), jointProb (xcNet X) θ s' =
          (1/2) ^ (n+1) * coreWeight θ (project s') := by
        intro θ s'
        have hT' : ∀ j θ b, sig (xcNet X) (Sum.inl j) θ b =
            if b then (if θ then 1/2 else 1/3) else 1 - (if θ then 1/2 else 1/3) := hsigT
        have hE' : ∀ e θ b, sig (xcNet X) (Sum.inr (Sum.inl e)) θ b = 1/2 := hsigE
        have hK' : ∀ θ b, sig (xcNet X) (Sum.inr (Sum.inr false)) θ b =
            if b then (if θ then 7/12 else 7/27) else 1 - (if θ then 7/12 else 7/27) := hsigK
        have hO' : ∀ θ b, sig (xcNet X) (Sum.inr (Sum.inr true)) θ b = 1/2 := hsigO
        unfold jointProb
        rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_bool]
        simp only [hT', hE', hK', hO', prod_const, card_univ, Fintype.card_fin]
        unfold coreWeight project
        simp only [kappa, tau]
        rw [pow_succ]
        ring_nf
      have hcwpos : ∀ θ (c : CoreProfile n), 0 < coreWeight θ c := by
        intro θ c
        unfold coreWeight
        apply mul_pos
        · split_ifs <;> norm_num
        · apply prod_pos; intro j _; split_ifs <;> norm_num
      have hM : ∀ θ, 0 < coreMass X θ := fun θ =>
        Finset.sum_pos (fun c _ => hcwpos θ c) ⟨baseProfile n, hP3⟩
      let φ : (XAgent n → Bool) ≃ CoreProfile n × (Bool × (Fin n → Bool)) :=
        { toFun := fun s' => (project s', s' observer, fun e => s' (epsilon e))
          invFun := fun x => Sum.elim x.1.2 (Sum.elim x.2.2 (fun b => if b then x.2.1 else x.1.1))
          left_inv := by
            intro s'; funext a
            rcases a with j | e | b
            · rfl
            · rfl
            · cases b <;> rfl
          right_inv := by intro x; rfl }
      have hS : ∀ θ, ∑ s' ∈ univ.filter (fun s' => s' observer = s observer ∧ project s' ∈ sigma X),
          jointProb (xcNet X) θ s' = (1/2) ^ (n+1) * (2 ^ n * coreMass X θ) := by
        intro θ
        rw [sum_congr rfl (fun s' _ => hjp θ s'), ← mul_sum]
        congr 1
        rw [sum_filter]
        rw [Fintype.sum_equiv φ
          (fun a => if a observer = s observer ∧ project a ∈ sigma X then coreWeight θ (project a) else 0)
          (fun x => if x.2.1 = s observer ∧ x.1 ∈ sigma X then coreWeight θ x.1 else 0) (fun s' => rfl)]
        rw [Fintype.sum_prod_type]
        have hin : ∀ c : CoreProfile n, ∑ y : Bool × (Fin n → Bool),
            (if (c, y).2.1 = s observer ∧ (c, y).1 ∈ sigma X then coreWeight θ (c, y).1 else 0) =
            2 ^ n * (if c ∈ sigma X then coreWeight θ c else 0) := by
          intro c
          rw [Fintype.sum_prod_type, Fintype.sum_bool]
          simp only [sum_const, card_univ, Fintype.card_pi, Fintype.card_bool, prod_const,
            Fintype.card_fin, nsmul_eq_mul]
          cases s observer <;> by_cases hc : c ∈ sigma X <;> simp [hc]
        rw [sum_congr rfl (fun c _ => hin c), ← mul_sum, sum_ite_mem, univ_inter]
        rfl
      have hP2 : rLog (xcNet X) 2 observer s = Real.log (coreMass X true / coreMass X false) := by
        unfold rLog belief post
        rw [hP1]
        simp only [hS, Fintype.sum_bool]
        congr 1
        have hD : (1/2 * ((1/2) ^ (n+1) * (2 ^ n * coreMass X true)) +
            1/2 * ((1/2) ^ (n+1) * (2 ^ n * coreMass X false)) : ℝ) ≠ 0 := by
          have := hM true; have := hM false; positivity
        rw [div_div_div_cancel_right₀ hD, mul_div_mul_left _ _ (by norm_num),
          mul_div_mul_left _ _ (by positivity), mul_div_mul_left _ _ (by positivity)]
      exact ⟨hP1, hP2, hP3, hP4, hP5⟩
