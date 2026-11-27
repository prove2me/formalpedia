-- Prove2me | solution 1 for BayesGroupHard.VertexCover.Supplement.section_B_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:28:31.813866+00:00
-- url     : https://prove2.me/submissions/7777493a-1cd4-47f2-8164-0d93756069d1

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Supplement_Network

open BayesGroupHard
open BayesGroupHard.VertexCover
open BayesGroupHard.VertexCover.Supplement

open Finset

/-- §B.2, p. 33 (YES case): `q̄ = 1/2`; with `N̂ ≥ 1` exact covers the likelihood sums of (21)
are `N̂ p̄⋆ q̄^n + (1-p̄⋆) p̄^n` and `N̂ p̲⋆ q̲^n + (1-p̲⋆) p̲^n`; `µ_i,2(1) = e^φ/(1+e^φ)`;
`ℓ̂ = log(q̄/q̲) < 0`; there is a constant `C`, independent of `n` and of the instance, with
`φ_i,2 < n ℓ̂ + C` on every YES instance; and there are `c > 0`, `N` with `µ_i,2(1) < exp(-c n)`
for every YES instance with `n ≥ N`. -/
theorem solution :
    qBar = 1 / 2 ∧
    (∀ {n : ℕ} (X : RXC3 n), HasCover X →
      1 ≤ coverCount X ∧
      coreMass X true =
        (coverCount X : ℝ) * (7 / 12) * qBar ^ n + (1 - 7 / 12) * (1 / 2) ^ n ∧
      coreMass X false =
        (coverCount X : ℝ) * (7 / 27) * qUnder ^ n + (1 - 7 / 27) * (1 / 3) ^ n ∧
      ∀ s : XAgent n → Bool, Observed X s →
        belief (xcNet X) 2 observer s true =
          Real.exp (rLog (xcNet X) 2 observer s) /
            (1 + Real.exp (rLog (xcNet X) 2 observer s))) ∧
    ellHat < 0 ∧
    (∃ C : ℝ, ∀ {n : ℕ} (X : RXC3 n), HasCover X →
      ∀ s : XAgent n → Bool, Observed X s →
        rLog (xcNet X) 2 observer s < (n : ℝ) * ellHat + C) ∧
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ X : RXC3 n, HasCover X →
      ∀ s : XAgent n → Bool, Observed X s →
        belief (xcNet X) 2 observer s true < Real.exp (-c * n) := by
          classical
          have hqBar : qBar = 1/2 := by
            unfold qBar
            rw [show (1 - 1/2 : ℝ) = 1/2 by norm_num, ← Real.rpow_add (by norm_num)]; norm_num
          have hqU3 : qUnder ^ 3 = 4/27 := by
            unfold qUnder
            rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast ((1 - 1/3 : ℝ) ^ (2/3:ℝ)),
              ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
            norm_num
          have hqUpos : 0 < qUnder := by unfold qUnder; positivity
          have hqU : 1/2 < qUnder := by
            by_contra h; push_neg at h
            have : qUnder ^ 3 ≤ (1/2)^3 := pow_le_pow_left₀ hqUpos.le h 3
            rw [hqU3] at this; norm_num at this
          have hell : ellHat < 0 := by
            unfold ellHat; rw [hqBar]
            apply Real.log_neg (by positivity)
            rw [div_lt_one hqUpos]; exact hqU
          have hqU3k : ∀ k : ℕ, qUnder ^ (3 * k) = (4/27) ^ k := fun k => by rw [pow_mul, hqU3]
          have hmass : ∀ {n : ℕ} (X : RXC3 n), HasCover X → 1 ≤ coverCount X ∧
              coreMass X true = (coverCount X : ℝ) * (7 / 12) * (1/2) ^ n + (1 - 7 / 12) * (1 / 2) ^ n ∧
              coreMass X false = (coverCount X : ℝ) * (7 / 27) * qUnder ^ n + (1 - 7 / 27) * (1 / 3) ^ n := by
            intro n X hX
            have sumbit : ∀ (c : CoreProfile n) (T : Finset (Fin n)),
                ∑ j ∈ T, bit (c.2 j) = (T.filter (fun j => c.2 j = true)).card := by
              intro c T
              simp only [bit]
              rw [Finset.sum_boole]; simp
            have Tcard : ∀ e, (univ.filter (fun j => e ∈ X.sets j)).card = 3 := X.regular
            -- (A)
            have hA : ∀ c ∈ sigma X, c.1 = false → c = baseProfile n := by
              intro c hc h1
              simp only [sigma, mem_filter, mem_univ, true_and] at hc
              have hall : ∀ j, c.2 j = true := by
                intro j
                obtain ⟨e, he⟩ : (X.sets j).Nonempty := by
                  rw [← Finset.card_pos, X.triple j]; norm_num
                have h := hc e
                rw [h1, sumbit] at h
                simp only [bit] at h
                have h3 : ((univ.filter (fun j => e ∈ X.sets j)).filter (fun j => c.2 j = true)).card
                    = (univ.filter (fun j => e ∈ X.sets j)).card := by
                  rw [Tcard]; simpa using h
                exact Finset.filter_card_eq h3 j (by simpa using he)
              obtain ⟨c1, c2⟩ := c
              simp only at h1 hall
              simp only [baseProfile, h1, Prod.mk.injEq, true_and]
              funext j; exact hall j
            -- (C)
            have hC : baseProfile n ∈ sigma X := by
              simp only [sigma, mem_filter, mem_univ, true_and, baseProfile]
              intro e
              simp [bit, Tcard e]
            -- (B)
            have hB : ∀ c ∈ sigma X, c.1 = true → ExactCover X (selected c) := by
              intro c hc h1 e
              simp only [sigma, mem_filter, mem_univ, true_and] at hc
              have h := hc e
              rw [h1, sumbit] at h
              norm_num [bit] at h
              simp only [selected, Finset.filter_filter]
              have : (univ.filter (fun j => e ∈ X.sets j ∧ c.2 j = true)).card = 1 := by
                rw [← Finset.filter_filter]; omega
              simpa [and_comm] using this
            have hcardS : ∀ S, ExactCover X S → 3 * S.card = n := by
              intro S hS
              have h1 : ∑ e : Fin n, (S.filter (fun j => e ∈ X.sets j)).card = n := by
                have hS' : ∀ e, (S.filter (fun j => e ∈ X.sets j)).card = 1 := hS
                simp [hS']
              have h2 : ∑ e : Fin n, (S.filter (fun j => e ∈ X.sets j)).card
                  = ∑ j ∈ S, (X.sets j).card := by
                simp only [Finset.card_filter]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro j _
                rw [← Finset.card_filter]; congr 1; ext x; simp
              rw [h2, Finset.sum_congr rfl (fun j _ => X.triple j)] at h1
              simp at h1; linarith
            -- (D)
            have hD : ((sigma X).filter (fun c => c.1 = true)).card = coverCount X := by
              unfold coverCount
              apply Finset.card_nbij' (fun c => selected c) (fun S => (true, fun j => decide (j ∈ S)))
              · intro c hc
                simp only [coe_filter, Set.mem_setOf_eq, mem_coe, mem_filter] at hc ⊢
                exact ⟨mem_univ _, hB c hc.1 hc.2⟩
              · intro S hS
                simp only [coe_filter, Set.mem_setOf_eq, mem_coe, mem_filter, mem_univ, true_and] at hS ⊢
                refine ⟨?_, trivial⟩
                simp only [sigma, mem_filter, mem_univ, true_and]
                intro e
                have := hS e
                have h2 : ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (decide (j ∈ S)) = 1 := by
                  simp only [bit, Finset.sum_boole]
                  rw [← this]; simp only [Nat.cast_id]; congr 1; ext j; simp [and_comm]
                rw [h2]; simp [bit]
              · intro c hc
                simp only [coe_filter, Set.mem_setOf_eq, mem_coe, mem_filter] at hc
                obtain ⟨c1, c2⟩ := c
                simp only at hc
                simp only [hc.2, selected, Prod.mk.injEq, true_and]
                funext j; simp
              · intro S _
                ext j; simp [selected]
            have hWt1 : ∀ c : CoreProfile n, c.1 = true → coreWeight true c = 7/12 * (1/2)^n := by
              intro c h; simp [coreWeight, h]; norm_num
            have hWt0 : ∀ c ∈ sigma X, c.1 = true → coreWeight false c = 7/27 * qUnder^n := by
              intro c hc h
              have h3 := hcardS _ (hB c hc h)
              have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun j => c.2 j = true)
              simp only [coreWeight, h, if_true, Bool.false_eq_true, if_false]
              rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
              simp only [selected] at h3
              rw [card_univ, Fintype.card_fin] at hsplit
              obtain ⟨k, hk⟩ : ∃ k, (univ.filter (fun j => c.2 j = true)).card = k := ⟨_, rfl⟩
              rw [hk] at h3 hsplit
              have hk2 : (univ.filter (fun j => ¬ c.2 j = true)).card = 2 * k := by omega
              rw [hk, hk2, ← h3, hqU3k, pow_mul, ← mul_pow]; norm_num
            have hcm : ∀ θ (w : ℝ), (∀ c ∈ (sigma X).filter (fun c => c.1 = true), coreWeight θ c = w) →
                coreMass X θ = (coverCount X : ℝ) * w + coreWeight θ (baseProfile n) := by
              intro θ w hw
              unfold coreMass
              rw [← Finset.sum_filter_add_sum_filter_not (sigma X) (fun c => c.1 = true)]
              have hnot : (sigma X).filter (fun c => ¬ c.1 = true) = {baseProfile n} := by
                ext c
                simp only [mem_filter, mem_singleton, Bool.not_eq_true]
                constructor
                · rintro ⟨h1, h2⟩; exact hA c h1 h2
                · rintro rfl; exact ⟨hC, rfl⟩
              rw [hnot, Finset.sum_singleton]
              congr 1
              rw [← hD, ← nsmul_eq_mul, ← Finset.sum_const]
              exact Finset.sum_congr rfl hw
            refine ⟨?_, ?_, ?_⟩
            · obtain ⟨S, hS⟩ := hX
              unfold coverCount
              exact Finset.card_pos.2 ⟨S, by simp [hS]⟩
            · rw [hcm true (7/12 * (1/2)^n) (fun c hc => hWt1 c (mem_filter.1 hc).2)]
              simp [coreWeight, baseProfile]; ring
            · rw [hcm false (7/27 * qUnder^n) (fun c hc => hWt0 c (mem_filter.1 hc).1 (mem_filter.1 hc).2)]
              simp [coreWeight, baseProfile]; ring
          have hnet : ∀ {n : ℕ} (X : RXC3 n) (s : XAgent n → Bool), Observed X s → ∀ θ : Bool,
              ∑ s' ∈ rInfo (xcNet X) 2 observer s, jointProb (xcNet X) θ s' = 1/2 * coreMass X θ := by
            intro n X s hs θ
            have hsigpos : ∀ a θ b, 0 < sig (xcNet X) a θ b := by
              intro a θ b
              rcases a with j | e | b'
              · cases θ <;> cases b <;> norm_num [sig, xcNet]
              · cases θ <;> cases b <;> norm_num [sig, xcNet]
              · cases b' <;> cases θ <;> cases b <;> norm_num [sig, xcNet]
            have cyl : ∀ (J : Finset (XAgent n)) (v : XAgent n → Bool) (θ : Bool),
                ∑ s' ∈ univ.filter (fun s' : XAgent n → Bool => ∀ j ∈ J, s' j = v j), jointProb (xcNet X) θ s'
                  = ∏ j ∈ J, sig (xcNet X) j θ (v j) := by
              intro J v θ
              rw [Finset.sum_filter]
              have h1 : ∀ s' : XAgent n → Bool, (if ∀ j ∈ J, s' j = v j then jointProb (xcNet X) θ s' else 0)
                  = ∏ i, (fun i b => if (i ∈ J → b = v i) then sig (xcNet X) i θ b else 0) i (s' i) := by
                intro s'
                simp only
                rw [Finset.prod_ite_zero]
                simp [jointProb]
              simp_rw [h1]
              refine (Fintype.prod_sum (fun i b => if (i ∈ J → b = v i) then sig (xcNet X) i θ b else 0)).symm.trans ?_
              rw [show ∏ j ∈ J, sig (xcNet X) j θ (v j) = ∏ i, if i ∈ J then sig (xcNet X) i θ (v i) else 1 from by
                rw [Finset.prod_ite_mem, univ_inter]]
              apply Finset.prod_congr rfl
              intro i _
              rw [Fintype.sum_bool]
              by_cases hi : i ∈ J
              · cases hv : v i <;> simp [hi, hv]
              · simp [hi, sig]
            have postcyl : ∀ (J : Finset (XAgent n)) (v : XAgent n → Bool) (I : Finset (XAgent n → Bool)),
                I = univ.filter (fun s' : XAgent n → Bool => ∀ j ∈ J, s' j = v j) →
                post (xcNet X) true I = (∏ j ∈ J, sig (xcNet X) j true (v j)) /
                  ((∏ j ∈ J, sig (xcNet X) j true (v j)) + ∏ j ∈ J, sig (xcNet X) j false (v j)) := by
              intro J v I hI
              subst hI
              unfold post
              rw [Fintype.sum_bool, cyl, cyl, ← mul_add, mul_div_mul_left _ _ (by norm_num)]
            have rep0 : ∀ j s, report (xcNet X) 0 j s = sig (xcNet X) j true (s j) /
                (sig (xcNet X) j true (s j) + sig (xcNet X) j false (s j)) := by
              intro j s
              unfold report belief rInfo
              rw [postcyl {j} s]
              · simp
              · ext s'; simp [rInfoUsing]
            have rep0eps : ∀ e s, report (xcNet X) 0 (epsilon e) s = 1/2 := by
              intro e s; rw [rep0]; cases s (epsilon e) <;> norm_num [sig, xcNet, epsilon]
            have rep0obs : ∀ s, report (xcNet X) 0 observer s = 1/2 := by
              intro s; rw [rep0]; cases s observer <;> norm_num [sig, xcNet, observer]
            have rep0tau : ∀ j s s', report (xcNet X) 0 (tau j) s' = report (xcNet X) 0 (tau j) s ↔
                s' (tau j) = s (tau j) := by
              intro j s s'; rw [rep0, rep0]
              cases s' (tau j) <;> cases s (tau j) <;> norm_num [sig, xcNet, tau]
            have rep0kap : ∀ s s', report (xcNet X) 0 kappa s' = report (xcNet X) 0 kappa s ↔
                s' kappa = s kappa := by
              intro s s'; rw [rep0, rep0]
              cases s' kappa <;> cases s kappa <;> norm_num [sig, xcNet, kappa]
            have ru10 : ∀ k s, reportsUpTo (xcNet X) 1 0 k s = report (xcNet X) 0 k s := by
              intro k s; rfl
            have ru20 : ∀ k s, reportsUpTo (xcNet X) 2 0 k s = report (xcNet X) 0 k s := by
              intro k s; rfl
            have ru21 : ∀ k s, reportsUpTo (xcNet X) 2 1 k s = report (xcNet X) 1 k s := by
              intro k s; rfl
            have nbrEps : ∀ e, (xcNet X).nbr (epsilon e) = insert (epsilon e) (insert kappa
                  ((univ.filter (fun j => e ∈ X.sets j)).image tau)) := fun e => rfl
            have nbrObs : (xcNet X).nbr observer = insert observer (univ.image epsilon) := rfl
            have info1eps : ∀ e s, rInfo (xcNet X) 1 (epsilon e) s =
                univ.filter (fun s' : XAgent n → Bool => ∀ j ∈ (xcNet X).nbr (epsilon e), s' j = s j) := by
              intro e s
              ext s'
              simp only [rInfo, rInfoUsing, mem_filter, mem_univ, true_and, Nat.lt_one_iff, forall_eq, ru10]
              rw [nbrEps]
              simp only [mem_insert, mem_image, mem_filter, mem_univ, true_and, forall_eq_or_imp,
                forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, rep0eps, rep0kap, rep0tau]
            have info1obs : ∀ s, rInfo (xcNet X) 1 observer s =
                univ.filter (fun s' : XAgent n → Bool => ∀ j ∈ ({observer} : Finset (XAgent n)), s' j = s j) := by
              intro s
              ext s'
              simp only [rInfo, rInfoUsing, mem_filter, mem_univ, true_and, Nat.lt_one_iff, forall_eq, ru10]
              rw [nbrObs]
              simp [rep0eps, rep0obs]
            have rep1obs : ∀ s, report (xcNet X) 1 observer s = 1/2 := by
              intro s
              unfold report belief
              rw [postcyl _ s _ (info1obs s)]
              cases s observer <;> norm_num [sig, xcNet, observer]
            have rep1eps : ∀ e s, report (xcNet X) 1 (epsilon e) s = 243/371 ↔
                2 * bit (s kappa) + ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (s (tau j)) = 3 := by
              intro e s
              unfold report belief
              rw [postcyl _ s _ (info1eps e s), nbrEps]
              have hne1 : epsilon e ∉ insert kappa ((univ.filter (fun j => e ∈ X.sets j)).image tau) := by
                simp [epsilon, kappa, tau]
              have hne2 : kappa ∉ ((univ.filter (fun j => e ∈ X.sets j)).image tau) := by
                simp [kappa, tau]
              have htinj : Set.InjOn (tau (n := n)) ↑(univ.filter (fun j => e ∈ X.sets j)) := by
                intro a _ b _ h; simpa [tau] using h
              rw [prod_insert hne1, prod_insert hne2, prod_insert hne1, prod_insert hne2,
                prod_image htinj, prod_image htinj]
              have hpow : ∀ θ : Bool, ∏ j ∈ univ.filter (fun j => e ∈ X.sets j), sig (xcNet X) (tau j) θ (s (tau j))
                  = (if θ then 1/2 else 1/3) ^ ((univ.filter (fun j => e ∈ X.sets j)).filter (fun j => s (tau j) = true)).card
                    * (1 - if θ then 1/2 else 1/3) ^ ((univ.filter (fun j => e ∈ X.sets j)).filter (fun j => ¬ s (tau j) = true)).card := by
                intro θ
                have hptau : ∀ j, (xcNet X).p (tau j) θ = if θ then 1/2 else 1/3 := fun _ => rfl
                simp only [sig]
                rw [Finset.prod_ite]
                simp only [hptau]
                rw [prod_const, prod_const]
              rw [hpow, hpow]
              have hsplit := Finset.card_filter_add_card_filter_not (s := univ.filter (fun j => e ∈ X.sets j)) (fun j => s (tau j) = true)
              rw [X.regular e] at hsplit
              have hsum : ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (s (tau j)) =
                  ((univ.filter (fun j => e ∈ X.sets j)).filter (fun j => s (tau j) = true)).card := by
                simp only [bit]; rw [Finset.sum_boole]; rfl
              rw [hsum]
              obtain ⟨k, hk⟩ : ∃ k, ((univ.filter (fun j => e ∈ X.sets j)).filter (fun j => s (tau j) = true)).card = k := ⟨_, rfl⟩
              rw [hk] at hsplit ⊢
              have hk' : ((univ.filter (fun j => e ∈ X.sets j)).filter (fun j => ¬ s (tau j) = true)).card = 3 - k := by omega
              rw [hk']
              have hk3 : k ≤ 3 := by omega
              have hsk : sig (xcNet X) kappa true (s kappa) = if s kappa then 7/12 else 5/12 := by
                cases s kappa <;> norm_num [sig, xcNet, kappa]
              have hsk0 : sig (xcNet X) kappa false (s kappa) = if s kappa then 7/27 else 20/27 := by
                cases s kappa <;> norm_num [sig, xcNet, kappa]
              have hse : ∀ θ, sig (xcNet X) (epsilon e) θ (s (epsilon e)) = 1/2 := by
                intro θ; cases s (epsilon e) <;> norm_num [sig, xcNet, epsilon]
              rw [hsk, hsk0, hse, hse]
              cases s kappa <;> interval_cases k <;> norm_num [bit]
            have hsig : ∀ c : CoreProfile n, c ∈ sigma X ↔ ∀ e, 2 * bit c.1 +
                ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (c.2 j) = 3 := by
              intro c; simp [sigma]
            have info2 : rInfo (xcNet X) 2 observer s =
                univ.filter (fun s' : XAgent n → Bool => s' observer = s observer ∧ project s' ∈ sigma X) := by
              ext s'
              simp only [rInfo, rInfoUsing, mem_filter, mem_univ, true_and]
              rw [nbrObs, hsig]
              simp only [project]
              simp only [← rep1eps]
              constructor
              · rintro ⟨h0, h⟩
                refine ⟨h0, fun e => ?_⟩
                have := h (epsilon e) (by simp) 1 (by norm_num)
                rw [ru21, ru21] at this
                rw [this]; exact (hs e).2
              · rintro ⟨h0, h⟩
                refine ⟨h0, fun k hk τ hτ => ?_⟩
                rw [mem_insert, mem_image] at hk
                interval_cases τ
                · rw [ru20, ru20]
                  rcases hk with rfl | ⟨e, _, rfl⟩
                  · rw [rep0obs, rep0obs]
                  · rw [rep0eps, rep0eps]
                · rw [ru21, ru21]
                  rcases hk with rfl | ⟨e, _, rfl⟩
                  · rw [rep1obs, rep1obs]
                  · rw [h e, (hs e).2]
            rw [info2]
            rw [← Finset.sum_fiberwise_of_maps_to (g := project) (t := sigma X) (by
              intro x hx; exact (mem_filter.1 hx).2.2)]
            unfold coreMass
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c hc
            let v : XAgent n → Bool := Sum.elim (fun j => c.2 j) (Sum.elim (fun _ => false) (fun b => if b then s observer else c.1))
            have hJ : (univ.filter (fun s' : XAgent n → Bool => s' observer = s observer ∧ project s' ∈ sigma X)).filter
                (fun s' => project s' = c) = univ.filter (fun s' : XAgent n → Bool =>
                  ∀ j ∈ insert observer (insert kappa (univ.image tau)), s' j = v j) := by
              ext s'
              rw [mem_filter, mem_filter, mem_filter]
              simp only [mem_univ, true_and]
              have hvo : v observer = s observer := rfl
              have hvk : v kappa = c.1 := rfl
              have hvt : ∀ i, v (tau i) = c.2 i := fun _ => rfl
              constructor
              · rintro ⟨⟨h0, _⟩, hp⟩ j hj
                rw [mem_insert, mem_insert, mem_image] at hj
                rcases hj with rfl | rfl | ⟨i, _, rfl⟩
                · rw [hvo, h0]
                · rw [hvk, ← hp]; rfl
                · rw [hvt, ← hp]; rfl
              · intro h
                have h0 := h observer (by simp)
                have hp : project s' = c := by
                  refine Prod.ext ?_ (funext fun i => ?_)
                  · exact (h kappa (by simp)).trans hvk
                  · exact (h (tau i) (by simp)).trans (hvt i)
                exact ⟨⟨h0.trans hvo, hp ▸ hc⟩, hp⟩
            rw [hJ, cyl]
            have hne1 : observer ∉ insert kappa (univ.image (tau (n := n))) := by simp [observer, kappa, tau]
            have hne2 : kappa ∉ univ.image (tau (n := n)) := by simp [kappa, tau]
            have htinj : Set.InjOn (tau (n := n)) ↑(univ : Finset (Fin n)) := by
              intro a _ b _ h; simpa [tau] using h
            rw [prod_insert hne1, prod_insert hne2, prod_image htinj]
            have hso : sig (xcNet X) observer θ (v observer) = 1/2 := by
              cases v observer <;> norm_num [sig, xcNet, observer]
            rw [hso]
            congr 1
          have hbel : ∀ {n : ℕ} (X : RXC3 n) (s : XAgent n → Bool),
              0 < ∑ s' ∈ rInfo (xcNet X) 2 observer s, jointProb (xcNet X) true s' ∧
              0 < ∑ s' ∈ rInfo (xcNet X) 2 observer s, jointProb (xcNet X) false s' := by
            intro n X s
            have hsigpos : ∀ a θ b, 0 < sig (xcNet X) a θ b := by
              intro a θ b
              rcases a with j | e | b'
              · cases θ <;> cases b <;> norm_num [sig, xcNet]
              · cases θ <;> cases b <;> norm_num [sig, xcNet]
              · cases b' <;> cases θ <;> cases b <;> norm_num [sig, xcNet]
            have hjp : ∀ θ s', 0 < jointProb (xcNet X) θ s' := fun θ s' =>
              Finset.prod_pos (fun a _ => hsigpos a θ _)
            have hmem : s ∈ rInfo (xcNet X) 2 observer s := by simp [rInfo, rInfoUsing]
            exact ⟨Finset.sum_pos (fun s' _ => hjp true s') ⟨s, hmem⟩,
              Finset.sum_pos (fun s' _ => hjp false s') ⟨s, hmem⟩⟩
          have hbelf : ∀ {n : ℕ} (X : RXC3 n) (s : XAgent n → Bool),
              belief (xcNet X) 2 observer s true =
                  Real.exp (rLog (xcNet X) 2 observer s) /
                    (1 + Real.exp (rLog (xcNet X) 2 observer s)) := by
            intro n X s
            obtain ⟨h1, h0⟩ := hbel X s
            unfold rLog belief post
            rw [Fintype.sum_bool]
            set a := ∑ s' ∈ rInfo (xcNet X) 2 observer s, jointProb (xcNet X) true s'
            set b := ∑ s' ∈ rInfo (xcNet X) 2 observer s, jointProb (xcNet X) false s'
            rw [Real.exp_log (by positivity)]
            field_simp
            ring
          have hrlog : ∀ {n : ℕ} (X : RXC3 n) (s : XAgent n → Bool), Observed X s →
              rLog (xcNet X) 2 observer s = Real.log (coreMass X true / coreMass X false) := by
            intro n X s hs
            obtain ⟨h1, h0⟩ := hbel X s
            have e1 := hnet X s hs true
            have e0 := hnet X s hs false
            unfold rLog belief post
            rw [Fintype.sum_bool]
            have p1 : 0 < coreMass X true := by rw [e1] at h1; linarith
            have p0 : 0 < coreMass X false := by rw [e0] at h0; linarith
            congr 1
            rw [e1, e0]
            field_simp
          have hC : ∃ C : ℝ, ∀ {n : ℕ} (X : RXC3 n), HasCover X →
              ∀ s : XAgent n → Bool, Observed X s →
                rLog (xcNet X) 2 observer s < (n : ℝ) * ellHat + C := by
            refine ⟨Real.log (27/7) + 1, ?_⟩
            intro n X hX s hs
            obtain ⟨hN, hM1, hM0⟩ := hmass X hX
            rw [hrlog X s hs, hM1, hM0]
            have hNr : (1:ℝ) ≤ coverCount X := by exact_mod_cast hN
            have hq : 0 < qUnder ^ n := pow_pos hqUpos n
            have ha : 0 < (1/2:ℝ)^n := by positivity
            have hb : 0 ≤ (1/3:ℝ)^n := by positivity
            set N : ℝ := (coverCount X : ℝ)
            have hM0pos : 0 < N * (7/27) * qUnder^n + (1 - 7/27) * (1/3)^n :=
              add_pos_of_pos_of_nonneg (mul_pos (mul_pos (by linarith) (by norm_num)) hq)
                (mul_nonneg (by norm_num) hb)
            have hM1pos : 0 < N * (7/12) * (1/2)^n + (1 - 7/12) * (1/2)^n :=
              add_pos_of_pos_of_nonneg (mul_pos (mul_pos (by linarith) (by norm_num)) ha)
                (mul_nonneg (by norm_num) ha.le)
            have hle : (N * (7/12) * (1/2)^n + (1 - 7/12) * (1/2)^n) /
                (N * (7/27) * qUnder^n + (1 - 7/27) * (1/3)^n) ≤ 27/7 * (qBar/qUnder)^n := by
              rw [div_le_iff₀ hM0pos, hqBar, show ((1:ℝ)/2/qUnder)^n = (1/2)^n / qUnder^n from div_pow _ _ _]
              have h1 : 27/7 * ((1/2:ℝ)^n / qUnder^n) * (N * (7/27) * qUnder^n) = N * (1/2)^n := by
                field_simp
              have h2 : 0 ≤ 27/7 * ((1/2:ℝ)^n / qUnder^n) * ((1 - 7/27) * (1/3)^n) := by
                apply mul_nonneg (by positivity) (mul_nonneg (by norm_num) hb)
              rw [mul_add, h1]
              nlinarith [mul_le_mul_of_nonneg_right hNr ha.le]
            calc Real.log ((N * (7/12) * (1/2)^n + (1 - 7/12) * (1/2)^n) /
                  (N * (7/27) * qUnder^n + (1 - 7/27) * (1/3)^n))
                ≤ Real.log (27/7 * (qBar/qUnder)^n) := Real.log_le_log (div_pos hM1pos hM0pos) hle
              _ = Real.log (27/7) + n * ellHat := by
                  rw [Real.log_mul (by norm_num) (by rw [hqBar]; positivity), Real.log_pow]; rfl
              _ < n * ellHat + (Real.log (27/7) + 1) := by linarith
          refine ⟨hqBar, ?_, hell, hC, ?_⟩
          · intro n X hX
            obtain ⟨hN, hM1, hM0⟩ := hmass X hX
            exact ⟨hN, by rw [hqBar]; exact hM1, hM0, fun s _ => hbelf X s⟩
          · obtain ⟨C, hCb⟩ := hC
            refine ⟨-ellHat/2, by linarith, ⌈2 * C / (-ellHat)⌉₊, ?_⟩
            intro n hn X hX s hs
            rw [hbelf X s]
            have hφ := hCb X hX s hs
            have hnr : 2 * C / (-ellHat) ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
            rw [div_le_iff₀ (by linarith)] at hnr
            set φ := rLog (xcNet X) 2 observer s
            calc Real.exp φ / (1 + Real.exp φ) < Real.exp φ :=
                  div_lt_self (Real.exp_pos _) (by linarith [Real.exp_pos φ])
              _ < Real.exp (n * ellHat + C) := Real.exp_lt_exp.2 hφ
              _ ≤ Real.exp (-(-ellHat/2) * n) := Real.exp_le_exp.2 (by nlinarith)
