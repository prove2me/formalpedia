-- Prove2me | solution 1 for BayesGroupHard.VertexCover.Supplement.section_B_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:28:04.151779+00:00
-- url     : https://prove2.me/submissions/73df8ec8-6fab-4fa8-bc66-0f72ee6e5f14

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Supplement_Network

open BayesGroupHard
open BayesGroupHard.VertexCover
open BayesGroupHard.VertexCover.Supplement

open Finset

/-- §B.1, p. 33 (NO case): without an exact cover, `Σ = {(0,1,…,1)}`, agent `i`'s time-two
log-belief ratio is exactly `2ℓ_0 + n log(3/2)` and `µ_i,2(0) = 1/(1 + e^{φ_i,2})`; and there are
`c > 0` and `N`, independent of the instance, with `µ_i,2(0) < exp(-c n)` for every NO instance
with `n ≥ N`. -/
theorem solution :
    (∀ {n : ℕ} (X : RXC3 n), ¬ HasCover X →
      sigma X = {baseProfile n} ∧
      ∀ s : XAgent n → Bool, Observed X s →
        rLog (xcNet X) 2 observer s = 2 * ellZero + (n : ℝ) * Real.log (3 / 2) ∧
        belief (xcNet X) 2 observer s false =
          1 / (1 + Real.exp (rLog (xcNet X) 2 observer s))) ∧
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ X : RXC3 n, ¬ HasCover X →
      ∀ s : XAgent n → Bool, Observed X s →
        belief (xcNet X) 2 observer s false < Real.exp (-c * n) := by
          have hRU : ∀ {n : ℕ} (N : BinNet (XAgent n)) (t τ : ℕ), τ < t →
              ∀ j s, reportsUpTo N t τ j s = report N τ j s := by
            intro n N t
            induction t with
            | zero => intro τ h; omega
            | succ t ih =>
              intro τ hτ j s
              simp only [reportsUpTo]
              split_ifs with h1 h2
              · exact ih τ h1 j s
              · subst h2; rfl
              · omega
          have hmem : ∀ {n : ℕ} (N : BinNet (XAgent n)) (t : ℕ) (i : XAgent n) (s s' : XAgent n → Bool),
              s' ∈ rInfo N t i s ↔
                (s' i = s i ∧ ∀ j ∈ N.nbr i, ∀ τ < t, report N τ j s' = report N τ j s) := by
            intro n N t i s s'
            simp only [rInfo, rInfoUsing, mem_filter, mem_univ, true_and]
            constructor
            · rintro ⟨h1, h2⟩
              refine ⟨h1, fun j hj τ hτ => ?_⟩
              rw [← hRU N t τ hτ, ← hRU N t τ hτ]; exact h2 j hj τ hτ
            · rintro ⟨h1, h2⟩
              refine ⟨h1, fun j hj τ hτ => ?_⟩
              rw [hRU N t τ hτ, hRU N t τ hτ]; exact h2 j hj τ hτ
          have hcyl : ∀ {n : ℕ} (N : BinNet (XAgent n)) (I : Finset (XAgent n → Bool))
              (F : Finset (XAgent n)) (s : XAgent n → Bool),
              (∀ s', s' ∈ I ↔ ∀ i ∈ F, s' i = s i) →
              ∀ θ, ∑ s' ∈ I, jointProb N θ s' = ∏ i ∈ F, sig N i θ (s i) := by
            intro n N I F s hI θ
            have hI' : I = Fintype.piFinset
                (fun i => if i ∈ F then ({s i} : Finset Bool) else univ) := by
              ext x
              rw [hI, Fintype.mem_piFinset]
              constructor
              · intro h i
                split_ifs with hi
                · simp [h i hi]
                · simp
              · intro h i hi
                have := h i
                rw [if_pos hi] at this
                simpa using this
            rw [hI']
            unfold jointProb
            rw [← Finset.prod_univ_sum]
            rw [show ∏ i ∈ F, sig N i θ (s i) = ∏ i, if i ∈ F then sig N i θ (s i) else 1 by
              rw [Finset.prod_ite_mem, univ_inter]]
            refine Finset.prod_congr rfl (fun i _ => ?_)
            split_ifs
            · simp
            · simp [sig]
          have hpost : ∀ {n : ℕ} (N : BinNet (XAgent n)) (I : Finset (XAgent n → Bool))
              (F : Finset (XAgent n)) (s : XAgent n → Bool),
              (∀ s', s' ∈ I ↔ ∀ i ∈ F, s' i = s i) → ∀ θ,
              post N θ I = (∏ i ∈ F, sig N i θ (s i)) /
                (∏ i ∈ F, sig N i true (s i) + ∏ i ∈ F, sig N i false (s i)) := by
            intro n N I F s hI θ
            unfold post
            rw [Fintype.sum_bool, hcyl N I F s hI θ, hcyl N I F s hI true, hcyl N I F s hI false]
            rw [← mul_add, mul_div_mul_left _ _ (by norm_num : (1/2:ℝ) ≠ 0)]
          have hrep0 : ∀ {n : ℕ} (N : BinNet (XAgent n)) a s, report N 0 a s =
              sig N a true (s a) / (sig N a true (s a) + sig N a false (s a)) := by
            intro n N a s
            unfold report belief
            rw [hpost N _ {a} s (fun s' => by rw [hmem]; simp) true]
            simp
          have main : ∀ {n : ℕ} (X : RXC3 n), ¬ HasCover X →
              sigma X = {baseProfile n} ∧ ∀ s : XAgent n → Bool, Observed X s →
                belief (xcNet X) 2 observer s true =
                  (1/2 * (5/12 * (1/2:ℝ)^n)) / (1/2 * (5/12 * (1/2:ℝ)^n) + 1/2 * (20/27 * (1/3:ℝ)^n)) ∧
                belief (xcNet X) 2 observer s false =
                  (1/2 * (20/27 * (1/3:ℝ)^n)) / (1/2 * (5/12 * (1/2:ℝ)^n) + 1/2 * (20/27 * (1/3:ℝ)^n)) := by
            intro n X hX
            have hsig : sigma X = {baseProfile n} := by
              ext p
              simp only [sigma, mem_filter, mem_univ, true_and, mem_singleton]
              constructor
              · intro h
                obtain ⟨b, f⟩ := p
                have hc : ∀ e, ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (f j) =
                    #((univ.filter (fun j => e ∈ X.sets j)).filter (fun j => f j = true)) := by
                  intro e; rw [card_filter]; rfl
                cases b
                · simp only [baseProfile, Prod.mk.injEq, true_and]
                  funext j
                  obtain ⟨e, he⟩ : (X.sets j).Nonempty := by
                    rw [← card_pos, X.triple j]; norm_num
                  have h3 := h e
                  rw [hc e] at h3
                  simp only [bit] at h3
                  have h4 : #((univ.filter (fun j => e ∈ X.sets j)).filter (fun j => f j = true)) =
                      #(univ.filter (fun j => e ∈ X.sets j)) := by rw [X.regular e]; simpa using h3
                  exact filter_card_eq h4 j (by simp [he])
                · exfalso; apply hX
                  refine ⟨selected (true, f), fun e => ?_⟩
                  have h3 := h e
                  rw [hc e] at h3
                  simp only [bit] at h3
                  have : (selected (true, f)).filter (fun j => e ∈ X.sets j) =
                      (univ.filter (fun j => e ∈ X.sets j)).filter (fun j => f j = true) := by
                    ext j; simp [selected, and_comm]
                  rw [this]; simp at h3; omega
              · rintro rfl e
                simp [baseProfile, bit, X.regular e]
            refine ⟨hsig, ?_⟩
            intro s hobs
            set N := xcNet X with hN
            have sτ : ∀ j θ b, sig N (tau j) θ b =
                if b then (if θ then 1/2 else 1/3) else 1 - (if θ then 1/2 else 1/3) := by
              intro j θ b; rfl
            have sε : ∀ e θ b, sig N (epsilon e) θ b = if b then 1/2 else 1 - 1/2 := fun _ _ _ => rfl
            have sκ : ∀ θ b, sig N kappa θ b =
                if b then (if θ then 7/12 else 7/27) else 1 - (if θ then 7/12 else 7/27) :=
              fun _ _ => rfl
            have sο : ∀ θ b, sig N observer θ b = if b then 1/2 else 1 - 1/2 := fun _ _ => rfl
            have r0ε : ∀ e (s : XAgent n → Bool), report N 0 (epsilon e) s = 1/2 := by
              intro e s; rw [hrep0, sε, sε]; split_ifs <;> norm_num
            have r0ο : ∀ (s : XAgent n → Bool), report N 0 observer s = 1/2 := by
              intro s; rw [hrep0, sο, sο]; split_ifs <;> norm_num
            have r0τ : ∀ j (s s' : XAgent n → Bool), report N 0 (tau j) s' = report N 0 (tau j) s ↔ s' (tau j) = s (tau j) := by
              intro j s s'; rw [hrep0, hrep0, sτ, sτ, sτ, sτ]
              cases s' (tau j) <;> cases s (tau j) <;> norm_num
            have r0κ : ∀ (s s' : XAgent n → Bool), report N 0 kappa s' = report N 0 kappa s ↔ s' kappa = s kappa := by
              intro s s'; rw [hrep0, hrep0, sκ, sκ, sκ, sκ]
              cases s' kappa <;> cases s kappa <;> norm_num
            have hnbrο : N.nbr observer = insert observer (univ.image epsilon) := rfl
            have hnbrε : ∀ e, N.nbr (epsilon e) =
                insert (epsilon e) (insert kappa ((univ.filter (fun j => e ∈ X.sets j)).image tau)) :=
              fun _ => rfl
            have r1ο : ∀ (s : XAgent n → Bool), report N 1 observer s = 1/2 := by
              intro s
              unfold report belief
              rw [hpost N _ {observer} s (fun s' => ?_) true]
              · simp only [prod_singleton]; rw [sο, sο]; split_ifs <;> norm_num
              · rw [hmem]; simp only [mem_singleton, forall_eq]
                constructor
                · exact fun h => h.1
                · intro h; refine ⟨h, fun j hj τ hτ => ?_⟩
                  have : τ = 0 := by omega
                  subst this
                  rw [hnbrο] at hj
                  simp only [mem_insert, mem_image, mem_univ, true_and] at hj
                  rcases hj with rfl | ⟨e, rfl⟩
                  · rw [r0ο, r0ο]
                  · rw [r0ε, r0ε]
            have r1ε : ∀ e (s : XAgent n → Bool), report N 1 (epsilon e) s =
                (∏ i ∈ N.nbr (epsilon e), sig N i true (s i)) /
                (∏ i ∈ N.nbr (epsilon e), sig N i true (s i) + ∏ i ∈ N.nbr (epsilon e), sig N i false (s i)) := by
              intro e s; unfold report belief
              apply hpost N _ _ s _ true
              intro s'
              rw [hmem]
              constructor
              · rintro ⟨h1, h2⟩ i hi
                have := h2 i hi 0 (by norm_num)
                rw [hnbrε] at hi
                simp only [mem_insert, mem_image, mem_filter, mem_univ, true_and] at hi
                rcases hi with rfl | rfl | ⟨j, hj, rfl⟩
                · exact h1
                · exact (r0κ s s').1 this
                · exact (r0τ j s s').1 this
              · intro h
                refine ⟨h _ (N.self_mem _), fun i hi τ hτ => ?_⟩
                have : τ = 0 := by omega
                subst this
                have hi' := h i hi
                rw [hnbrε] at hi
                simp only [mem_insert, mem_image, mem_filter, mem_univ, true_and] at hi
                rcases hi with rfl | rfl | ⟨j, hj, rfl⟩
                · rw [r0ε, r0ε]
                · exact (r0κ s s').2 hi'
                · exact (r0τ j s s').2 hi'
            have hprodε : ∀ e (s : XAgent n → Bool) θ, ∏ i ∈ N.nbr (epsilon e), sig N i θ (s i) =
                sig N (epsilon e) θ (s (epsilon e)) * (sig N kappa θ (s kappa) *
                  ∏ j ∈ univ.filter (fun j => e ∈ X.sets j), sig N (tau j) θ (s (tau j))) := by
              intro e s θ
              rw [hnbrε, prod_insert, prod_insert, prod_image]
              · intro a _ b _ h; exact Sum.inl_injective h
              · simp [kappa, tau]
              · simp [epsilon, kappa, tau]
            have hprodT : ∀ (T : Finset (Fin n)) (s : XAgent n → Bool) θ, ∏ j ∈ T, sig N (tau j) θ (s (tau j)) =
                (if θ then 1/2 else 1/3) ^ #(T.filter (fun j => s (tau j) = true)) *
                (1 - if θ then 1/2 else 1/3) ^ #(T.filter (fun j => ¬ s (tau j) = true)) := by
              intro T s θ
              simp only [sτ]
              rw [prod_ite, prod_const, prod_const]
            have r1εiff : ∀ e (s : XAgent n → Bool), report N 1 (epsilon e) s = 243/371 ↔
                2 * bit (s kappa) + ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (s (tau j)) = 3 := by
              intro e s
              rw [r1ε, hprodε, hprodε, hprodT, hprodT]
              have hsum : ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (s (tau j)) =
                  #((univ.filter (fun j => e ∈ X.sets j)).filter (fun j => s (tau j) = true)) := by
                rw [card_filter]; rfl
              rw [hsum]
              have hkm := card_filter_add_card_filter_not (s := univ.filter (fun j => e ∈ X.sets j))
                (fun j => s (tau j) = true)
              rw [X.regular e] at hkm
              generalize #((univ.filter (fun j => e ∈ X.sets j)).filter (fun j => s (tau j) = true)) = k
                at hkm ⊢
              generalize #((univ.filter (fun j => e ∈ X.sets j)).filter (fun j => ¬ s (tau j) = true)) = m
                at hkm ⊢
              have hm : m = 3 - k := by omega
              subst hm
              have hk : k ≤ 3 := by omega
              rw [sε, sε, sκ, sκ]
              cases s kappa <;> cases s (epsilon e) <;> interval_cases k <;> norm_num [bit]
            have hsigmaiff : ∀ (s' : XAgent n → Bool), (∀ e, report N 1 (epsilon e) s' = 243/371) ↔ project s' ∈ sigma X := by
              intro s'
              simp only [sigma, mem_filter, mem_univ, true_and, project]
              exact forall_congr' (fun e => r1εiff e s')
            have hsproj : project s = baseProfile n := by
              rw [← mem_singleton, ← hsig, ← hsigmaiff]; exact fun e => (hobs e).2
            have hsκ : s kappa = false := congrArg Prod.fst hsproj
            have hsτ : ∀ j, s (tau j) = true := fun j => congrFun (congrArg Prod.snd hsproj) j
            have hI2 : ∀ (s' : XAgent n → Bool), s' ∈ rInfo N 2 observer s ↔
                ∀ i ∈ insert observer (insert kappa (univ.image tau)), s' i = s i := by
              intro s'
              rw [hmem]
              constructor
              · rintro ⟨h1, h2⟩
                have hp : project s' = baseProfile n := by
                  rw [← mem_singleton, ← hsig, ← hsigmaiff]
                  intro e
                  rw [h2 (epsilon e) (by rw [hnbrο]; simp) 1 (by norm_num)]
                  exact (hobs e).2
                intro i hi
                simp only [mem_insert, mem_image, mem_univ, true_and] at hi
                rcases hi with rfl | rfl | ⟨j, rfl⟩
                · exact h1
                · rw [hsκ]; exact congrArg Prod.fst hp
                · rw [hsτ]; exact congrFun (congrArg Prod.snd hp) j
              · intro h
                have hp' : project s' = baseProfile n := by
                  simp only [project, baseProfile, Prod.mk.injEq]
                  refine ⟨by rw [h kappa (by simp), hsκ], funext fun j => ?_⟩
                  rw [h (tau j) (by simp), hsτ]
                refine ⟨h _ (by simp), fun i hi τ hτ => ?_⟩
                rw [hnbrο] at hi
                simp only [mem_insert, mem_image, mem_univ, true_and] at hi
                interval_cases τ
                · rcases hi with rfl | ⟨e, rfl⟩
                  · rw [r0ο, r0ο]
                  · rw [r0ε, r0ε]
                · rcases hi with rfl | ⟨e, rfl⟩
                  · rw [r1ο, r1ο]
                  · rw [(hobs e).2]
                    exact (hsigmaiff s').2 (by rw [hp', hsig]; simp) e
            have hG : ∀ θ, ∏ i ∈ insert observer (insert kappa (univ.image tau)), sig N i θ (s i) =
                1/2 * ((if θ then 5/12 else 20/27) * (if θ then 1/2 else 1/3) ^ n) := by
              intro θ
              rw [prod_insert, prod_insert, prod_image]
              · simp only [hsκ, hsτ, sτ, sκ, sο, prod_const, card_univ, Fintype.card_fin]
                cases θ <;> cases s observer <;> norm_num
              · intro a _ b _ h; exact Sum.inl_injective h
              · simp [kappa, tau]
              · simp [observer, kappa, tau]
            unfold belief
            rw [hpost N _ _ s hI2 true, hpost N _ _ s hI2 false, hG true, hG false]
            simp only [Bool.false_eq_true, ↓reduceIte, and_self]
          have hratio : ∀ n : ℕ, (1/2 * (5/12 * (1/2:ℝ)^n)) / (1/2 * (20/27 * (1/3:ℝ)^n))
              = 9/16 * (3/2:ℝ)^n := by
            intro n
            rw [show (1/2:ℝ)^n = (3/2)^n * (1/3)^n by rw [← mul_pow]; norm_num]
            have : (0:ℝ) < (1/3)^n := by positivity
            field_simp
            ring
          have hell : 2 * ellZero = Real.log (9/16) := by
            rw [ellZero, show (9/16:ℝ) = ((1 - 1/2)/(1 - 1/3))^2 by norm_num, Real.log_pow]; norm_num
          have key : ∀ a b : ℝ, 0 < b → b / (a + b) = 1 / (1 + a / b) := by
            intro a b hb
            rw [one_add_div hb.ne', one_div_div, add_comm]
          have part1 : ∀ {n : ℕ} (X : RXC3 n), ¬ HasCover X →
              sigma X = {baseProfile n} ∧
              ∀ s : XAgent n → Bool, Observed X s →
                rLog (xcNet X) 2 observer s = 2 * ellZero + (n : ℝ) * Real.log (3 / 2) ∧
                belief (xcNet X) 2 observer s false =
                  1 / (1 + Real.exp (rLog (xcNet X) 2 observer s)) := by
            intro n X hX
            obtain ⟨hs, hb⟩ := main X hX
            refine ⟨hs, fun s hobs => ?_⟩
            obtain ⟨h1, h0⟩ := hb s hobs
            have hr : rLog (xcNet X) 2 observer s = Real.log (9/16 * (3/2:ℝ)^n) := by
              rw [rLog, h1, h0, div_div_div_cancel_right₀ (ne_of_gt (by positivity)), hratio]
            refine ⟨?_, ?_⟩
            · rw [hr, hell, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
            · rw [hr, Real.exp_log (by positivity), h0, ← hratio]
              exact key _ _ (by positivity)
          refine ⟨part1, Real.log (5/4), Real.log_pos (by norm_num), 4, ?_⟩
          intro n hn X hX s hobs
          obtain ⟨-, hb⟩ := main X hX
          rw [(hb s hobs).2]
          have hexp : Real.exp (-Real.log (5/4) * n) = (4/5:ℝ)^n := by
            rw [show -Real.log (5/4) * (n:ℝ) = (n:ℝ) * Real.log (4/5) by
              rw [show (4/5:ℝ) = (5/4)⁻¹ by norm_num, Real.log_inv]; ring, Real.exp_nat_mul,
              Real.exp_log (by norm_num)]
          rw [hexp, div_lt_iff₀ (by positivity)]
          have hy : (1296/625:ℝ) ≤ (6/5)^n := by
            calc (1296/625:ℝ) = (6/5)^4 := by norm_num
              _ ≤ (6/5)^n := pow_le_pow_right₀ (by norm_num) hn
          have hx : (0:ℝ) < (1/3)^n := by positivity
          have hz : (0:ℝ) < (4/5)^n := by positivity
          have hzw : (4/5:ℝ)^n * (1/2)^n = (6/5)^n * (1/3)^n := by
            rw [← mul_pow, ← mul_pow]; norm_num
          nlinarith [mul_pos hz hx, mul_le_mul_of_nonneg_right hy hx.le]
