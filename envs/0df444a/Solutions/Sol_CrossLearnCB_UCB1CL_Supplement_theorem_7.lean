-- Prove2me | solution 1 for CrossLearnCB.UCB1CL.Supplement.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:11:22.99918+00:00
-- url     : https://prove2.me/submissions/6ba3824b-6336-42a3-980d-ceffdfd6a1c6

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Model
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Protocol

open CrossLearnCB
open CrossLearnCB.UCB1CL
open CrossLearnCB.UCB1CL.Supplement

/-- Theorem 7, p. 39: with `K = 2` arms, uniform contexts, and each round–context pair an
independent fair coin deciding which arm pays `1` (the other pays `0`), the expected ex post
regret of every algorithm, under any CL graphs, is at least `T/2 − ε` once the number of
contexts `C` is large enough; i.e. `liminf_{C→∞} E[Reg_Post(A)] ≥ T/2`, uniformly in `A`. -/
theorem solution (T : ℕ) : ∀ ε : ℝ, 0 < ε → ∃ C₀ : ℕ, ∀ C : ℕ, C₀ ≤ C →
    ∀ G : Fin 2 → Fin C → Fin C → Prop, HasSelfLoops G →
    ∀ A : Policy 2 C, A.IsValid →
      (T : ℝ) / 2 - ε ≤ coinExPostRegret T C G A := by
        classical
        have key : ∀ (α : Type) [Fintype α] (g h : (t : ℕ) → (Fin t → α) → α → ℝ) (m : ℕ → ℝ)
          (hg0 : ∀ t p x, 0 ≤ g t p x) (hg1 : ∀ t p, ∑ x, g t p x = 1)
          (hm : ∀ t p, m t ≤ ∑ x, g t p x * h t p x), ∀ n : ℕ,
          (∑ ω : Fin n → α, ∏ t : Fin n, g t (fun s : Fin t => ω (Fin.castLE t.2.le s)) (ω t)) = 1 ∧
          (∑ t : Fin n, m t) ≤ ∑ ω : Fin n → α,
            (∏ t : Fin n, g t (fun s : Fin t => ω (Fin.castLE t.2.le s)) (ω t)) *
              ∑ t : Fin n, h t (fun s : Fin t => ω (Fin.castLE t.2.le s)) (ω t) := by
          intro α _ g h m hg0 hg1 hm
          intro n
          induction n with
          | zero => simp
          | succ n ih =>
            have hsplit : ∀ F : (Fin (n+1) → α) → ℝ,
                ∑ ω, F ω = ∑ ω' : Fin n → α, ∑ x : α, F (Fin.snoc ω' x) := by
              intro F
              rw [← (Fin.snocEquiv (fun _ => α)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
              rfl
            have hpre : ∀ (ω' : Fin n → α) (x : α) (t : Fin n),
                (fun s : Fin ((Fin.castSucc t : Fin (n+1)) : ℕ) =>
                  (Fin.snoc ω' x : Fin (n+1) → α) (Fin.castLE (Fin.castSucc t).2.le s))
                  = (fun s : Fin t => ω' (Fin.castLE t.2.le s)) := by
              intro ω' x t
              funext s
              have : (Fin.castLE (Fin.castSucc t).2.le s : Fin (n+1)) = Fin.castSucc (Fin.castLE t.2.le s) := by
                ext; simp
              rw [this, Fin.snoc_castSucc]
            have hlast : ∀ (ω' : Fin n → α) (x : α),
                (fun s : Fin ((Fin.last n : Fin (n+1)) : ℕ) =>
                  (Fin.snoc ω' x : Fin (n+1) → α) (Fin.castLE (Fin.last n).2.le s)) = ω' := by
              intro ω' x
              funext s
              have : (Fin.castLE (Fin.last n).2.le s : Fin (n+1)) = Fin.castSucc s := by
                ext; simp
              rw [this, Fin.snoc_castSucc]
            have hprod : ∀ (ω' : Fin n → α) (x : α),
                (∏ t : Fin (n+1), g t (fun s : Fin t => (Fin.snoc ω' x : Fin (n+1) → α) (Fin.castLE t.2.le s))
                  ((Fin.snoc ω' x : Fin (n+1) → α) t))
                = (∏ t : Fin n, g t (fun s : Fin t => ω' (Fin.castLE t.2.le s)) (ω' t)) * g n ω' x := by
              intro ω' x
              rw [Fin.prod_univ_castSucc]
              congr 1
              · apply Finset.prod_congr rfl
                intro t _
                rw [Fin.snoc_castSucc]
                exact congrArg (fun p => g t p (ω' t)) (hpre ω' x t)
              · rw [Fin.snoc_last]
                exact congrArg (fun p => g n p x) (hlast ω' x)
            have hsum : ∀ (ω' : Fin n → α) (x : α),
                (∑ t : Fin (n+1), h t (fun s : Fin t => (Fin.snoc ω' x : Fin (n+1) → α) (Fin.castLE t.2.le s))
                  ((Fin.snoc ω' x : Fin (n+1) → α) t))
                = (∑ t : Fin n, h t (fun s : Fin t => ω' (Fin.castLE t.2.le s)) (ω' t)) + h n ω' x := by
              intro ω' x
              rw [Fin.sum_univ_castSucc]
              congr 1
              · apply Finset.sum_congr rfl
                intro t _
                rw [Fin.snoc_castSucc]
                exact congrArg (fun p => h t p (ω' t)) (hpre ω' x t)
              · rw [Fin.snoc_last]
                exact congrArg (fun p => h n p x) (hlast ω' x)
            obtain ⟨ih1, ih2⟩ := ih
            constructor
            · rw [hsplit]
              simp_rw [hprod, ← Finset.mul_sum, hg1, mul_one]
              exact ih1
            · rw [hsplit]
              simp_rw [hprod, hsum]
              have : ∀ ω' : Fin n → α, ∑ x, (∏ t : Fin n, g t (fun s : Fin t => ω' (Fin.castLE t.2.le s)) (ω' t)) * g n ω' x *
                  ((∑ t : Fin n, h t (fun s : Fin t => ω' (Fin.castLE t.2.le s)) (ω' t)) + h n ω' x)
                  = (∏ t : Fin n, g t (fun s : Fin t => ω' (Fin.castLE t.2.le s)) (ω' t)) *
                    (∑ t : Fin n, h t (fun s : Fin t => ω' (Fin.castLE t.2.le s)) (ω' t)) +
                    (∏ t : Fin n, g t (fun s : Fin t => ω' (Fin.castLE t.2.le s)) (ω' t)) * ∑ x, g n ω' x * h n ω' x := by
                intro ω'
                generalize (∏ t : Fin n, g t (fun s : Fin t => ω' (Fin.castLE t.2.le s)) (ω' t)) = P
                generalize (∑ t : Fin n, h t (fun s : Fin t => ω' (Fin.castLE t.2.le s)) (ω' t)) = S
                have e : ∀ x, P * g n ω' x * (S + h n ω' x) = P * S * g n ω' x + P * (g n ω' x * h n ω' x) := by
                  intro x; ring
                simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum, hg1, mul_one]
              simp_rw [this, Finset.sum_add_distrib]
              rw [Fin.sum_univ_castSucc]
              simp only [Fin.val_castSucc, Fin.val_last]
              have h3 : m n ≤ ∑ ω' : Fin n → α, (∏ t : Fin n, g t (fun s : Fin t => ω' (Fin.castLE t.2.le s)) (ω' t)) *
                  ∑ x, g n ω' x * h n ω' x := by
                calc m n = ∑ ω' : Fin n → α, (∏ t : Fin n, g t (fun s : Fin t => ω' (Fin.castLE t.2.le s)) (ω' t)) * m n := by
                      rw [← Finset.sum_mul, ih1, one_mul]
                  _ ≤ _ := by
                    apply Finset.sum_le_sum; intro ω' _
                    apply mul_le_mul_of_nonneg_left (hm _ _)
                    exact Finset.prod_nonneg (fun t _ => hg0 _ _ _)
              linarith
        intro ε hε
        refine ⟨⌈(T:ℝ)^2 / ε⌉₊ + 1, ?_⟩
        intro C hC G _hG A hA
        have hCpos : (0:ℝ) < C := by
          have : 1 ≤ C := le_trans (Nat.le_add_left 1 _) hC
          exact_mod_cast this
        have hCbig : (T:ℝ)^2 / ε < C := by
          have h1 := Nat.le_ceil ((T:ℝ)^2 / ε)
          have h2 : ((⌈(T:ℝ)^2 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ C := by exact_mod_cast hC
          push_cast at h2
          linarith
        have hTC : (T:ℝ)^2 / C ≤ ε := by
          rw [div_le_iff₀ hCpos]
          rw [div_lt_iff₀ hε] at hCbig
          linarith
        let H : (t : ℕ) → (Fin t → (Fin C × Fin 2) × (Fin C → Bool)) → (Fin t → Obs 2 C) :=
          fun t p s => ((p s).1.1, (p s).1.2,
            fun c' => if G (p s).1.2 (p s).1.1 c' then
              (if ((p s).2 c' = true ↔ (p s).1.2 = 0) then (1:ℝ) else 0) else 0)
        let g : (t : ℕ) → (Fin t → (Fin C × Fin 2) × (Fin C → Bool)) → (Fin C × Fin 2) × (Fin C → Bool) → ℝ :=
          fun t p x => (1 / (C:ℝ)) * A t (H t p) x.1.1 x.1.2 * ((2:ℝ)^C)⁻¹
        let h : (t : ℕ) → (Fin t → (Fin C × Fin 2) × (Fin C → Bool)) → (Fin C × Fin 2) × (Fin C → Bool) → ℝ :=
          fun t p x => (1 - if x.1.1 ∈ Finset.univ.image (fun s => (p s).1.1) then 1 else 0)
            - (if (x.2 x.1.1 = true ↔ x.1.2 = 0) then 1 else 0)
        let m : ℕ → ℝ := fun t => 1 / 2 - t / C
        have hg0 : ∀ t p x, 0 ≤ g t p x := by
          intro t p x
          have := hA.1 t (H t p) x.1.1 x.1.2
          positivity
        have hbool : ∀ f : (Fin C → Bool) → ℝ, ∑ β : Fin C → Bool, f β = ∑ β : Fin C → Bool, f (fun c => !β c) := by
          intro f
          let e : (Fin C → Bool) ≃ (Fin C → Bool) :=
            ⟨fun (β : Fin C → Bool) c => !β c, fun (β : Fin C → Bool) c => !β c,
              fun β => by funext c; simp, fun β => by funext c; simp⟩
          exact (e.sum_comp f).symm
        have hcardB : ∑ _β : Fin C → Bool, (1:ℝ) = (2:ℝ)^C := by
          simp
        have hβc : ∀ a : ℝ, ∑ _β : Fin C → Bool, a * ((2:ℝ)^C)⁻¹ = a := by
          intro a
          rw [Finset.sum_const, Finset.card_univ]
          simp
          field_simp
        have hAsum : ∀ t q c, ∑ i, A t q c i = 1 := fun t q c => hA.2 t q c
        have hg1 : ∀ t p, ∑ x, g t p x = 1 := by
          intro t p
          simp only [g, Fintype.sum_prod_type, hβc]
          simp_rw [← Finset.mul_sum, hAsum]
          simp
          exact inv_mul_cancel₀ (ne_of_gt hCpos)
        have hr : ∀ (c : Fin C) (i : Fin 2),
            ∑ β : Fin C → Bool, (if (β c = true ↔ i = 0) then (1:ℝ) else 0) = (2:ℝ)^C / 2 := by
          intro c i
          have e1 := hbool (fun β => if (β c = true ↔ i = 0) then (1:ℝ) else 0)
          have e2 : ∀ β : Fin C → Bool, (if (β c = true ↔ i = 0) then (1:ℝ) else 0)
              + (if ((fun c => !β c) c = true ↔ i = 0) then (1:ℝ) else 0) = 1 := by
            intro β
            cases hb : β c <;> by_cases hi : i = 0 <;> simp [hb, hi]
          have e3 : ∑ β : Fin C → Bool, ((if (β c = true ↔ i = 0) then (1:ℝ) else 0)
              + (if ((fun c => !β c) c = true ↔ i = 0) then (1:ℝ) else 0)) = (2:ℝ)^C := by
            simp_rw [e2]; exact hcardB
          rw [Finset.sum_add_distrib, ← e1] at e3
          linarith
        have hm : ∀ t p, m t ≤ ∑ x, g t p x * h t p x := by
          intro t p
          set S := Finset.univ.image (fun s : Fin t => (p s).1.1) with hS
          have hScard : (S.card : ℝ) ≤ t := by
            have := Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := fun s : Fin t => (p s).1.1)
            simp only [Finset.card_univ, Fintype.card_fin] at this
            exact_mod_cast this
          have step1 : ∀ (c : Fin C) (i : Fin 2), ∑ β : Fin C → Bool, g t p ((c, i), β) * h t p ((c, i), β)
              = 1 / (C:ℝ) * A t (H t p) c i * ((1 - if c ∈ S then 1 else 0) - 1/2) := by
            intro c i
            simp only [g, h]
            have : ∀ β : Fin C → Bool, 1 / (C:ℝ) * A t (H t p) c i * ((2:ℝ)^C)⁻¹ *
                ((1 - if c ∈ S then 1 else 0) - if (β c = true ↔ i = 0) then 1 else 0)
                = 1 / (C:ℝ) * A t (H t p) c i * ((1 - if c ∈ S then 1 else 0)) * ((2:ℝ)^C)⁻¹
                  - 1 / (C:ℝ) * A t (H t p) c i * ((2:ℝ)^C)⁻¹ * (if (β c = true ↔ i = 0) then 1 else 0) := by
              intro β; ring
            rw [Finset.sum_congr rfl (fun β _ => this β), Finset.sum_sub_distrib, hβc, ← Finset.mul_sum, hr]
            field_simp
          have step2 : ∑ x, g t p x * h t p x
              = ∑ c : Fin C, 1 / (C:ℝ) * ((1 - if c ∈ S then 1 else 0) - 1/2) := by
            rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
            apply Finset.sum_congr rfl; intro c _
            simp_rw [step1, ← Finset.sum_mul, ← Finset.mul_sum, hAsum, mul_one]
          have step3 : ∑ c : Fin C, (if c ∈ S then (1:ℝ) else 0) = S.card := by
            rw [Finset.sum_boole]
            congr 2
            ext c; simp
          rw [step2, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, step3]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, m]
          have e : 1 / (C:ℝ) * (C - S.card - C * (1 / 2)) = 1 / 2 - S.card / C := by
            field_simp; ring
          rw [e]
          have : (S.card:ℝ) / C ≤ t / C := div_le_div_of_nonneg_right hScard hCpos.le
          linarith
        have hpre_ne : ∀ (ω : Fin T → (Fin C × Fin 2) × (Fin C → Bool)) (t1 t2 : Fin T), t1 < t2 →
            (ω t1).1.1 ∈ Finset.univ.image (fun s : Fin t2 => (ω (Fin.castLE t2.2.le s)).1.1) := by
          intro ω t1 t2 h12
          rw [Finset.mem_image]
          refine ⟨⟨t1.val, h12⟩, Finset.mem_univ _, ?_⟩
          have : (Fin.castLE t2.2.le (⟨t1.val, h12⟩ : Fin t2) : Fin T) = t1 := Fin.ext rfl
          rw [this]
        have hX : ∀ ω : Fin T → (Fin C × Fin 2) × (Fin C → Bool),
            ∑ t : Fin T, h t (fun s : Fin t => ω (Fin.castLE t.2.le s)) (ω t) ≤
            (∑ c, Finset.univ.sup' Finset.univ_nonempty
                (fun i => ∑ t ∈ Finset.univ.filter (fun t => (ω t).1.1 = c),
                  coinTable (fun t => (ω t).2) t i c))
              - ∑ t, coinTable (fun t => (ω t).2) t (ω t).1.2 (ω t).1.1 := by
          intro ω
          let V : Fin T → ℝ := fun t =>
            if (ω t).1.1 ∈ Finset.univ.image (fun s : Fin t => (ω (Fin.castLE t.2.le s)).1.1) then 0 else 1
          have e1 : ∑ t : Fin T, h t (fun s : Fin t => ω (Fin.castLE t.2.le s)) (ω t)
              = ∑ t, V t - ∑ t, coinTable (fun t => (ω t).2) t (ω t).1.2 (ω t).1.1 := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl; intro t _
            simp only [h, V, coinTable]
            split_ifs <;> norm_num
          rw [e1]
          apply sub_le_sub_right
          rw [← Finset.sum_fiberwise Finset.univ (fun t => (ω t).1.1) V]
          apply Finset.sum_le_sum
          intro c _
          by_cases hF : (Finset.univ.filter (fun t : Fin T => (ω t).1.1 = c)).Nonempty
          · obtain ⟨t0, ht0⟩ := hF
            have hle1 : ∑ t ∈ Finset.univ.filter (fun t : Fin T => (ω t).1.1 = c), V t ≤ 1 := by
              have : ∀ t : Fin T, V t = if (ω t).1.1 ∉ Finset.univ.image (fun s : Fin t => (ω (Fin.castLE t.2.le s)).1.1)
                  then 1 else 0 := by
                intro t; simp only [V]; rw [ite_not]
              simp_rw [this]
              rw [Finset.sum_boole]
              have hc : (Finset.filter (fun t : Fin T => (ω t).1.1 ∉ Finset.univ.image
                  (fun s : Fin t => (ω (Fin.castLE t.2.le s)).1.1))
                  (Finset.univ.filter (fun t : Fin T => (ω t).1.1 = c))).card ≤ 1 := by
                rw [Finset.card_le_one]
                intro a ha b hb
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
                rcases lt_trichotomy a b with hab | hab | hab
                · exfalso; apply hb.2; rw [hb.1, ← ha.1]; exact hpre_ne ω a b hab
                · exact hab
                · exfalso; apply ha.2; rw [ha.1, ← hb.1]; exact hpre_ne ω b a hab
              exact_mod_cast hc
            have hge1 : (1:ℝ) ≤ Finset.univ.sup' Finset.univ_nonempty
                (fun i => ∑ t ∈ Finset.univ.filter (fun t => (ω t).1.1 = c),
                  coinTable (fun t => (ω t).2) t i c) := by
              refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ
                (if (ω t0).2 c = true then (0 : Fin 2) else 1)))
              refine le_trans ?_ (Finset.single_le_sum (f := fun t => coinTable (fun t => (ω t).2) t
                (if (ω t0).2 c = true then (0 : Fin 2) else 1) c) ?_ ht0)
              · simp only [coinTable]
                by_cases hb : (ω t0).2 c = true <;> simp [hb]
              · intro t _; simp only [coinTable]; split_ifs <;> norm_num
            linarith
          · rw [Finset.not_nonempty_iff_eq_empty] at hF
            rw [hF, Finset.sum_empty]
            refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ (0 : Fin 2)))
            simp
        have hcard : ((Fintype.card (Fin T → Fin C → Bool) : ℕ) : ℝ) = ((2:ℝ)^C)^T := by
          simp
        have hP : ∀ ω : Fin T → (Fin C × Fin 2) × (Fin C → Bool),
            ((Fintype.card (Fin T → Fin C → Bool) : ℕ) : ℝ)⁻¹ *
              trajProb G (uniformDist C) A (coinTable (fun t => (ω t).2)) (fun t => (ω t).1)
            = ∏ t : Fin T, g t (fun s : Fin t => ω (Fin.castLE t.2.le s)) (ω t) := by
          intro ω
          rw [hcard, ← inv_pow]
          have : (((2:ℝ)^C)⁻¹)^T = ∏ _t : Fin T, ((2:ℝ)^C)⁻¹ := by simp
          rw [this, trajProb, ← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro t _
          simp only [g, uniformDist]
          have hh : hist G (coinTable (fun t => (ω t).2)) (fun t => (ω t).1) t
              = H t (fun s : Fin t => ω (Fin.castLE t.2.le s)) := by
            funext s
            simp only [hist, H]
            congr 2
          rw [hh]; ring
        obtain ⟨_, hlow⟩ := key _ g h m hg0 hg1 hm T
        have hmsum : (T:ℝ) / 2 - ε ≤ ∑ t : Fin T, m t := by
          have : ∀ t : Fin T, 1 / 2 - (T:ℝ) / C ≤ m t := by
            intro t
            simp only [m]
            have : (t:ℝ) ≤ T := by exact_mod_cast t.2.le
            have : (t:ℝ) / C ≤ T / C := div_le_div_of_nonneg_right this hCpos.le
            linarith
          calc (T:ℝ) / 2 - ε ≤ ∑ _t : Fin T, (1 / 2 - (T:ℝ) / C) := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                have : (T:ℝ) * (1 / 2 - T / C) = T / 2 - T^2 / C := by ring
                rw [this]; linarith
            _ ≤ _ := Finset.sum_le_sum (fun t _ => this t)
        have hR : coinExPostRegret T C G A = ∑ ω : Fin T → (Fin C × Fin 2) × (Fin C → Bool),
            ((Fintype.card (Fin T → Fin C → Bool) : ℕ) : ℝ)⁻¹ *
              (trajProb G (uniformDist C) A (coinTable (fun t => (ω t).2)) (fun t => (ω t).1) *
                ((∑ c, Finset.univ.sup' Finset.univ_nonempty
                  (fun i => ∑ t ∈ Finset.univ.filter (fun t => (ω t).1.1 = c),
                    coinTable (fun t => (ω t).2) t i c))
                - ∑ t, coinTable (fun t => (ω t).2) t (ω t).1.2 (ω t).1.1)) := by
          unfold coinExPostRegret exPostRegret expect
          rw [Finset.mul_sum]
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm, ← Fintype.sum_prod_type',
            ← (Equiv.arrowProdEquivProdArrow (Fin T) (fun _ => Fin C × Fin 2)
              (fun _ => Fin C → Bool)).sum_comp]
          rfl
        rw [hR]
        refine le_trans hmsum (le_trans hlow ?_)
        apply Finset.sum_le_sum
        intro ω _
        rw [← mul_assoc, hP ω]
        apply mul_le_mul_of_nonneg_left (hX ω)
        exact Finset.prod_nonneg (fun t _ => hg0 _ _ _)
