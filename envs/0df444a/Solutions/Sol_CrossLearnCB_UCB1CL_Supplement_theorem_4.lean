-- Prove2me | solution 1 for CrossLearnCB.UCB1CL.Supplement.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:10:12.209024+00:00
-- url     : https://prove2.me/submissions/7e3d53de-533d-4673-9bb7-be01c654da16

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_FixedContextProtocol

open CrossLearnCB
open CrossLearnCB.UCB1CL
open CrossLearnCB.UCB1CL.Supplement

open MeasureTheory

/-- Theorem 4, pp. 25–26. The asymptotic constant is absolute; the threshold may depend
on K,C. A single oblivious distribution over tables defeats every measurable policy.
The context sequence and law are chosen before the algorithm. -/
theorem solution : ∃ c : ℝ, 0 < c ∧
    ∀ (K C : ℕ) [NeZero K], 2 ≤ K → 0 < C → ∃ T₀ : ℕ, 0 < T₀ ∧
    ∀ T : ℕ, T₀ ≤ T → ∃ ctx : Fin T → Fin C,
    ∃ L : Measure (Fin T → Fin K → Fin C → ℝ),
      IsProbabilityMeasure L ∧
      (∀ᵐ r ∂L, ∀ t i d, r t i d ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ A : Policy K C, A.IsValid → A.IsMeasurable →
        c * Real.sqrt ((C : ℝ) * K * T) ≤
          ∫ r, fixedAdvRegret (fun _ _ _ => True) ctx A r ∂L := by
            have Hstep : ∀ (Z : Type) [Fintype Z] (p : (t:ℕ) → (Fin t → Z) → Z → ℝ) (n : ℕ)
                (F : (Fin (n+1) → Z) → ℝ),
                ∑ z : Fin (n+1) → Z, (∏ t : Fin (n+1), p t (fun s => z (Fin.castLE t.2.le s)) (z t)) * F z
                = ∑ z : Fin n → Z, (∏ t : Fin n, p t (fun s => z (Fin.castLE t.2.le s)) (z t)) *
                    ∑ y, p n z y * F (Fin.snoc z y) := by
              intro Z _ p n F
              rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => Z)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
              refine Finset.sum_congr rfl fun z _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun y _ => ?_
              have h1 : (Fin.snocEquiv (fun _ : Fin (n+1) => Z)) (y, z) = (Fin.snoc z y : Fin (n+1) → Z) := rfl
              rw [h1, Fin.prod_univ_castSucc, mul_assoc]
              congr 1
              · refine Finset.prod_congr rfl fun t _ => ?_
                congr 1
                · funext s
                  have : (Fin.castLE t.castSucc.2.le s : Fin (n+1)) = (Fin.castLE t.2.le s : Fin n).castSucc := rfl
                  rw [this]; exact Fin.snoc_castSucc (α := fun _ => Z) y z _
                · exact Fin.snoc_castSucc (α := fun _ => Z) y z _
              · congr 1
                congr 1
                · funext s
                  have : (Fin.castLE (Fin.last n).2.le s : Fin (n+1)) = (s : Fin n).castSucc := rfl
                  rw [this]; exact Fin.snoc_castSucc (α := fun _ => Z) y z _
                · exact Fin.snoc_last (α := fun _ => Z) y z
            have Hone : ∀ (Z : Type) [Fintype Z] (p : (t:ℕ) → (Fin t → Z) → Z → ℝ)
                (_ : ∀ t h, ∑ y, p t h y = 1) (n : ℕ),
                ∑ z : Fin n → Z, (∏ t : Fin n, p t (fun s => z (Fin.castLE t.2.le s)) (z t)) = 1 := by
              intro Z _ p hp n
              induction n with
              | zero => simp
              | succ n ih =>
                have := Hstep Z p n (fun _ => 1)
                simp only [mul_one, hp] at this
                rw [this, ih]
            have Hmart : ∀ (Z : Type) [Fintype Z] (p : (t:ℕ) → (Fin t → Z) → Z → ℝ)
                (_ : ∀ t h, ∑ y, p t h y = 1) (φ : ℕ → Z → ℝ) (_ : ∀ t h, ∑ y, p t h y * φ t y = 0) (n : ℕ),
                ∑ z : Fin n → Z, (∏ t : Fin n, p t (fun s => z (Fin.castLE t.2.le s)) (z t)) *
                  ∑ t : Fin n, φ t (z t) = 0 := by
              intro Z _ p hp φ hφ n
              induction n with
              | zero => simp
              | succ n ih =>
                rw [Hstep Z p n, ← ih]
                refine Finset.sum_congr rfl fun z _ => ?_
                congr 1
                have : ∀ y, p n z y * ∑ t : Fin (n+1), φ t ((Fin.snoc z y : Fin (n+1) → Z) t)
                    = p n z y * (∑ t : Fin n, φ t (z t)) + p n z y * φ n y := by
                  intro y
                  rw [Fin.sum_univ_castSucc, ← mul_add]
                  congr 2
                  · refine Finset.sum_congr rfl fun t _ => ?_
                    congr 1
                    exact Fin.snoc_castSucc (α := fun _ => Z) y z _
                  · congr 1
                    exact Fin.snoc_last (α := fun _ => Z) y z
                rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_add_distrib, hφ, ← Finset.sum_mul, hp]
                simp
            have Hchange : ∀ (Ω : Type) [Fintype Ω] (P0 L f : Ω → ℝ) (m D : ℝ) (_ : ∀ z, 0 ≤ P0 z)
                (_ : ∀ z, 0 < L z) (_ : ∑ z, P0 z = 1) (_ : ∑ z, P0 z * L z = 1)
                (_ : ∑ z, P0 z * Real.log (L z) = -D) (_ : ∀ z, 0 ≤ f z) (_ : ∀ z, f z ≤ m) (_ : 0 ≤ D) (_ : 0 ≤ m),
                ∑ z, P0 z * L z * f z ≤ ∑ z, P0 z * f z + m * (1/8 + 8 * D) := by
              intro Ω _ P0 L f m D h0 hL h1 h2 h3 hf0 hfm hD hm
              have key : ∀ x : ℝ, 0 < x → |x - 1| ≤ (8+1/32) * (x+1) - (16-1/16) * (1 + 1/2 * Real.log x) := by
                intro x hx
                obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ x = s^2 := ⟨√x, Real.sqrt_pos.2 hx, (Real.sq_sqrt hx.le).symm⟩
                have hl : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs
                have hl2 : Real.log (s^2) = 2 * Real.log s := by rw [Real.log_pow]; norm_num
                rw [hl2, abs_le]
                constructor <;> nlinarith [sq_nonneg (8*(s-1) - (s+1)/4), sq_nonneg (8*(s-1) + (s+1)/4), sq_nonneg (s-1), sq_nonneg (s+1), sq_nonneg (16*(s-1) - (s+1)), sq_nonneg (16*(s-1) + (s+1))]
              have : ∑ z, P0 z * L z * f z - ∑ z, P0 z * f z ≤ ∑ z, P0 z * (m * ((8+1/32) * (L z+1) - (16-1/16) * (1 + 1/2 * Real.log (L z)))) := by
                rw [← Finset.sum_sub_distrib]
                refine Finset.sum_le_sum fun z _ => ?_
                have e : P0 z * L z * f z - P0 z * f z = P0 z * ((L z - 1) * f z) := by ring
                rw [e]
                refine mul_le_mul_of_nonneg_left ?_ (h0 z)
                calc (L z - 1) * f z ≤ |L z - 1| * f z := mul_le_mul_of_nonneg_right (le_abs_self _) (hf0 z)
                  _ ≤ |L z - 1| * m := mul_le_mul_of_nonneg_left (hfm z) (abs_nonneg _)
                  _ = m * |L z - 1| := mul_comm _ _
                  _ ≤ _ := mul_le_mul_of_nonneg_left (key _ (hL z)) hm
              have e : ∑ z, P0 z * (m * ((8+1/32) * (L z+1) - (16-1/16) * (1 + 1/2 * Real.log (L z))))
                  = m * ((8+1/32) * (∑ z, P0 z * L z) + (8+1/32) * (∑ z, P0 z) - (16-1/16) * (∑ z, P0 z) - (16-1/16)/2 * ∑ z, P0 z * Real.log (L z)) := by
                simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun z _ => ?_
                ring
              rw [e, h1, h2, h3] at this
              nlinarith [mul_nonneg hm hD]
            have Hmarg : ∀ (ι U X : Type) [Fintype ι] [DecidableEq ι] [Fintype U] [Fintype X] [DecidableEq X] (w : U → ℝ) (g : ι → U → X)
                (F : (ι → X) → ℝ),
                ∑ u : ι → U, (∏ t, w (u t)) * F (fun t => g t (u t))
                = ∑ x : ι → X, (∏ t, ∑ v, if g t v = x t then w v else 0) * F x := by
              intro ι U X _ _ _ _ _ w g F
              have h1 : ∀ x : ι → X, (∏ t, ∑ v, if g t v = x t then w v else 0)
                  = ∑ u : ι → U, if (fun t => g t (u t)) = x then ∏ t, w (u t) else 0 := by
                intro x
                rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
                refine Finset.sum_congr rfl fun u _ => ?_
                split_ifs with h
                · refine Finset.prod_congr rfl fun t _ => ?_
                  rw [if_pos (congrFun h t)]
                · obtain ⟨t, ht⟩ := Function.ne_iff.1 h
                  exact Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)
              simp only [h1, Finset.sum_mul]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun u _ => ?_
              simp [ite_mul]
            have Hsymm : ∀ (C K : ℕ) (c : Fin C) (G : (Fin C → Fin K) → ℝ),
                ∑ j : Fin C → Fin K, ∑ i : Fin K, G (Function.update j c i) = K * ∑ j, G j := by
              intro C K c G
              let σ : (Fin C → Fin K) × Fin K → (Fin C → Fin K) × Fin K := fun q => (Function.update q.1 c q.2, q.1 c)
              have hσ : Function.Involutive σ := by
                rintro ⟨j, i⟩
                simp [σ]
              have := Equiv.sum_comp hσ.toPerm (fun q : (Fin C → Fin K) × Fin K => G q.1)
              rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at this
              simp only [Function.Involutive.coe_toPerm, σ] at this
              rw [this]
              simp [Finset.mul_sum]
            have Hbandit : ∀ (K C T : ℕ) [NeZero K] (_ : 2 ≤ K) (ctx : ℕ → Fin C) (M ε : ℝ)
                (_ : ∀ c : Fin C, (∑ t : Fin T, if ctx t = c then (1:ℝ) else 0) ≤ M) (_ : 0 ≤ ε) (_ : 4 * ε^2 ≤ 1/2)
                (_ : 32 * ε^2 * M ≤ K / 8) (α : (t:ℕ) → (Fin t → Fin K × Bool) → Fin K → ℝ)
                (_ : ∀ t h a, 0 ≤ α t h a) (_ : ∀ t h, ∑ a, α t h a = 1),
                ∑ j : Fin C → Fin K, ∑ z : Fin T → Fin K × Bool,
                  (∏ t : Fin T, (α t (fun s => z (Fin.castLE t.2.le s)) (z t).1 *
                    (1/2 + (if (z t).2 then (1:ℝ) else -1) * (if j (ctx t) = (z t).1 then ε else 0)))) *
                    ∑ t : Fin T, (if (z t).2 then (1:ℝ) else 0)
                  ≤ (K:ℝ)^C * (T / 2 + ε * (3/4 * T)) := by
              intro K C T _ hK ctx M ε hM hε hε2 hεM α hα0 hα1
              have hεlt : 2 * ε < 1 := by nlinarith
              have hK' : (2:ℝ) ≤ K := by exact_mod_cast hK
              obtain ⟨p, hp⟩ : ∃ p : (Fin C → Option (Fin K)) → (t:ℕ) → (Fin t → Fin K × Bool) → Fin K × Bool → ℝ,
                ∀ θ t h y, p θ t h y = α t h y.1 * (1/2 + (if y.2 then (1:ℝ) else -1) * (if θ (ctx t) = some y.1 then ε else 0)) :=
                  ⟨_, fun _ _ _ _ => rfl⟩
              have hp1 : ∀ θ t h, ∑ y, p θ t h y = 1 := by
                intro θ t h
                rw [Fintype.sum_prod_type, ← hα1 t h]
                refine Finset.sum_congr rfl fun a _ => ?_
                rw [Fintype.sum_bool, hp, hp]
                simp only [if_true, Bool.false_eq_true, if_false]
                ring
              have hp0 : ∀ θ t h y, 0 ≤ p θ t h y := by
                intro θ t h y
                rw [hp]
                refine mul_nonneg (hα0 _ _ _) ?_
                split_ifs <;> linarith
              obtain ⟨P, hP⟩ : ∃ P : (Fin C → Option (Fin K)) → (Fin T → Fin K × Bool) → ℝ,
                ∀ θ z, P θ z = ∏ t : Fin T, p θ t (fun s => z (Fin.castLE t.2.le s)) (z t) := ⟨_, fun _ _ => rfl⟩
              have hP0 : ∀ θ z, 0 ≤ P θ z := fun θ z => by
                rw [hP]; exact Finset.prod_nonneg fun t _ => hp0 _ _ _ _
              have hP1 : ∀ θ, ∑ z, P θ z = 1 := fun θ => by
                simp only [hP]; exact Hone _ _ (hp1 θ) T
              obtain ⟨N, hN⟩ : ∃ N : Fin C → Fin K → (Fin T → Fin K × Bool) → ℝ,
                ∀ c i z, N c i z = ∑ t : Fin T, if ctx t = c ∧ (z t).1 = i then (1:ℝ) else 0 := ⟨_, fun _ _ _ => rfl⟩
              obtain ⟨m, hm⟩ : ∃ m : Fin C → ℝ, ∀ c, m c = ∑ t : Fin T, if ctx t = c then (1:ℝ) else 0 := ⟨_, fun _ => rfl⟩
              have hm0 : ∀ c, 0 ≤ m c := fun c => by
                rw [hm]; exact Finset.sum_nonneg fun t _ => by split_ifs <;> norm_num
              have hN0 : ∀ c i z, 0 ≤ N c i z := fun c i z => by
                rw [hN]; exact Finset.sum_nonneg fun t _ => by split_ifs <;> norm_num
              have hNm : ∀ c i z, N c i z ≤ m c := fun c i z => by
                rw [hN, hm]
                refine Finset.sum_le_sum fun t _ => ?_
                by_cases h1 : ctx t = c <;> by_cases h2 : (z t).1 = i <;> simp [h1, h2]
              have hNsum : ∀ c z, ∑ i, N c i z = m c := fun c z => by
                simp only [hN, hm]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun t _ => ?_
                by_cases h1 : ctx t = c <;> simp [h1]
              have hmT : ∑ c, m c = T := by
                simp only [hm]
                rw [Finset.sum_comm]
                simp
              -- reward
              have hrew : ∀ j : Fin C → Fin K, ∑ z, P (fun c => some (j c)) z * ∑ t : Fin T, (if (z t).2 then (1:ℝ) else 0)
                  = T / 2 + ε * ∑ c, ∑ z, P (fun c => some (j c)) z * N c (j c) z := by
                intro j
                have h := Hmart _ (p (fun c => some (j c))) (hp1 _)
                  (fun t y => (if y.2 then (1:ℝ) else 0) - 1/2 - (if j (ctx t) = y.1 then ε else 0)) (by
                    intro t h
                    rw [Fintype.sum_prod_type]
                    refine Finset.sum_eq_zero fun a _ => ?_
                    rw [Fintype.sum_bool, hp, hp]
                    simp only [if_true, Bool.false_eq_true, if_false, Option.some.injEq]
                    split_ifs <;> ring) T
                simp only [← hP] at h
                have h2 : ∀ z : Fin T → Fin K × Bool, ∑ t : Fin T, ((if (z t).2 then (1:ℝ) else 0) - 1/2 - (if j (ctx t) = (z t).1 then ε else 0))
                    = ∑ t : Fin T, (if (z t).2 then (1:ℝ) else 0) - T/2 - ε * ∑ c, N c (j c) z := by
                  intro z
                  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
                  congr 1
                  · congr 1
                    simp; ring
                  · simp only [hN]
                    rw [Finset.sum_comm, Finset.mul_sum]
                    refine Finset.sum_congr rfl fun t _ => ?_
                    have : ∀ c, (if ctx t = c ∧ (z t).1 = j c then (1:ℝ) else 0) = if ctx t = c then (if (z t).1 = j c then (1:ℝ) else 0) else 0 := by
                      intro c; by_cases h1 : ctx t = c <;> simp [h1]
                    simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true, eq_comm (a := j (ctx t))]
                    split_ifs <;> simp
                simp only [h2, mul_sub, Finset.sum_sub_distrib] at h
                rw [← Finset.sum_mul, hP1] at h
                have h3 : ∑ c, ∑ z, P (fun c => some (j c)) z * N c (j c) z = ∑ z, P (fun c => some (j c)) z * ∑ c, N c (j c) z := by
                  rw [Finset.sum_comm]
                  simp only [Finset.mul_sum]
                rw [h3]
                have h4 : ∑ z, P (fun c => some (j c)) z * (ε * ∑ c, N c (j c) z) = ε * ∑ z, P (fun c => some (j c)) z * ∑ c, N c (j c) z := by
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl fun z _ => by ring
                linarith
              -- change of measure
              have hcom : ∀ (j : Fin C → Fin K) (c : Fin C),
                  ∑ z, P (fun c => some (j c)) z * N c (j c) z ≤
                  (1 + 32 * ε^2 * M) * (∑ z, P (Function.update (fun c => some (j c)) c none) z * N c (j c) z) + m c / 8 := by
                intro j c
                obtain ⟨θ0, hθ0⟩ : ∃ θ0, θ0 = Function.update (fun c => some (j c)) c (none : Option (Fin K)) := ⟨_, rfl⟩
                rw [← hθ0]
                obtain ⟨l, hl⟩ : ∃ l : ℕ → Fin K × Bool → ℝ, ∀ t y, l t y = if ctx t = c ∧ y.1 = j c then 1 + (if y.2 then (1:ℝ) else -1) * (2 * ε) else 1 := ⟨_, fun _ _ => rfl⟩
                have hl0 : ∀ t y, 0 < l t y := by
                  intro t y; rw [hl]; split_ifs <;> linarith
                have hPl : ∀ z, P (fun c => some (j c)) z = P θ0 z * ∏ t : Fin T, l t (z t) := by
                  intro z
                  rw [hP, hP, ← Finset.prod_mul_distrib]
                  refine Finset.prod_congr rfl fun t _ => ?_
                  rw [hp, hp, hl, mul_assoc]
                  congr 1
                  by_cases h1 : ctx t = c
                  · by_cases h2 : (z t).1 = j c
                    · simp only [h1, h2, hθ0, Function.update_self, and_self, if_true, reduceCtorEq, if_false]
                      ring
                    · have h2' : ¬ j c = (z t).1 := fun h => h2 h.symm
                      simp only [h1, h2, h2', hθ0, Function.update_self, and_false, reduceCtorEq, if_false, Option.some.injEq]
                      ring
                  · simp only [h1, hθ0, Function.update_of_ne h1, false_and, if_false, mul_one]
                obtain ⟨κ, hκ⟩ : ∃ κ, κ = -(1/2 * (Real.log (1 + 2 * ε) + Real.log (1 - 2 * ε))) := ⟨_, rfl⟩
                have hκle : κ ≤ 4 * ε^2 := by
                  have h1 : Real.log (1 + 2 * ε) + Real.log (1 - 2 * ε) = Real.log (1 - 4 * ε^2) := by
                    rw [← Real.log_mul (by linarith) (by linarith)]; congr 1; ring
                  have h2 := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 1 - 4 * ε^2 by linarith)
                  have h3 : (1 - 4 * ε^2)⁻¹ ≤ 1 + 8 * ε^2 := by
                    rw [inv_le_iff_one_le_mul₀ (by linarith)]
                    nlinarith [sq_nonneg ε]
                  rw [hκ, h1]; linarith
                have hκ0 : 0 ≤ κ := by
                  have h1 : Real.log (1 + 2 * ε) ≤ 2 * ε := by
                    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 2 * ε by linarith); linarith
                  have h2 : Real.log (1 - 2 * ε) ≤ - (2 * ε) := by
                    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 - 2 * ε by linarith); linarith
                  rw [hκ]; linarith
                have hlog : ∑ z, P θ0 z * Real.log (∏ t : Fin T, l t (z t)) = - (κ * ∑ z, P θ0 z * N c (j c) z) := by
                  have h := Hmart _ (p θ0) (hp1 _)
                    (fun t y => Real.log (l t y) + κ * (if ctx t = c ∧ y.1 = j c then (1:ℝ) else 0)) (by
                      intro t h
                      rw [Fintype.sum_prod_type]
                      refine Finset.sum_eq_zero fun a _ => ?_
                      rw [Fintype.sum_bool, hp, hp, hl, hl]
                      by_cases h1 : ctx t = c
                      · by_cases h2 : a = j c
                        · simp only [h1, h2, hθ0, Function.update_self, and_self, if_true, reduceCtorEq, if_false, Bool.false_eq_true]
                          rw [hκ, show (1 + 1 * (2 * ε)) = 1 + 2 * ε by ring, show (1 + -1 * (2 * ε)) = 1 - 2 * ε by ring]
                          ring
                        · simp [h1, h2]
                      · simp [h1]) T
                  simp only [← hP] at h
                  have h2 : ∀ z : Fin T → Fin K × Bool, ∑ t : Fin T, (Real.log (l t (z t)) + κ * (if ctx t = c ∧ (z t).1 = j c then (1:ℝ) else 0))
                    = Real.log (∏ t : Fin T, l t (z t)) + κ * N c (j c) z := by
                    intro z
                    rw [Finset.sum_add_distrib, Real.log_prod (fun t _ => (hl0 _ _).ne'), hN, Finset.mul_sum]
                  simp only [h2, mul_add, Finset.sum_add_distrib] at h
                  have h4 : ∑ z, P θ0 z * (κ * N c (j c) z) = κ * ∑ z, P θ0 z * N c (j c) z := by
                    rw [Finset.mul_sum]
                    exact Finset.sum_congr rfl fun z _ => by ring
                  linarith
                have hE0 : 0 ≤ ∑ z, P θ0 z * N c (j c) z := Finset.sum_nonneg fun z _ => mul_nonneg (hP0 _ _) (hN0 _ _ _)
                have h := Hchange _ (P θ0) (fun z => ∏ t : Fin T, l t (z t)) (N c (j c)) (m c) (κ * ∑ z, P θ0 z * N c (j c) z)
                  (hP0 _) (fun z => Finset.prod_pos fun t _ => hl0 _ _) (hP1 _)
                  (by simp only [← hPl]; exact hP1 _) hlog (hN0 _ _) (hNm _ _) (mul_nonneg hκ0 hE0) (hm0 _)
                simp only [← hPl] at h
                have h5 : m c * κ ≤ M * (4 * ε^2) := mul_le_mul (by rw [hm]; exact hM c) hκle hκ0 (le_trans (hm0 c) (by rw [hm]; exact hM c))
                nlinarith [mul_le_mul_of_nonneg_right h5 hE0]
              -- averaging
              have havg : ∀ c : Fin C, ∑ j : Fin C → Fin K, ∑ z, P (fun c => some (j c)) z * N c (j c) z ≤ (K:ℝ)^C * (3/4 * m c) := by
                intro c
                have h1 := Hsymm C K c (fun j => ∑ z, P (Function.update (fun c => some (j c)) c none) z * N c (j c) z)
                have h2 : ∀ (j : Fin C → Fin K) (i : Fin K), Function.update (fun c' => some (Function.update j c i c')) c (none : Option (Fin K))
                    = Function.update (fun c' => some (j c')) c none := by
                  intro j i
                  funext c'
                  by_cases h : c' = c
                  · subst h; simp
                  · simp [Function.update_of_ne h]
                have h3 : ∀ j : Fin C → Fin K, ∑ i : Fin K, ∑ z, P (Function.update (fun c' => some (Function.update j c i c')) c none) z * N c (Function.update j c i c) z = m c := by
                  intro j
                  simp only [h2, Function.update_self]
                  rw [Finset.sum_comm]
                  simp only [← Finset.mul_sum, hNsum]
                  rw [← Finset.sum_mul, hP1, one_mul]
                simp only [h3] at h1
                have h4 : ∑ j : Fin C → Fin K, m c = (K:ℝ)^C * m c := by simp
                rw [h4] at h1
                have h5 := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hcom j c)
                rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h5
                have h6 : ∑ j : Fin C → Fin K, m c / 8 = (K:ℝ)^C * m c / 8 := by simp; ring
                rw [h6] at h5
                refine h5.trans ?_
                obtain ⟨S, hS⟩ : ∃ S, S = ∑ j : Fin C → Fin K, ∑ z, P (Function.update (fun c => some (j c)) c none) z * N c (j c) z := ⟨_, rfl⟩
                rw [← hS] at h1 ⊢
                have hS0 : 0 ≤ S := by
                  rw [hS]
                  exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun z _ => mul_nonneg (hP0 _ _) (hN0 _ _ _)
                nlinarith [mul_le_mul_of_nonneg_right hεM hS0, mul_le_mul_of_nonneg_right hK' hS0]
              have hfin : ∀ j : Fin C → Fin K, ∑ z : Fin T → Fin K × Bool,
                  (∏ t : Fin T, (α t (fun s => z (Fin.castLE t.2.le s)) (z t).1 *
                    (1/2 + (if (z t).2 then (1:ℝ) else -1) * (if j (ctx t) = (z t).1 then ε else 0)))) *
                    ∑ t : Fin T, (if (z t).2 then (1:ℝ) else 0)
                  = T / 2 + ε * ∑ c, ∑ z, P (fun c => some (j c)) z * N c (j c) z := by
                intro j
                rw [← hrew j]
                refine Finset.sum_congr rfl fun z _ => ?_
                rw [hP]
                simp only [hp, Option.some.injEq]
              simp only [hfin]
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
              have h7 : ∑ j : Fin C → Fin K, (T:ℝ) / 2 = (K:ℝ)^C * (T / 2) := by simp
              have h8 := Finset.sum_le_sum (s := Finset.univ) (fun c _ => havg c)
              rw [← Finset.mul_sum, ← Finset.mul_sum, hmT] at h8
              rw [h7]
              nlinarith [mul_le_mul_of_nonneg_left h8 hε]
            have Hreward : ∀ (K C T : ℕ) (ctx : ℕ → Fin C) (ε : ℝ) (w : Fin 3 → ℝ) (_ : w = ![1/2, ε, 1/2-ε]) (A : Policy K C) (j : Fin C → Fin K),
                ∑ u : Fin T → Fin 3, (∏ t, w (u t)) *
                  fixedAlgReward (fun _ _ _ => True) (fun t : Fin T => ctx t) A
                    (fun t i d => if d = ctx t then (if decide (u t = 0 ∨ u t = 1 ∧ j (ctx t) = i) then (1:ℝ) else 0) else 0)
                = ∑ z : Fin T → Fin K × Bool,
                  (∏ t : Fin T, (A t (fun s : Fin t => (ctx s, (z (Fin.castLE t.2.le s)).1, fun d => if d = ctx s then (if (z (Fin.castLE t.2.le s)).2 then (1:ℝ) else 0) else 0)) (ctx t) (z t).1 *
                    (1/2 + (if (z t).2 then (1:ℝ) else -1) * (if j (ctx t) = (z t).1 then ε else 0)))) *
                    ∑ t : Fin T, (if (z t).2 then (1:ℝ) else 0) := by
              intro K C T ctx ε w hw A j
              let e : (Fin T → Fin K) × (Fin T → Bool) ≃ (Fin T → Fin K × Bool) :=
                ⟨fun q t => (q.1 t, q.2 t), fun z => (fun t => (z t).1, fun t => (z t).2), fun _ => rfl, fun _ => rfl⟩
              rw [← e.sum_comp, Fintype.sum_prod_type]
              simp only [fixedAlgReward, Finset.mul_sum (s := (Finset.univ : Finset (Fin T → Fin K)))]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun a _ => ?_
              have hM := Hmarg (Fin T) (Fin 3) Bool w (fun t v => decide (v = 0 ∨ v = 1 ∧ j (ctx t) = a t))
                (fun x => (∏ t : Fin T, A t (fun s : Fin t => (ctx s, a (Fin.castLE t.2.le s), fun d => if d = ctx s then (if x (Fin.castLE t.2.le s) then (1:ℝ) else 0) else 0)) (ctx t) (a t)) * ∑ t : Fin T, (if x t then (1:ℝ) else 0))
              refine Eq.trans ?_ (hM.trans ?_)
              · refine Finset.sum_congr rfl fun u _ => ?_
                congr 1
                congr 1
                · refine Finset.prod_congr rfl fun t _ => ?_
                  congr 1
                  funext s
                  refine Prod.ext rfl (Prod.ext rfl ?_)
                  funext d
                  simp only [hist, feedback, if_true]
                  rfl
              · refine Finset.sum_congr rfl fun x _ => ?_
                rw [← mul_assoc, ← Finset.prod_mul_distrib]
                refine congrArg₂ (· * ·) ?_ rfl
                refine Finset.prod_congr rfl fun t _ => ?_
                rw [mul_comm]
                congr 1
                simp only [e, Equiv.coe_fn_mk, Fin.sum_univ_three, hw]
                rcases Bool.eq_false_or_eq_true (x t) with h | h <;> by_cases h1 : j (ctx t) = a t <;>
                  simp [h, h1] <;> ring
            have Hbench : ∀ (K C T : ℕ) [NeZero K] (ctx : ℕ → Fin C) (ε : ℝ) (w : Fin 3 → ℝ) (_ : w = ![1/2, ε, 1/2-ε]) (_ : ∀ v, 0 ≤ w v) (j : Fin C → Fin K),
                (T:ℝ) * (1/2 + ε) ≤ ∑ u : Fin T → Fin 3, (∏ t, w (u t)) *
                  (∑ c, Finset.univ.sup' Finset.univ_nonempty
                (fun i => ∑ t ∈ Finset.univ.filter (fun t : Fin T => ctx t = c), 
                    (if c = ctx t then (if decide (u t = 0 ∨ u t = 1 ∧ j (ctx t) = i) then (1:ℝ) else 0) else 0))) := by
              intro K C T _ ctx ε w hw hw0 j
              have hw1 : ∑ v, w v = 1 := by
                simp [hw, Fin.sum_univ_three]; norm_num
              have h := Hmart (Fin 3) (fun _ _ => w) (fun _ _ => hw1) (fun _ v => (if v = 0 ∨ v = 1 then (1:ℝ) else 0) - (1/2+ε))
                (fun _ _ => by simp [hw, Fin.sum_univ_three]; ring) T
              have h1 := Hone (Fin 3) (fun _ _ => w) (fun _ _ => hw1) T
              simp only [Finset.sum_sub_distrib, mul_sub] at h
              rw [← Finset.sum_mul, h1] at h
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_mul] at h
              have h2 : (T:ℝ) * (1/2+ε) = ∑ u : Fin T → Fin 3, (∏ t, w (u t)) * ∑ t, (if u t = 0 ∨ u t = 1 then (1:ℝ) else 0) := by linarith
              rw [h2]
              refine Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun t _ => hw0 _)
              rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun t : Fin T => ctx t)]
              refine Finset.sum_le_sum fun c _ => ?_
              refine le_trans (le_of_eq ?_) (Finset.le_sup' _ (Finset.mem_univ (j c)))
              refine Finset.sum_congr rfl fun t ht => ?_
              have : ctx t = c := (Finset.mem_filter.1 ht).2
              simp [this]
            refine ⟨1/128, by norm_num, fun K C _ hK hC => ⟨K * C, Nat.mul_pos (by omega) hC, fun T hT => ?_⟩⟩
            have hKC : 0 < K * C := Nat.mul_pos (by omega) hC
            have hTR : (K:ℝ) * C ≤ T := by exact_mod_cast hT
            have hT0 : (0:ℝ) < T := by exact_mod_cast (lt_of_lt_of_le hKC hT)
            have hC0 : (0:ℝ) < C := by exact_mod_cast hC
            have hK0 : (2:ℝ) ≤ K := by exact_mod_cast hK
            obtain ⟨ctx, hctx⟩ : ∃ ctx : ℕ → Fin C, ∀ t, ctx t = ⟨t % C, Nat.mod_lt _ hC⟩ := ⟨_, fun _ => rfl⟩
            obtain ⟨ε, hεd⟩ : ∃ ε, ε = Real.sqrt ((C : ℝ) * K * T) / (32 * T) := ⟨_, rfl⟩
            have hε0 : 0 ≤ ε := by rw [hεd]; positivity
            have hεsq : ε^2 = C * K / (1024 * T) := by
              rw [hεd, div_pow, Real.sq_sqrt (by positivity)]
              field_simp
              norm_num
            have hε2 : 4 * ε^2 ≤ 1/2 := by
              rw [hεsq, mul_div_assoc', div_le_iff₀ (by positivity)]
              nlinarith
            have hεhalf : ε ≤ 1/2 := by nlinarith
            have hM : ∀ c : Fin C, (∑ t : Fin T, if ctx t = c then (1:ℝ) else 0) ≤ 2 * T / C := by
              intro c
              have h1 : (∑ t : Fin T, if ctx t = c then (1:ℝ) else 0) = ((Finset.univ.filter (fun t : Fin T => ctx t = c)).card : ℝ) := by
                simp
              have h2 : (Finset.univ.filter (fun t : Fin T => ctx t = c)).card ≤ (Finset.range (T / C + 1)).card := by
                refine Finset.card_le_card_of_injOn (fun t => t.1 / C) ?_ ?_
                · intro t _
                  simp only [Finset.coe_range, Set.mem_Iio]
                  exact Nat.lt_succ_of_le (Nat.div_le_div_right t.2.le)
                · intro t ht t' ht' htt
                  have e1 : ctx t = c := by simpa using ht
                  have e2 : ctx t' = c := by simpa using ht'
                  rw [hctx] at e1 e2
                  have e3 : t.1 % C = t'.1 % C := by
                    have := congrArg Fin.val (e1.trans e2.symm); simpa using this
                  have e4 : t.1 / C = t'.1 / C := htt
                  apply Fin.ext
                  rw [← Nat.div_add_mod t.1 C, ← Nat.div_add_mod t'.1 C, e3, e4]
              rw [Finset.card_range] at h2
              rw [h1]
              have h3 : ((Finset.univ.filter (fun t : Fin T => ctx t = c)).card : ℝ) ≤ ((T / C : ℕ) : ℝ) + 1 := by exact_mod_cast h2
              have h4 : ((T / C : ℕ) : ℝ) ≤ T / C := Nat.cast_div_le
              have h5 : (1:ℝ) ≤ T / C := by
                rw [le_div_iff₀ hC0]; nlinarith
              have h6 : 2 * (T:ℝ) / C = T / C + T / C := by ring
              linarith
            have hεM : 32 * ε^2 * (2 * T / C) ≤ K / 8 := by
              rw [hεsq]
              have : 32 * ((C:ℝ) * K / (1024 * T)) * (2 * T / C) = K / 16 := by
                field_simp
                norm_num
              rw [this]; linarith
            obtain ⟨w, hw⟩ : ∃ w : Fin 3 → ℝ, w = ![1/2, ε, 1/2-ε] := ⟨_, rfl⟩
            have hw0 : ∀ v, 0 ≤ w v := by
              intro v
              rw [hw]
              fin_cases v <;> simp <;> linarith
            have hw1 : ∑ v, w v = 1 := by
              simp [hw, Fin.sum_univ_three]; norm_num
            obtain ⟨tb, htb⟩ : ∃ tb : (Fin C → Fin K) × (Fin T → Fin 3) → Fin T → Fin K → Fin C → ℝ, ∀ q, tb q =
                fun (t : Fin T) i d => if d = ctx t then (if decide (q.2 t = 0 ∨ q.2 t = 1 ∧ q.1 (ctx t) = i) then (1:ℝ) else 0) else 0 := ⟨_, fun _ => rfl⟩
            obtain ⟨W, hW⟩ : ∃ W : (Fin C → Fin K) × (Fin T → Fin 3) → ℝ, ∀ q, W q = ((K:ℝ)^C)⁻¹ * ∏ t : Fin T, w (q.2 t) := ⟨_, fun _ => rfl⟩
            have hW0 : ∀ q, 0 ≤ W q := fun q => by
              rw [hW]; exact mul_nonneg (by positivity) (Finset.prod_nonneg fun t _ => hw0 _)
            have hW1 : ∑ q, W q = 1 := by
              rw [Fintype.sum_prod_type]
              simp only [hW, ← Finset.mul_sum]
              rw [Hone (Fin 3) (fun _ _ => w) (fun _ _ => hw1) T]
              simp
            refine ⟨fun t => ctx t, ∑ q, ENNReal.ofReal (W q) • Measure.dirac (tb q), ⟨?_⟩, ?_, ?_⟩
            · simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
              rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => hW0 q), hW1, ENNReal.ofReal_one]
            · rw [ae_iff, Measure.coe_finsetSum, Finset.sum_apply]
              refine Finset.sum_eq_zero fun q _ => ?_
              rw [← ae_iff]
              refine Measure.ae_smul_measure ?_ _
              rw [ae_dirac_eq]
              simp only [Filter.eventually_pure, htb]
              intro t i d
              split_ifs <;> simp
            · intro A hA _
              rw [integral_finsetSum_measure (fun q _ => (integrable_dirac (by simp)).smul_measure (by simp))]
              simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hW0 _), smul_eq_mul]
              have hB := Hbandit K C T hK ctx (2 * T / C) ε hM hε0 hε2 hεM
                (fun t h a => A t (fun s : Fin t => (ctx s, (h s).1, fun d => if d = ctx s then (if (h s).2 then (1:ℝ) else 0) else 0)) (ctx t) a)
                (fun t h a => hA.1 _ _ _ _) (fun t h => hA.2 _ _ _)
              have hR : ∀ j : Fin C → Fin K, (T:ℝ) * (1/2 + ε) - (∑ u : Fin T → Fin 3, (∏ t, w (u t)) * fixedAlgReward (fun _ _ _ => True) (fun t : Fin T => ctx t) A (tb (j, u)))
                  ≤ ∑ u : Fin T → Fin 3, (∏ t, w (u t)) * fixedAdvRegret (fun _ _ _ => True) (fun t : Fin T => ctx t) A (tb (j, u)) := by
                intro j
                have := Hbench K C T ctx ε w hw hw0 j
                simp only [fixedAdvRegret, mul_sub, Finset.sum_sub_distrib]
                refine sub_le_sub_right (this.trans (le_of_eq ?_)) _
                refine Finset.sum_congr rfl fun u _ => ?_
                congr 1
                refine Finset.sum_congr rfl fun c _ => ?_
                simp only [htb]
              have hR2 := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hR j)
              simp only [htb, Hreward K C T ctx ε w hw A] at hR2
              rw [Finset.sum_sub_distrib] at hR2
              have hc : ∑ j : Fin C → Fin K, (T:ℝ) * (1/2 + ε) = (K:ℝ)^C * (T * (1/2+ε)) := by simp
              rw [hc] at hR2
              have hR3 : (K:ℝ)^C * (ε * T / 4) ≤ ∑ j : Fin C → Fin K, ∑ u : Fin T → Fin 3, (∏ t, w (u t)) * fixedAdvRegret (fun _ _ _ => True) (fun t : Fin T => ctx t) A (tb (j, u)) := by
                simp only [htb]
                refine le_trans ?_ hR2
                refine le_trans ?_ (sub_le_sub_left hB _)
                apply le_of_eq
                ring
              rw [Fintype.sum_prod_type]
              simp only [hW, mul_assoc, ← Finset.mul_sum]
              have hKp : (0:ℝ) < (K:ℝ)^C := by positivity
              have hval : 1/128 * Real.sqrt ((C : ℝ) * K * T) = ε * T / 4 := by
                rw [hεd]; field_simp; norm_num
              rw [← mul_assoc (C:ℝ), hval, inv_mul_eq_div, le_div_iff₀ hKp, mul_comm]
              exact hR3
