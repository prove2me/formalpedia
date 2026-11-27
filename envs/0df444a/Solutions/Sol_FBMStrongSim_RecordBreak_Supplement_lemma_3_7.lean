-- Prove2me | solution 1 for FBMStrongSim.RecordBreak.Supplement.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:19:22.415666+00:00
-- url     : https://prove2.me/submissions/01411224-3253-4993-9fea-f7c6c95f4d51

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_HolderModel

open FBMStrongSim
open FBMStrongSim.RecordBreak
open FBMStrongSim.RecordBreak.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Lemma 3.7 (p.13), deterministic extension to 0<α≤1. -/
theorem solution (x : ℝ → ℝ) (k : ℕ) (hk : 1 ≤ k) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    HolderBound alpha ((2 : ℝ) ^ (alpha * ((k : ℝ) - 1) + 2) * maxDisp x k)
      (fun t => interp x k t - interp x (k - 1) t) := by
        have key : ∀ (n m : ℕ) (t : ℝ), m < 2 ^ n → (m : ℝ) / 2 ^ n ≤ t → t ≤ ((m : ℝ) + 1) / 2 ^ n →
            interp x n t = x (dyadic n m) + ((2 : ℝ) ^ n * t - m) * (x (dyadic n (m + 1)) - x (dyadic n m)) := by
          intro n m t hm h1 h2
          have hpos : (0 : ℝ) < 2 ^ n := by positivity
          have e1 : (m : ℝ) ≤ 2 ^ n * t := by rw [div_le_iff₀ hpos] at h1; linarith
          have e2 : 2 ^ n * t ≤ (m : ℝ) + 1 := by rw [le_div_iff₀ hpos] at h2; linarith
          have hnn : (0:ℝ) ≤ 2 ^ n * t := le_trans (Nat.cast_nonneg m) e1
          have hfl : m ≤ ⌊(2 : ℝ) ^ n * t⌋₊ := Nat.le_floor e1
          have hfl2 : ⌊(2 : ℝ) ^ n * t⌋₊ ≤ m + 1 := Nat.floor_le_of_le (by push_cast; exact e2)
          unfold interp
          simp only
          rcases Nat.lt_or_ge ⌊(2 : ℝ) ^ n * t⌋₊ (m+1) with h | h
          · have hf : ⌊(2:ℝ)^n*t⌋₊ = m := by omega
            rw [hf, min_eq_left (by omega)]
          · have hf : ⌊(2:ℝ)^n*t⌋₊ = m + 1 := by omega
            have ht : (2:ℝ)^n * t = m + 1 := by
              have := Nat.floor_le hnn
              rw [hf] at this; push_cast at this; linarith
            rw [hf]
            rcases Nat.lt_or_ge (m+1) (2^n) with h' | h'
            · rw [min_eq_left (by omega), ht]; push_cast; ring
            · have h3 : 2^n - 1 = m := by omega
              rw [min_eq_right (by omega), h3]
        have grid : ∀ (n m : ℕ), m ≤ 2 ^ n → interp x n (dyadic n m) = x (dyadic n m) := by
          intro n m hm
          have hpos : (0 : ℝ) < 2 ^ n := by positivity
          have hc : (2:ℝ)^n * dyadic n m = m := by unfold dyadic; field_simp
          rcases Nat.lt_or_ge m (2^n) with h | h
          · rw [key n m _ h (by unfold dyadic; exact le_refl _) (by unfold dyadic; gcongr; linarith), hc]
            ring
          · have hm' : m = 2^n := le_antisymm hm h
            have h1 : 1 ≤ m := by rw [hm']; exact Nat.one_le_two_pow
            have hcast : ((m - 1 : ℕ) : ℝ) = (m:ℝ) - 1 := by push_cast [h1]; ring
            have := key n (m-1) (dyadic n m) (by omega)
              (by unfold dyadic; rw [hcast]; gcongr; linarith)
              (by unfold dyadic; rw [hcast]; ring_nf; exact le_refl _)
            rw [this, Nat.sub_add_cancel h1, hc, hcast]
            ring
        obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        have hc2 : (2:ℝ)^(n+1) = 2 * 2^n := by ring
        have hpn : (0:ℝ) < 2^n := by positivity
        -- grid values
        have gval : ∀ m : ℕ, m ≤ 2 ^ (n+1) →
            |interp x (n+1) (dyadic (n+1) m) - interp x n (dyadic (n+1) m)| ≤ maxDisp x (n+1) := by
          intro m hm
          have hM0 : 0 ≤ maxDisp x (n+1) := by
            unfold maxDisp
            exact le_trans (abs_nonneg _) (Finset.le_sup' (fun j => |disp x (n+1) j|) (Finset.mem_range.2 (Nat.two_pow_pos _)))
          rw [grid (n+1) m hm]
          rcases Nat.even_or_odd' m with ⟨p, rfl | rfl⟩
          · have hp : p ≤ 2^n := by rw [pow_succ] at hm; omega
            have hd : dyadic (n+1) (2*p) = dyadic n p := by
              unfold dyadic; push_cast; field_simp; ring
            rw [hd, grid n p hp]; simpa using hM0
          · have hp : p < 2^n := by rw [pow_succ] at hm; omega
            have hd : (2:ℝ)^n * dyadic (n+1) (2*p+1) - p = 1/2 := by
              unfold dyadic; push_cast; field_simp; ring
            rw [key n p _ hp (by unfold dyadic; push_cast; rw [div_le_div_iff₀ (by positivity) (by positivity)]; ring_nf; nlinarith)
              (by unfold dyadic; push_cast; rw [div_le_div_iff₀ (by positivity) (by positivity)]; ring_nf; nlinarith), hd]
            have : x (dyadic (n + 1) (2 * p + 1)) - (x (dyadic n p) + 1 / 2 * (x (dyadic n (p + 1)) - x (dyadic n p))) = disp x (n+1) p := by
              unfold disp; simp only [Nat.add_sub_cancel]; ring
            rw [this]
            unfold maxDisp
            exact Finset.le_sup' (fun j => |disp x (n+1) j|) (by simp only [Nat.add_sub_cancel]; exact Finset.mem_range.2 hp)
        have piece : ∀ m : ℕ, m < 2 ^ (n+1) → ∀ t : ℝ, (m:ℝ) / 2^(n+1) ≤ t → t ≤ ((m:ℝ)+1) / 2^(n+1) →
            interp x (n+1) t - interp x n t =
              (interp x (n+1) (dyadic (n+1) m) - interp x n (dyadic (n+1) m)) +
              ((2:ℝ)^(n+1) * t - m) * ((interp x (n+1) (dyadic (n+1) (m+1)) - interp x n (dyadic (n+1) (m+1)))
                - (interp x (n+1) (dyadic (n+1) m) - interp x n (dyadic (n+1) m))) := by
          intro m hm t h1 h2
          set p := m / 2 with hpdef
          have hp1 : 2 * p ≤ m := by omega
          have hp2 : m + 1 ≤ 2 * p + 2 := by omega
          have hp : p < 2 ^ n := by rw [pow_succ] at hm; omega
          have hp1' : 2 * (p:ℝ) ≤ m := by exact_mod_cast hp1
          have hp2' : (m:ℝ) + 1 ≤ 2 * p + 2 := by exact_mod_cast hp2
          have inP : ∀ t' : ℝ, (m:ℝ) / 2^(n+1) ≤ t' → t' ≤ ((m:ℝ)+1) / 2^(n+1) →
              (p:ℝ) / 2^n ≤ t' ∧ t' ≤ ((p:ℝ)+1) / 2^n := by
            intro t' h1 h2
            rw [hc2] at h1 h2
            constructor
            · refine le_trans ?_ h1
              rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
            · refine le_trans h2 ?_
              rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
          have haL : (m:ℝ) / 2^(n+1) ≤ dyadic (n+1) m := by unfold dyadic; exact le_refl _
          have haR : dyadic (n+1) m ≤ ((m:ℝ)+1) / 2^(n+1) := by unfold dyadic; gcongr; linarith
          have hbL : (m:ℝ) / 2^(n+1) ≤ dyadic (n+1) (m+1) := by unfold dyadic; push_cast; gcongr; linarith
          have hbR : dyadic (n+1) (m+1) ≤ ((m:ℝ)+1) / 2^(n+1) := by unfold dyadic; push_cast; exact le_refl _
          rw [key (n+1) m t hm h1 h2, key (n+1) m _ hm haL haR, key (n+1) m _ hm hbL hbR,
            key n p t hp (inP t h1 h2).1 (inP t h1 h2).2,
            key n p _ hp (inP _ haL haR).1 (inP _ haL haR).2,
            key n p _ hp (inP _ hbL hbR).1 (inP _ hbL hbR).2]
          have ea : (2:ℝ)^(n+1) * dyadic (n+1) m = m := by unfold dyadic; field_simp
          have eb : (2:ℝ)^(n+1) * dyadic (n+1) (m+1) = m + 1 := by unfold dyadic; push_cast; field_simp
          have ea' : (2:ℝ)^n * dyadic (n+1) m = m / 2 := by unfold dyadic; rw [hc2]; field_simp
          have eb' : (2:ℝ)^n * dyadic (n+1) (m+1) = (m + 1) / 2 := by unfold dyadic; push_cast; rw [hc2]; field_simp
          have et : (2:ℝ)^(n+1) * t = 2 * (2^n * t) := by rw [hc2]; ring
          rw [ea, eb, ea', eb', et]
          ring
        have locate : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ m : ℕ, m < 2 ^ (n+1) ∧ (m:ℝ) / 2^(n+1) ≤ t ∧ t ≤ ((m:ℝ)+1) / 2^(n+1) := by
          intro t h0 h1
          have hcpos : (0:ℝ) < 2^(n+1) := by positivity
          have hnn : (0:ℝ) ≤ 2^(n+1) * t := by positivity
          rcases Nat.lt_or_ge ⌊(2:ℝ)^(n+1) * t⌋₊ (2^(n+1)) with h | h
          · refine ⟨_, h, ?_, ?_⟩
            · rw [div_le_iff₀ hcpos]; have := Nat.floor_le hnn; linarith
            · rw [le_div_iff₀ hcpos]; have := (Nat.lt_floor_add_one ((2:ℝ)^(n+1) * t)).le; linarith
          · have h1' : (1:ℕ) ≤ 2^(n+1) := Nat.one_le_two_pow
            have hge : (2:ℝ)^(n+1) ≤ 2^(n+1)*t := le_trans (by exact_mod_cast h) (Nat.floor_le hnn)
            refine ⟨2^(n+1) - 1, by omega, ?_, ?_⟩
            · push_cast [h1']; rw [div_le_iff₀ hcpos]; nlinarith
            · push_cast [h1']; rw [le_div_iff₀ hcpos]; nlinarith
        have hM0 : 0 ≤ maxDisp x (n+1) := by
          unfold maxDisp
          exact le_trans (abs_nonneg _) (Finset.le_sup' (fun j => |disp x (n+1) j|) (Finset.mem_range.2 (Nat.two_pow_pos _)))
        have hcpos : (0:ℝ) < 2^(n+1) := by positivity
        have mem1 : ∀ m : ℕ, m < 2 ^ (n+1) → m + 1 ≤ 2 ^ (n+1) := fun m hm => hm
        have absF : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |interp x (n+1) t - interp x n t| ≤ maxDisp x (n+1) := by
          intro t h0 h1
          obtain ⟨m, hm, hl, hr⟩ := locate t h0 h1
          rw [piece m hm t hl hr]
          have ga := gval m hm.le
          have gb := gval (m+1) (mem1 m hm)
          have l0 : 0 ≤ (2:ℝ)^(n+1) * t - m := by rw [div_le_iff₀ hcpos] at hl; linarith
          have l1 : (2:ℝ)^(n+1) * t - m ≤ 1 := by rw [le_div_iff₀ hcpos] at hr; linarith
          rw [abs_le] at ga gb ⊢
          constructor <;> nlinarith
        have lipP : ∀ m : ℕ, m < 2 ^ (n+1) → ∀ s t : ℝ, (m:ℝ) / 2^(n+1) ≤ s → s ≤ t → t ≤ ((m:ℝ)+1) / 2^(n+1) →
            |(interp x (n+1) t - interp x n t) - (interp x (n+1) s - interp x n s)|
              ≤ 2 * maxDisp x (n+1) * ((2:ℝ)^(n+1) * (t - s)) := by
          intro m hm s t hs hst ht
          rw [piece m hm t (hs.trans hst) ht, piece m hm s hs (hst.trans ht)]
          have ga := gval m hm.le
          have gb := gval (m+1) (mem1 m hm)
          have hd : 0 ≤ (2:ℝ)^(n+1) * (t - s) := by have : 0 ≤ t - s := by linarith
                                                    positivity
          have e : ∀ A B : ℝ, A + ((2:ℝ)^(n+1) * t - m) * (B - A) - (A + ((2:ℝ)^(n+1) * s - m) * (B - A))
              = ((2:ℝ)^(n+1) * (t - s)) * (B - A) := by intro A B; ring
          rw [e, abs_mul, abs_of_nonneg hd]
          have : |interp x (n + 1) (dyadic (n + 1) (m + 1)) - interp x n (dyadic (n + 1) (m + 1)) -
              (interp x (n + 1) (dyadic (n + 1) m) - interp x n (dyadic (n + 1) m))| ≤ 2 * maxDisp x (n+1) := by
            refine (abs_sub _ _).trans ?_; linarith
          nlinarith
        unfold HolderBound
        intro s hs t ht hst
        simp only [Real.norm_eq_abs]
        set u := (2:ℝ)^(n+1) * (t - s) with hu
        have hupos : 0 < u := by have : 0 < t - s := by linarith
                                 positivity
        have step1 : |(interp x (n+1) t - interp x n t) - (interp x (n+1) s - interp x n s)|
            ≤ 2 * maxDisp x (n+1) * u ^ alpha := by
          rcases le_or_gt 1 u with hu1 | hu1
          · have := Real.one_le_rpow hu1 ha.le
            have := absF t ht.1 ht.2
            have := absF s hs.1 hs.2
            refine (abs_sub _ _).trans ?_
            nlinarith
          · have hle : u ≤ u ^ alpha := by
              have := Real.rpow_le_rpow_of_exponent_ge hupos hu1.le ha1
              simpa using this
            suffices h : |(interp x (n+1) t - interp x n t) - (interp x (n+1) s - interp x n s)|
                ≤ 2 * maxDisp x (n+1) * u by nlinarith
            obtain ⟨m, hm, hl, hr⟩ := locate s hs.1 hs.2
            rcases le_or_gt t (((m:ℝ)+1) / 2^(n+1)) with htr | htr
            · exact lipP m hm s t hl hst.le htr
            · have hm1 : m + 1 < 2 ^ (n+1) := by
                rw [div_lt_iff₀ hcpos] at htr
                have : ((m + 1 : ℕ) : ℝ) < ((2 ^ (n+1) : ℕ) : ℝ) := by push_cast; nlinarith [ht.2]
                exact_mod_cast this
              have hgt : t ≤ (((m+1 : ℕ) : ℝ) + 1) / 2^(n+1) := by
                push_cast
                rw [le_div_iff₀ hcpos]; rw [le_div_iff₀ hcpos] at hr; nlinarith
              have h1 := lipP m hm s (((m:ℝ)+1) / 2^(n+1)) hl hr le_rfl
              have h2 := lipP (m+1) hm1 (((m:ℝ)+1) / 2^(n+1)) t (by push_cast; exact le_rfl) htr.le hgt
              have := abs_sub_le ((interp x (n+1) t - interp x n t))
                (interp x (n+1) (((m:ℝ)+1) / 2^(n+1)) - interp x n (((m:ℝ)+1) / 2^(n+1)))
                (interp x (n+1) s - interp x n s)
              have e : 2 * maxDisp x (n + 1) * (2 ^ (n + 1) * (t - (↑m + 1) / 2 ^ (n + 1))) +
                  2 * maxDisp x (n + 1) * (2 ^ (n + 1) * ((↑m + 1) / 2 ^ (n + 1) - s)) = 2 * maxDisp x (n+1) * u := by
                rw [hu]; ring
              linarith
        have step2 : 2 * maxDisp x (n+1) * u ^ alpha
            ≤ (2:ℝ) ^ (alpha * (((n + 1 : ℕ) : ℝ) - 1) + 2) * maxDisp x (n+1) * (t - s) ^ alpha := by
          have hts : 0 ≤ t - s := by linarith
          have e1 : u ^ alpha = (2:ℝ) ^ (((n:ℝ)+1) * alpha) * (t - s) ^ alpha := by
            rw [hu, Real.mul_rpow (by positivity) hts, Real.rpow_mul (by norm_num)]
            congr 2
            rw [← Real.rpow_natCast]; push_cast; ring_nf
          rw [e1]
          have e2 : 2 * (2:ℝ) ^ (((n:ℝ)+1) * alpha) = (2:ℝ) ^ (1 + ((n:ℝ)+1) * alpha) := by
            rw [Real.rpow_add (by norm_num), Real.rpow_one]
          have e3 : (2:ℝ) ^ (1 + ((n:ℝ)+1) * alpha) ≤ (2:ℝ) ^ (alpha * (((n + 1 : ℕ) : ℝ) - 1) + 2) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            push_cast; nlinarith
          have hp : 0 ≤ maxDisp x (n+1) * (t - s) ^ alpha := mul_nonneg hM0 (Real.rpow_nonneg hts _)
          calc 2 * maxDisp x (n+1) * ((2:ℝ) ^ (((n:ℝ)+1) * alpha) * (t - s) ^ alpha)
              = (2 * (2:ℝ) ^ (((n:ℝ)+1) * alpha)) * (maxDisp x (n+1) * (t - s) ^ alpha) := by ring
            _ ≤ (2:ℝ) ^ (alpha * (((n + 1 : ℕ) : ℝ) - 1) + 2) * (maxDisp x (n+1) * (t - s) ^ alpha) := by
              rw [e2]; exact mul_le_mul_of_nonneg_right e3 hp
            _ = _ := by ring
        exact step1.trans step2
