-- Prove2me | solution 1 for FBMStrongSim.RecordBreak.Supplement.lemma_5_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:21:32.278428+00:00
-- url     : https://prove2.me/submissions/ef6b51a7-7315-43f1-853b-cde2b418dafc

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_HolderModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_YoungModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_EulerModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_GridHolderModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_YoungConstants

open FBMStrongSim
open FBMStrongSim.RecordBreak
open FBMStrongSim.RecordBreak.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Lemma 5.8 (p.31), corrected entrywise constant L; the remainder is forward in time. -/
theorem solution {d h : ℕ} (hd : 0 < d) (hh : 0 < h) {alpha C F0 F1 F2 : ℝ}
    (ha : 1 / 2 < alpha) (ha1 : alpha ≤ 1) (hC : 0 < C)
    {f : Field d h} (hf : CoefficientBounds f F0 F1 F2)
    {x : ℝ → Vec h} (hx : HolderBound alpha C x)
    (y0 : Vec d) (n : ℕ) :
    (∀ j r : ℕ, j ≤ 2 ^ n → r ≤ 2 ^ n →
      ‖eulerValue f x y0 n j - eulerValue f x y0 n r‖ ≤
        correctedG1 d h alpha C F0 F1 * |dyadic n j - dyadic n r| ^ alpha) ∧
    (∀ r j : ℕ, r ≤ j → j ≤ 2 ^ n →
      ‖eulerValue f x y0 n j - eulerValue f x y0 n r -
          f (eulerValue f x y0 n r) (x (dyadic n j) - x (dyadic n r))‖ ≤
        correctedG2 d h alpha C F0 F1 * (dyadic n j - dyadic n r) ^ (2 * alpha)) := by
          have hF0 := hf.pos0
          have hF1 := hf.pos1
          have hdR : (0:ℝ) < d := by exact_mod_cast hd
          have hhR : (0:ℝ) < h := by exact_mod_cast hh
          have ha0 : 0 < alpha := by linarith
          -- coordinates expansion
          have hexp : ∀ {m : ℕ} (u : Vec m), u = ∑ k, u k • basisVec k := by
            intro m u
            funext i
            simp [basisVec, Finset.sum_apply, Pi.single_apply]
          have hval : ∀ (a : Vec d) (u : Vec h), ‖f a u‖ ≤ h * F0 * ‖u‖ := by
            intro a u
            rw [pi_norm_le_iff_of_nonneg (by positivity)]
            intro i
            have e : f a u i = ∑ k, u k * f a (basisVec k) i := by
              conv_lhs => rw [hexp u]
              simp [map_sum, Finset.sum_apply]
            rw [e]
            calc ‖∑ k, u k * f a (basisVec k) i‖ ≤ ∑ k : Fin h, ‖u k * f a (basisVec k) i‖ := norm_sum_le _ _
              _ ≤ ∑ k : Fin h, ‖u‖ * F0 := by
                  apply Finset.sum_le_sum
                  intro k _
                  rw [norm_mul]
                  exact mul_le_mul (norm_le_pi_norm u k) (hf.value a i k) (norm_nonneg _) (norm_nonneg _)
              _ = h * F0 * ‖u‖ := by simp; ring
          have hder : ∀ a : Vec d, ‖fderiv ℝ f a‖ ≤ d * h * F1 := by
            intro a
            apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
            intro v
            apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
            intro u
            rw [pi_norm_le_iff_of_nonneg (by positivity)]
            intro i
            have e : fderiv ℝ f a v u i =
                ∑ l, ∑ k, v l * (u k * fderiv ℝ f a (basisVec l) (basisVec k) i) := by
              have e1 : fderiv ℝ f a v = ∑ l, v l • fderiv ℝ f a (basisVec l) := by
                conv_lhs => rw [hexp v]
                simp [map_sum]
              have e2 : ∀ l, fderiv ℝ f a (basisVec l) u i =
                  ∑ k, u k * fderiv ℝ f a (basisVec l) (basisVec k) i := by
                intro l
                conv_lhs => rw [hexp u]
                simp [map_sum, Finset.sum_apply]
              rw [e1]
              simp only [_root_.sum_apply, Finset.sum_apply,
                _root_.smul_apply, Pi.smul_apply, smul_eq_mul, e2, Finset.mul_sum]
            rw [e]
            calc ‖∑ l, ∑ k, v l * (u k * fderiv ℝ f a (basisVec l) (basisVec k) i)‖
                ≤ ∑ l : Fin d, ∑ k : Fin h, ‖v l * (u k * fderiv ℝ f a (basisVec l) (basisVec k) i)‖ :=
                  (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_sum_le _ _)
              _ ≤ ∑ l : Fin d, ∑ k : Fin h, ‖v‖ * (‖u‖ * F1) := by
                  apply Finset.sum_le_sum
                  intro l _
                  apply Finset.sum_le_sum
                  intro k _
                  rw [norm_mul, norm_mul]
                  exact mul_le_mul (norm_le_pi_norm v l)
                    (mul_le_mul (norm_le_pi_norm u k) (hf.deriv a i k l) (norm_nonneg _) (norm_nonneg _))
                    (by positivity) (norm_nonneg _)
              _ = d * h * F1 * ‖v‖ * ‖u‖ := by simp; ring
          have hlip : ∀ a b : Vec d, ‖f b - f a‖ ≤ d * h * F1 * ‖b - a‖ := by
            intro a b
            have hdiff : Differentiable ℝ f := hf.smooth.differentiable (by norm_num)
            exact Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ)
              (fun z _ => hdiff z) (fun z _ => hder z) convex_univ (Set.mem_univ a) (Set.mem_univ b)
          obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / 2 ^ n := ⟨_, rfl⟩
          have hδ0 : 0 < δ := by rw [hδ]; positivity
          have hδ1 : (2:ℝ) ^ n * δ = 1 := by rw [hδ]; field_simp
          have hdy : ∀ k : ℕ, dyadic n k = k * δ := by
            intro k; rw [hδ, dyadic]; ring
          have hgrid : ∀ k : ℕ, k ≤ 2 ^ n → (k:ℝ) * δ ≤ 1 := by
            intro k hk
            rw [← hδ1]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hδ0.le
          obtain ⟨X, hX⟩ : ∃ X : ℕ → Vec h, X = fun k => x (dyadic n k) := ⟨_, rfl⟩
          have hXb : ∀ j N : ℕ, j + N ≤ 2 ^ n → ‖X (j + N) - X j‖ ≤ C * (N * δ) ^ alpha := by
            intro j N hN
            rcases Nat.eq_zero_or_pos N with h0 | h0
            · subst h0
              simp [Real.zero_rpow ha0.ne']
            · have h1 := hx (dyadic n j) ⟨by rw [hdy]; positivity, by rw [hdy]; exact hgrid j (by omega)⟩
                (dyadic n (j + N)) ⟨by rw [hdy]; positivity, by rw [hdy]; exact hgrid _ hN⟩
                (by rw [hdy, hdy]; exact mul_lt_mul_of_pos_right (by exact_mod_cast (by omega)) hδ0)
              have e : dyadic n (j + N) - dyadic n j = N * δ := by
                rw [hdy, hdy]; push_cast; ring
              rw [e] at h1
              rw [hX]; exact h1
          obtain ⟨y, hy⟩ : ∃ y : ℕ → Vec d, y = eulerValue f x y0 n := ⟨_, rfl⟩
          have hstep : ∀ k, y (k + 1) = y k + f (y k) (X (k + 1) - X k) := by
            intro k; rw [hy, hX]; rfl
          -- constants
          obtain ⟨a0, ha0'⟩ : ∃ a0 : ℝ, a0 = h * F0 * C := ⟨_, rfl⟩
          have ha0p : 0 < a0 := by rw [ha0']; positivity
          obtain ⟨L, hL⟩ : ∃ L : ℝ, L = correctedL d h alpha C F0 F1 := ⟨_, rfl⟩
          obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (2:ℝ) ^ (1 - 2 * alpha) := ⟨_, rfl⟩
          have hθ1 : θ < 1 := by
            rw [hθ]; exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
          have hLeq : L * (1 - θ) = 4 * ((h : ℝ) * C) ^ 2 * d * F1 * F0 := by
            have : 1 - θ ≠ 0 := by linarith
            rw [hL, correctedL, ← hθ]; field_simp
          have hLp : 0 < L := by
            have h1 : 0 < L * (1 - θ) := by rw [hLeq]; positivity
            exact (pos_iff_pos_of_mul_pos h1).2 (by linarith)
          obtain ⟨ω, hω⟩ : ∃ ω : ℝ, ω = correctedOmega d h alpha C F0 F1 := ⟨_, rfl⟩
          have hωe : ω = (a0 / L) ^ (1 / alpha) := by rw [hω, correctedOmega, ← hL, ← ha0']
          have hωp : 0 < ω := by rw [hωe]; positivity
          have hωα : L * ω ^ alpha = a0 := by
            rw [hωe, ← Real.rpow_mul (by positivity), one_div_mul_cancel ha0.ne', Real.rpow_one]
            field_simp
          have hsq : ∀ t : ℝ, 0 ≤ t → t ^ (2 * alpha) = t ^ alpha * t ^ alpha := by
            intro t ht
            rw [two_mul, Real.rpow_add_of_nonneg ht ha0.le ha0.le]
          have hone : ∀ j N : ℕ, j + N ≤ 2 ^ n → ‖f (y j) (X (j + N) - X j)‖ ≤ a0 * (N * δ) ^ alpha := by
            intro j N hN
            calc _ ≤ h * F0 * ‖X (j + N) - X j‖ := hval _ _
              _ ≤ h * F0 * (C * (N * δ) ^ alpha) :=
                mul_le_mul_of_nonneg_left (hXb j N hN) (by positivity)
              _ = _ := by rw [ha0']; ring
          -- local estimate
          have hloc : ∀ N j : ℕ, j + N ≤ 2 ^ n → (N:ℝ) * δ ≤ ω →
              ‖y (j + N) - y j - f (y j) (X (j + N) - X j)‖ ≤ L * (N * δ) ^ (2 * alpha) := by
            intro N
            induction N using Nat.strong_induction_on with
            | _ N ih =>
            intro j hN hNω
            rcases Nat.lt_or_ge N 2 with h2 | h2
            · have hz : y (j + N) - y j - f (y j) (X (j + N) - X j) = 0 := by
                interval_cases N
                · simp
                · rw [hstep j]; abel
              rw [hz, norm_zero]; positivity
            obtain ⟨p, hp⟩ : ∃ p, p = N / 2 := ⟨_, rfl⟩
            obtain ⟨q, hq⟩ : ∃ q, q = N - p - 1 := ⟨_, rfl⟩
            have hpq : N = p + 1 + q := by omega
            have hp2 : 2 * p ≤ N := by omega
            have hq2 : 2 * q ≤ N := by omega
            have hT0 : (0:ℝ) ≤ N * δ := by positivity
            have hle : ∀ m : ℕ, m ≤ N → (m:ℝ) * δ ≤ N * δ := fun m hm =>
              mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hδ0.le
            have hleα : ∀ m : ℕ, m ≤ N → ((m:ℝ) * δ) ^ alpha ≤ (N * δ) ^ alpha := fun m hm =>
              Real.rpow_le_rpow (by positivity) (hle m hm) ha0.le
            have hhalf : ∀ m : ℕ, 2 * m ≤ N →
                ((m:ℝ) * δ) ^ (2 * alpha) ≤ θ / 2 * (N * δ) ^ (2 * alpha) := by
              intro m hm
              have hm' : (2:ℝ) * m ≤ N := by exact_mod_cast hm
              have h1 : (m:ℝ) * δ ≤ 1 / 2 * (N * δ) := by
                rw [← mul_assoc]
                exact mul_le_mul_of_nonneg_right (by linarith only [hm']) hδ0.le
              have h2 : θ / 2 = (1 / 2 : ℝ) ^ (2 * alpha) := by
                rw [hθ, Real.rpow_sub (by norm_num), one_div, Real.inv_rpow (by norm_num), Real.rpow_one]
                field_simp
              rw [h2, ← Real.mul_rpow (by norm_num) hT0]
              exact Real.rpow_le_rpow (by positivity) h1 (by positivity)
            have hI1 := ih p (by omega) j (by omega) ((hle p (by omega)).trans hNω)
            have hI2 := ih q (by omega) (j + p + 1) (by omega) ((hle q (by omega)).trans hNω)
            have hy1 : ‖y (j + p) - y j‖ ≤ 2 * a0 * (N * δ) ^ alpha := by
              have e : y (j + p) - y j = (y (j + p) - y j - f (y j) (X (j + p) - X j)) +
                f (y j) (X (j + p) - X j) := by abel
              have h3 : L * ((p:ℝ) * δ) ^ (2 * alpha) ≤ a0 * (p * δ) ^ alpha := by
                rw [hsq _ (by positivity), ← hωα, ← mul_assoc]
                have : ((p:ℝ) * δ) ^ alpha ≤ ω ^ alpha :=
                  Real.rpow_le_rpow (by positivity) ((hle p (by omega)).trans hNω) ha0.le
                gcongr
              calc ‖y (j + p) - y j‖ ≤ ‖y (j + p) - y j - f (y j) (X (j + p) - X j)‖ +
                    ‖f (y j) (X (j + p) - X j)‖ := by
                      conv_lhs => rw [e]
                      exact norm_add_le _ _
                _ ≤ L * ((p:ℝ) * δ) ^ (2 * alpha) + a0 * (p * δ) ^ alpha :=
                  add_le_add hI1 (hone j p (by omega))
                _ ≤ 2 * a0 * (p * δ) ^ alpha := by linarith
                _ ≤ _ := mul_le_mul_of_nonneg_left (hleα p (by omega)) (by positivity)
            have hy2 : ‖y (j + p + 1) - y (j + p)‖ ≤ 2 * a0 * (N * δ) ^ alpha := by
              have e : y (j + p + 1) - y (j + p) = f (y (j + p)) (X (j + p + 1) - X (j + p)) := by
                rw [hstep (j + p)]; abel
              rw [e]
              calc _ ≤ a0 * ((1:ℕ) * δ) ^ alpha := hone (j + p) 1 (by omega)
                _ ≤ a0 * (N * δ) ^ alpha := mul_le_mul_of_nonneg_left (hleα 1 (by omega)) ha0p.le
                _ ≤ _ := by
                  have : 0 ≤ a0 * (N * δ) ^ alpha := by positivity
                  linarith
            have hcross : ∀ a b : Vec d, ∀ k m : ℕ, k + m ≤ 2 ^ n → m ≤ N →
                ‖b - a‖ ≤ 2 * a0 * (N * δ) ^ alpha →
                ‖(f b - f a) (X (k + m) - X k)‖ ≤ L * (1 - θ) / 2 * (N * δ) ^ (2 * alpha) := by
              intro a b k m hk hm hab
              calc _ ≤ ‖f b - f a‖ * ‖X (k + m) - X k‖ := ContinuousLinearMap.le_opNorm _ _
                _ ≤ (d * h * F1 * (2 * a0 * (N * δ) ^ alpha)) * (C * (N * δ) ^ alpha) := by
                  apply mul_le_mul _ _ (norm_nonneg _) (by positivity)
                  · exact (hlip a b).trans (mul_le_mul_of_nonneg_left hab (by positivity))
                  · exact (hXb k m hk).trans (mul_le_mul_of_nonneg_left (hleα m hm) hC.le)
                _ = _ := by rw [hLeq, hsq _ hT0, ha0']; ring
            have hc1 := hcross (y j) (y (j + p)) (j + p) (1 + q) (by omega) (by omega) hy1
            have hc2 := hcross (y (j + p)) (y (j + p + 1)) (j + p + 1) q (by omega) (by omega) hy2
            have e1 : j + N = j + p + 1 + q := by omega
            have e2 : j + p + (1 + q) = j + p + 1 + q := by omega
            rw [e2] at hc1
            have hdec : y (j + N) - y j - f (y j) (X (j + N) - X j) =
                (y (j + p) - y j - f (y j) (X (j + p) - X j)) +
                (y (j + p + 1 + q) - y (j + p + 1) -
                  f (y (j + p + 1)) (X (j + p + 1 + q) - X (j + p + 1))) +
                (f (y (j + p)) - f (y j)) (X (j + p + 1 + q) - X (j + p)) +
                (f (y (j + p + 1)) - f (y (j + p))) (X (j + p + 1 + q) - X (j + p + 1)) := by
              have hs := hstep (j + p)
              have hs' : f (y (j + p)) (X (j + p + 1) - X (j + p)) = y (j + p + 1) - y (j + p) := by
                rw [hs]; abel
              rw [e1]
              simp only [_root_.sub_apply, map_sub] at hs' ⊢
              have hs'' : y (j + p + 1) = f (y (j + p)) (X (j + p + 1)) - f (y (j + p)) (X (j + p)) + y (j + p) := by
                rw [hs']; abel
              generalize f (y (j + p + 1)) = g at *
              rw [hs'']
              abel
            rw [hdec]
            refine (norm_add_le _ _).trans ?_
            refine (add_le_add_left (norm_add_le _ _) _).trans ?_
            refine (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _).trans ?_
            have h5 := mul_le_mul_of_nonneg_left (hhalf p hp2) hLp.le
            have h6 := mul_le_mul_of_nonneg_left (hhalf q hq2) hLp.le
            have h7 : L * (N * δ) ^ (2 * alpha) = L * (θ / 2 * (N * δ) ^ (2 * alpha)) +
              L * (θ / 2 * (N * δ) ^ (2 * alpha)) + L * (1 - θ) / 2 * (N * δ) ^ (2 * alpha) +
              L * (1 - θ) / 2 * (N * δ) ^ (2 * alpha) := by ring
            rw [h7]
            linarith
          -- blocks
          obtain ⟨A, hA⟩ : ∃ A : ℝ, A = L + a0 := ⟨_, rfl⟩
          have hAp : 0 < A := by rw [hA]; positivity
          obtain ⟨K, hK⟩ : ∃ K : ℕ, K = max 1 ⌊ω / δ⌋₊ := ⟨_, rfl⟩
          have hK1 : 1 ≤ K := by rw [hK]; exact le_max_left _ _
          have hKω : ω / 2 ≤ K * δ := by
            have h1 : ω / δ < ⌊ω / δ⌋₊ + 1 := Nat.lt_floor_add_one _
            have h2 : (⌊ω / δ⌋₊ : ℝ) ≤ K := by rw [hK]; exact_mod_cast le_max_right _ _
            have h3 : (1:ℝ) ≤ K := by exact_mod_cast hK1
            have h4 : ω / δ ≤ 2 * K := by linarith
            rw [div_le_iff₀ hδ0] at h4
            linarith
          have hblock : ∀ N j : ℕ, j + N ≤ 2 ^ n → N ≤ K → ‖y (j + N) - y j‖ ≤ A * (N * δ) ^ alpha := by
            intro N j hN hNK
            have hb := hone j N hN
            have hIb : ‖y (j + N) - y j - f (y j) (X (j + N) - X j)‖ ≤ L * (N * δ) ^ alpha := by
              rcases Nat.lt_or_ge N 2 with h2 | h2
              · have hz : y (j + N) - y j - f (y j) (X (j + N) - X j) = 0 := by
                  interval_cases N
                  · simp
                  · rw [hstep j]; abel
                rw [hz, norm_zero]; positivity
              · have h3 : N ≤ ⌊ω / δ⌋₊ := by
                  rcases le_max_iff.1 (hK ▸ hNK) with h | h
                  · omega
                  · exact h
                have h4 : (N:ℝ) ≤ ω / δ := (Nat.le_floor_iff (by positivity)).1 h3
                rw [le_div_iff₀ hδ0] at h4
                refine (hloc N j hN h4).trans (mul_le_mul_of_nonneg_left ?_ hLp.le)
                rw [hsq _ (by positivity)]
                have h5 : ((N:ℝ) * δ) ^ alpha ≤ 1 :=
                  Real.rpow_le_one (by positivity) (hgrid N (by omega)) ha0.le
                exact mul_le_of_le_one_left (by positivity) h5
            have e : y (j + N) - y j = (y (j + N) - y j - f (y j) (X (j + N) - X j)) +
                f (y j) (X (j + N) - X j) := by abel
            rw [e]
            refine (norm_add_le _ _).trans ?_
            rw [hA, add_mul]
            exact add_le_add hIb hb
          -- two-term Jensen
          have hjen : ∀ m : ℕ, 1 ≤ m → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
              (m:ℝ) ^ (1 - alpha) * a ^ alpha + b ^ alpha ≤
                ((m + 1 : ℕ):ℝ) ^ (1 - alpha) * (a + b) ^ alpha := by
            intro m hm a b hna hnb
            have hmR : (0:ℝ) < m := by exact_mod_cast hm
            have hc := (Real.concaveOn_rpow ha0.le ha1).2
              (show a / (m:ℝ) ∈ Set.Ici 0 from Set.mem_Ici.2 (by positivity)) (Set.mem_Ici.2 hnb)
              (show (0:ℝ) ≤ m / (m + 1) by positivity) (show (0:ℝ) ≤ 1 / (m + 1) by positivity)
              (by field_simp)
            simp only [smul_eq_mul] at hc
            have e1 : (m:ℝ) / (m + 1) * (a / m) + 1 / (m + 1) * b = (a + b) / (m + 1) := by
              field_simp
            rw [e1, Real.div_rpow hna hmR.le, Real.div_rpow (by positivity) (by positivity)] at hc
            have hmm : (m:ℝ) ^ (1 - alpha) = m / m ^ alpha := by
              rw [Real.rpow_sub hmR, Real.rpow_one]
            have hmm' : ((m + 1 : ℕ):ℝ) ^ (1 - alpha) = (m + 1) / (m + 1) ^ alpha := by
              push_cast
              rw [Real.rpow_sub (by positivity), Real.rpow_one]
            rw [hmm, hmm']
            have hc2 := mul_le_mul_of_nonneg_left hc (show (0:ℝ) ≤ m + 1 by positivity)
            have hmα : (0:ℝ) < m ^ alpha := by positivity
            have hmα' : (0:ℝ) < (m + 1 : ℝ) ^ alpha := by positivity
            calc _ = (m + 1 : ℝ) * (m / (m + 1) * (a ^ alpha / m ^ alpha) + 1 / (m + 1) * b ^ alpha) := by
                  field_simp
              _ ≤ _ := hc2
              _ = _ := by field_simp
          have hchain : ∀ m : ℕ, 1 ≤ m → ∀ N j : ℕ, j + N ≤ 2 ^ n → N ≤ m * K →
              ‖y (j + N) - y j‖ ≤ A * ((m:ℝ) ^ (1 - alpha) * (N * δ) ^ alpha) := by
            intro m hm
            induction m, hm using Nat.le_induction with
            | base =>
              intro N j hN hNK
              have := hblock N j hN (by omega)
              simpa using this
            | succ m hm ih =>
              intro N j hN hNK
              obtain ⟨N1, N2, hN12, hN1, hN2⟩ : ∃ N1 N2, N = N1 + N2 ∧ N1 ≤ m * K ∧ N2 ≤ K := by
                refine ⟨min N (m * K), N - min N (m * K), by omega, by omega, ?_⟩
                rw [add_mul, one_mul] at hNK
                omega
              have h1 := ih N1 j (by omega) hN1
              have h2 := hblock N2 (j + N1) (by omega) hN2
              have h3 := hjen m hm (N1 * δ) (N2 * δ) (by positivity) (by positivity)
              have e0 : j + N = j + N1 + N2 := by omega
              have e : y (j + N) - y j = (y (j + N1) - y j) + (y (j + N1 + N2) - y (j + N1)) := by
                rw [e0]; abel
              have e3 : (N:ℝ) * δ = N1 * δ + N2 * δ := by rw [hN12]; push_cast; ring
              rw [e, e3]
              refine (norm_add_le _ _).trans ?_
              refine (add_le_add h1 h2).trans ?_
              rw [← mul_add]
              exact mul_le_mul_of_nonneg_left h3 hAp.le
          have hglob : ∀ N j : ℕ, j + N ≤ 2 ^ n →
              ‖y (j + N) - y j‖ ≤ A * (1 + ω⁻¹) * (N * δ) ^ alpha := by
            intro N j hN
            obtain ⟨m, hm⟩ : ∃ m, m = N / K + 1 := ⟨_, rfl⟩
            have hm1 : 1 ≤ m := by rw [hm]; exact Nat.le_add_left 1 _
            have hmK : N ≤ m * K := by
              rw [hm]
              have := Nat.lt_div_mul_add (a := N) (b := K) (by omega)
              rw [add_mul, one_mul]; omega
            have h1 := hchain m hm1 N j hN hmK
            refine h1.trans ?_
            rw [mul_assoc]
            apply mul_le_mul_of_nonneg_left _ hAp.le
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm1
            have hmb : (m:ℝ) ≤ 1 + 2 * ω⁻¹ := by
              have h2 : (((N / K : ℕ)):ℝ) * K ≤ N := by exact_mod_cast Nat.div_mul_le_self N K
              have h3 := hgrid N (by omega)
              have h4 : ((N / K : ℕ):ℝ) * (ω / 2) ≤ 1 := by
                calc ((N / K : ℕ):ℝ) * (ω / 2) ≤ ((N / K : ℕ):ℝ) * (K * δ) :=
                      mul_le_mul_of_nonneg_left hKω (by positivity)
                  _ = ((N / K : ℕ):ℝ) * K * δ := by ring
                  _ ≤ N * δ := mul_le_mul_of_nonneg_right h2 hδ0.le
                  _ ≤ 1 := h3
              have h5 : ((N / K : ℕ):ℝ) ≤ 2 * ω⁻¹ := by
                rw [← div_eq_mul_inv, le_div_iff₀ hωp]; linarith
              rw [hm]; push_cast; linarith
            calc (m:ℝ) ^ (1 - alpha) ≤ (m:ℝ) ^ (1 / 2 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le hmR (by linarith)
              _ = Real.sqrt m := (Real.sqrt_eq_rpow _).symm
              _ ≤ 1 + ω⁻¹ := by
                  rw [Real.sqrt_le_iff]
                  refine ⟨by positivity, hmb.trans ?_⟩
                  have hsqω : (1 + ω⁻¹) ^ 2 = 1 + 2 * ω⁻¹ + (ω⁻¹) ^ 2 := by ring
                  rw [hsqω]
                  exact le_add_of_nonneg_right (sq_nonneg _)
          have hG1 : correctedG1 d h alpha C F0 F1 = A * (1 + ω⁻¹) := by
            rw [correctedG1, ← hL, ← hω, ← ha0', hA]
          have hG2 : correctedG2 d h alpha C F0 F1 =
              max ((2 * ω ^ (-alpha) + ω ^ (-1 - alpha)) * A) L := by
            rw [correctedG2, ← hL, ← hω, ← ha0', hA]
          have hdiffe : ∀ r N : ℕ, dyadic n (r + N) - dyadic n r = N * δ := by
            intro r N; rw [hdy, hdy]; push_cast; ring
          constructor
          · have key : ∀ j r : ℕ, r ≤ j → j ≤ 2 ^ n → ‖y j - y r‖ ≤
                correctedG1 d h alpha C F0 F1 * |dyadic n j - dyadic n r| ^ alpha := by
              intro j r hrj hj
              obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le hrj
              rw [hdiffe, abs_of_nonneg (by positivity), hG1]
              exact hglob N r hj
            intro j r hj hr
            rw [← hy]
            rcases le_total r j with hrj | hrj
            · exact key j r hrj hj
            · rw [norm_sub_rev, abs_sub_comm]
              exact key r j hrj hr
          · intro r j hrj hj
            obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le hrj
            rw [hdiffe, hG2, ← hy]
            have hXe : x (dyadic n (r + N)) - x (dyadic n r) = X (r + N) - X r := by rw [hX]
            rw [hXe]
            rcases le_or_gt ((N:ℝ) * δ) ω with hN | hN
            · exact (hloc N r hj hN).trans
                (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
            · have hT0 : 0 < (N:ℝ) * δ := hωp.trans hN
              have h1 := hglob N r hj
              have h2 := hone r N hj
              refine (norm_sub_le _ _).trans ((add_le_add h1 h2).trans ?_)
              have h3 : A * (1 + ω⁻¹) * (N * δ) ^ alpha + a0 * (N * δ) ^ alpha ≤
                  A * (2 + ω⁻¹) * (N * δ) ^ alpha := by
                have : a0 * (N * δ) ^ alpha ≤ A * (N * δ) ^ alpha :=
                  mul_le_mul_of_nonneg_right (by rw [hA]; linarith) (by positivity)
                linarith
              refine h3.trans ?_
              refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
              have h4 : ω ^ (-1 - alpha) = ω⁻¹ * ω ^ (-alpha) := by
                rw [sub_eq_add_neg, Real.rpow_add hωp, Real.rpow_neg_one]
              have h5 : 1 ≤ ω ^ (-alpha) * (N * δ) ^ alpha := by
                rw [Real.rpow_neg hωp.le, ← div_eq_inv_mul, one_le_div (by positivity)]
                exact Real.rpow_le_rpow hωp.le hN.le ha0.le
              have h6 : (2 * ω ^ (-alpha) + ω ^ (-1 - alpha)) * A * (N * δ) ^ (2 * alpha) =
                  (A * (2 + ω⁻¹) * (N * δ) ^ alpha) * (ω ^ (-alpha) * (N * δ) ^ alpha) := by
                rw [h4, hsq _ hT0.le]; ring
              rw [h6]
              exact le_mul_of_one_le_right (by positivity) h5
