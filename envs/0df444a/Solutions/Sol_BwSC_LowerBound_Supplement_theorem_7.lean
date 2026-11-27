-- Prove2me | solution 1 for BwSC.LowerBound.Supplement.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:36:30.776722+00:00
-- url     : https://prove2.me/submissions/6e11b045-f794-4222-af44-84decad7bae5

import Mathlib
import Definitions.Def_BwSC_LowerBound_Supplement_Gap

open MeasureTheory ProbabilityTheory BanditAlgorithm

open BwSC
open BwSC.LowerBound
open BwSC.LowerBound.Supplement

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (K S T : ℕ), 1 < K → 2 * K ≤ T →
      ∀ π : BanditPolicy K, IsAdmissiblePolicy S T π →
        ((C / Real.log T * max (gapRateA K S T) (gapRateBLower K S T) : ℝ) : EReal) ≤
          gapWeightedWorstRegret π T := by
            classical
            have FIN :
                ∃ C : ℝ, 0 < C ∧ ∀ (K S T : ℕ) (X : ℝ), 1 < K → 2 * K ≤ T →
              (K : ℝ) / 384 ≤ X →
              (∀ (M : ℕ) (τ : ℕ → ℕ) (R : ℝ), 0 < M → (∀ j < M, τ j < τ (j+1)) → τ M ≤ T → 0 ≤ R → S < M * (K - 1) →
                (∀ j < M, R ≤ ((τ (j+1) : ℝ) - τ j) / 16) →
                (∀ j < M, R * (64 * M * τ j) ≤ ((M : ℝ) * ((K : ℝ) - 1) - S) * ((τ (j+1) : ℝ) - τ j)) →
                R * ((M : ℝ) * ((K : ℝ) - 1) - S) / (4 * M * K) ≤ X) →
              (∀ (M : ℕ) (τ : ℕ → ℕ) (R : ℝ), 0 < M → (∀ j < M, τ j < τ (j+1)) → τ M < T → 0 ≤ R → S = M * (K - 1) →
                (∀ j < M, R ≤ ((τ (j+1) : ℝ) - τ j) / 16) →
                (∀ j < M, R * (2048 * M * τ j) ≤ (τ (j+1) : ℝ) - τ j) →
                R ≤ ((T : ℝ) - τ M) / 16 → R * (2048 * M * τ (M-1)) ≤ (T : ℝ) - τ M →
                R / (64 * M * K) ≤ X) →
              C / Real.log T * max (gapRateA K S T) (gapRateBLower K S T) ≤ X := by
              classical
              have ML : ∀ {a b c : ℝ}, b ≤ c → 0 ≤ a → a * b ≤ a * c := fun h k => mul_le_mul_of_nonneg_left h k
              have MR : ∀ {a b c : ℝ}, b ≤ c → 0 ≤ a → b * a ≤ c * a := fun h k => mul_le_mul_of_nonneg_right h k
              have MP : ∀ {a b : ℝ}, 0 < a → 0 < b → 0 < a * b := fun h k => mul_pos h k
              have MN : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b := fun h k => mul_nonneg h k
              have DN : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → 0 ≤ a / b := fun h k => div_nonneg h k
              have DP : ∀ {a b : ℝ}, 0 < a → 0 < b → 0 < a / b := fun h k => div_pos h k
              have DI : ∀ {a b c : ℝ}, 0 < c → (a / c ≤ b ↔ a ≤ b * c) := fun h => div_le_iff₀ h
              have LD : ∀ {a b c : ℝ}, 0 < c → (a ≤ b / c ↔ a * c ≤ b) := fun h => le_div_iff₀ h
              have DD : ∀ {a b c d : ℝ}, 0 < b → 0 < d → (a / b ≤ c / d ↔ a * d ≤ c * b) := fun h k => div_le_div_iff₀ h k
              have DM : ∀ a b c : ℝ, a / b * c = a * c / b := fun a b c => div_mul_eq_mul_div a b c
              have DV : ∀ a b c : ℝ, a / b / c = a / (b * c) := fun a b c => div_div a b c
              have MC : ∀ {a b : ℝ}, b ≠ 0 → b * (a / b) = a := fun h => mul_div_cancel₀ _ h
              have NP : ∀ {n : ℕ} [n.AtLeastTwo], (0:ℝ) < OfNat.ofNat n := Nat.ofNat_pos
              have N0 : ∀ n : ℕ, (0:ℝ) ≤ (n : ℝ) := fun n => Nat.cast_nonneg n
              have O1 : ∀ a : ℝ, 1 * a = a := one_mul
              have TT : ∀ {a b : ℝ}, 0 < a → a ≤ b → 0 < b := fun h k => lt_of_lt_of_le h k
              have TE : ∀ {a b c : ℝ}, a ≤ b → b ≤ c → a ≤ c := fun h k => le_trans h k
              have KV : ∀ c L v : ℝ, 1 / c / L * v = v / (c * L) := by
                intro c L v
                rw [DV, DM, O1]
              have SQ : ∀ a L : ℝ, 0 < a → a * a ≤ L → 1 ≤ (1 / (4 * a))^2 * (16 * L) := by
                intro a L ha h
                have h4 : 0 < (4 * a) * (4 * a) := MP (MP NP ha) (MP NP ha)
                rw [div_pow, one_pow, sq, DM, O1]
                exact (LD h4).mpr (by linarith only [h])
              have h14 : (1:ℝ) ≤ 4 := Nat.one_le_ofNat
              have h464 : (4:ℝ) ≤ 64 := by norm_num
              have h48 : (4:ℝ) ≤ 8 := by norm_num
              have G1 : ∀ n ρ b f f' : ℝ, 1 ≤ n → n ≤ b → 4 ≤ ρ → f ≤ b → b * ρ - 1 < f' →
                  ρ * f / 2 ≤ f' - f ∧ ρ * n / 2 ≤ f' - f := by
                intro n ρ b f f' hn hb hρ h1 h2
                have hb0 : 0 ≤ b := zero_le_one.trans (hn.trans hb)
                have hρ0 : 0 ≤ ρ := zero_le_four.trans hρ
                have a0 := ML hρ hb0
                have a1 := ML h1 hρ0
                have a2 := ML hb hρ0
                exact ⟨by linarith only [a0, a1, hn, hb, h1, h2], by linarith only [a0, a2, hn, hb, h1, h2]⟩
              have C1 : ∀ ρ m M n D : ℝ, 0 < M → 0 ≤ ρ → m ≤ 4 * M * n → ρ * n / 2 ≤ D →
                  ρ * m / (128 * M) ≤ D / 16 := by
                intro ρ m M n D hM hρ hm hD
                refine (DI (MP NP hM)).mpr ?_
                linarith only [ML hm hρ, ML hD hM.le]
              have C2 : ∀ ρ m M f D : ℝ, 0 < M → 0 ≤ m → ρ * f / 2 ≤ D →
                  ρ * m / (128 * M) * (64 * M * f) ≤ m * D := by
                intro ρ m M f D hM hm hD
                refine (DM _ _ _).trans_le ((DI (MP NP hM)).mpr ?_)
                linarith only [ML hD (MN hM.le hm)]
              have C3 : ∀ ρ m M K f : ℝ, 0 < M → 0 < K → 0 ≤ ρ → 0 ≤ f → f * (M * K) ≤ m →
                  ρ * K / 512 * f ^ 2 ≤ ρ * m / (128 * M) * m / (4 * M * K) := by
                intro ρ m M K f hM hK hρ hf h
                have hMK := MP hM hK
                have h1 := mul_self_le_mul_self (MN hf hMK.le) h
                refine le_of_le_of_eq ((LD (MP (MP NP hM)
                  (MP (MP NP hM) hK))).mpr ?_) ((DV _ _ _).symm.trans (congrArg (· / (4 * M * K)) (DM _ _ _).symm))
                linarith only [ML h1 hρ]
              have D1 : ∀ ρ M D : ℝ, 1 ≤ M → 0 ≤ ρ → ρ ≤ D → ρ / (4096 * M) ≤ D / 16 := by
                intro ρ M D hM hρ hD
                refine (DI (MP NP (TT zero_lt_one hM))).mpr ?_
                linarith only [ML hM (hρ.trans hD), hD, hρ]
              have D2 : ∀ ρ M f D : ℝ, 1 ≤ M → ρ * f / 2 ≤ D → ρ / (4096 * M) * (2048 * M * f) ≤ D := by
                intro ρ M f D hM hD
                have hM0 : 0 < M := TT zero_lt_one hM
                refine (DM _ _ _).trans_le ((DI (MP NP hM0)).mpr ?_)
                linarith only [ML hD hM0.le]
              have FB : ∀ L v w F X : ℝ, 0 < L → 0 ≤ w → 1 ≤ F * (16 * L) → v ≤ 8 * w → w / 512 * F ≤ X →
                  1 / 10^6 / L * v ≤ X := by
                intro L v w F X hL hw hF hv h
                refine le_trans ?_ h
                refine (KV _ _ _).trans_le ((DI (MP (pow_pos NP _) hL)).mpr ?_)
                linarith only [ML hF hw, hv, hw]
              have FA : ∀ L z n M K X : ℝ, 0 < M → 0 < K → 0 ≤ z → M * M ≤ L →
                  z * K / 512 * (n / (3 * (M * K))) ^ 2 ≤ X → 1 / 10^8 / L * (n^2 / K * z) ≤ X := by
                intro L z n M K X hM hK hz hML h
                refine le_trans ?_ h
                have hMM := MP hM hM
                have e : z * K / 512 * (n / (3 * (M * K))) ^ 2 = (n^2 / K * z) * (1 / (4608 * (M * M))) := by
                  field_simp
                  ring
                rw [e, mul_comm, DV]
                refine ML ?_ (MN (DN (sq_nonneg n) hK.le) hz)
                exact div_le_div_of_nonneg_left zero_le_one (MP NP hMM) (by linarith only [hML, hMM])
              have FS : ∀ L z ρ M K X : ℝ, 0 < M → 0 < K → 0 ≤ z → M * M ≤ L → z / 2 ≤ ρ →
                  ρ / (4096 * M) / (64 * M * K) ≤ X → 1 / 10^8 / L * ((2:ℝ)^2 / K * z) ≤ X := by
                intro L z ρ M K X hM hK hz hML hρ h
                refine le_trans ?_ h
                have hMM := MP hM hM
                have hL : 0 < L := hMM.trans_le hML
                rw [DV, DV, DM, DM, O1, DV,
                  DD (MP hK (MP (pow_pos NP _) hL))
                    (MP (MP NP hM) (MP (MP NP hM) hK))]
                have hρ0 : 0 ≤ ρ := (DN hz two_pos.le).trans hρ
                have h1 := MR hρ (MN hK.le hMM.le)
                have h2 := ML hML (MN hK.le hρ0)
                have h3 : 0 ≤ ρ * K * L := MN (MN hρ0 hK.le) hL.le
                linarith only [h1, h2, h3]
              have FT : ∀ L K X v : ℝ, 1 ≤ L → 0 ≤ K → K / 384 ≤ X → v ≤ 64 * K → 1 / 10^6 / L * v ≤ X := by
                intro L K X v hL hK hX hv
                refine le_trans ?_ hX
                have hL0 : 0 < L := TT zero_lt_one hL
                refine (KV _ _ _).trans_le ((DI (MP (pow_pos NP _) hL0)).mpr ?_)
                linarith only [ML hL hK, hv, hK]
              have F0 : ∀ L K T X : ℝ, 1 ≤ L → 2 ≤ K → 0 ≤ T → T / 16 * (1 * (K - 1) - 0) / (4 * 1 * K) ≤ X →
                  1 / 10^8 / L * ((K + 1) / K * T) ≤ X := by
                intro L K T X hL hK hT h
                have hL0 : 0 < L := TT zero_lt_one hL
                have hK0 : 0 < K := TT two_pos hK
                refine le_trans ?_ h
                rw [DV, DM, DM, O1, DV,
                  DD (MP hK0 (MP (pow_pos NP _) hL0)) (MP (MP NP one_pos) hK0)]
                have h1 := ML hL (MN (MN hT hK0.le) (by linarith only [hK] : 0 ≤ K - 1))
                have h2 := ML hK (MN hT hK0.le)
                have h3 := MN hT hK0.le
                linarith only [h1, h2, h3]
              have P : ∀ c b T s : ℝ, 0 < b → 0 < T →
                  b ^ (c - 1 / s) * T ^ (1 / s) = b ^ c * Real.exp (Real.log (T / b) / s) := by
                intro c b T s hb hT
                rw [Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hT, ← Real.exp_add, ← Real.exp_add,
                  Real.log_div hT.ne' hb.ne']
                congr 1
                ring
              have Q1 : ∀ p a d : ℝ, 1 ≤ p → 0 ≤ d → a ≤ p * p → (a + d) / p ≤ a / (p + 1) + (1 + d) := by
                intro p a d hp hd ha
                have hp0 : 0 < p := TT zero_lt_one hp
                have hp1 : 0 < p + 1 := add_pos hp0 one_pos
                have ht : a / (p+1) * (p+1) = a := div_mul_cancel₀ _ hp1.ne'
                have ht2 : a / (p+1) ≤ p := by
                  rw [DI hp1]; linarith only [ha, hp]
                rw [DI hp0]
                generalize a / (p+1) = t at *
                linarith only [ht, ht2, ML hp hd]
              have Q2 : ∀ n K x z e : ℝ, 0 < n → n ≤ K → 0 ≤ x → e ≤ 3 → z ≤ x * (e * (K / n)) →
                  n ^ 2 / K * z ≤ 3 * (K * x) := by
                intro n K x z e hn hK hx he hz
                have hK0 : 0 < K := hn.trans_le hK
                have h1 := ML hz (DN (sq_nonneg n) hK0.le)
                have e1 : n^2 / K * (x * (e * (K / n))) = n * (x * e) := by field_simp
                rw [e1] at h1
                linarith only [h1, ML he (MN hn.le hx), MR hK hx]
              have R1 : ∀ g N M ℓ a : ℝ, 0 < g → M = g + N → 0 ≤ N → 4 ≤ ℓ → N * ℓ ≤ 2 * g → g * ℓ = a → ℓ - 2 ≤ a / M := by
                intro g N M ℓ a hg hM hN hℓ h1 h2
                rw [LD (hM ▸ add_pos_of_pos_of_nonneg hg hN), ← h2, hM]
                linarith only [h1, hN]
              have R2 : ∀ g N M ℓ S K : ℝ, 0 < g → M = g + N → 0 ≤ N → 4 ≤ ℓ → N * ℓ ≤ 2 * g → g ≤ N * ℓ → 2 ≤ K →
                  S ≤ (g - 1) * (K - 1) → 1 / (4 * ℓ) * (M * K) ≤ M * (K - 1) - S := by
                intro g N M ℓ S K hg hM hN hℓ h1 h2 hK hS
                have hℓ0 : 0 < ℓ := TT four_pos hℓ
                have hK0 : 0 ≤ K := two_pos.le.trans hK
                rw [DM, O1, DI (MP NP hℓ0), hM]
                have a1 : N * (K / 2) ≤ (g + N) * (K - 1) - S := by
                  linarith only [hS, ML hK hN, hK]
                have a2 := MR a1 (MP (zero_lt_four' ℝ) hℓ0).le
                have a3 := MR h2 hK0
                have a4 := ML hℓ hN
                have a5 := MR h1 hK0
                have a6 := MR a4 hK0
                refine le_trans ?_ a2
                linarith only [a3, a5, a6, hN, MN hN hK0]
              have R3 : ∀ x : ℝ, 0 < x → x / 8 ≤ Real.exp (Real.log x - 2) := by
                intro x hx
                rw [Real.exp_sub, Real.exp_log hx]
                apply div_le_div_of_nonneg_left hx.le (Real.exp_pos _)
                have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
                rw [h3]
                have h1 := (Real.exp_one_lt_d9).le.trans (by norm_num : (2.7182818286:ℝ) ≤ 2.8)
                exact (mul_self_le_mul_self (Real.exp_pos 1).le h1).trans (by norm_num)
              have E1 : ∀ (a : ℝ) (M : ℕ) , 0 < a → 0 < M → (Real.exp (Real.log a / M)) ^ M = a := by
                intro a M ha hM
                exact (Real.exp_nat_mul _ _).symm.trans ((congrArg Real.exp (MC (Nat.cast_pos.mpr hM).ne')).trans (Real.exp_log ha))
              refine ⟨1 / 10^8, by norm_num, ?_⟩
              intro K S T X hK hT hX0 hHC hHS
              have hK1 : (2:ℝ) ≤ K := Nat.ofNat_le_cast.mpr hK
              have hT1 : 2 * (K:ℝ) ≤ T := by
                have h := (Nat.cast_le (α := ℝ)).mpr hT
                rwa [Nat.cast_mul, Nat.cast_ofNat] at h
              have hT4 : (4:ℝ) ≤ T := by linarith only [hK1, hT1]
              have hKpos : (0:ℝ) < K := TT two_pos hK1
              have hTpos : (0:ℝ) < T := TT four_pos hT4
              have hlog2 : (0.69:ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
              have hL : (1:ℝ) ≤ Real.log T := by
                rw [Real.le_log_iff_exp_le hTpos]
                linarith only [Real.exp_one_lt_d9, hT4]
              generalize hLdef : Real.log T = L at hL ⊢
              have hL0 : 0 < L := TT zero_lt_one hL
              have hKm : ((K - 1 : ℕ):ℝ) = (K:ℝ) - 1 := by rw [Nat.cast_sub hK.le, Nat.cast_one]
              have hgrid : ∀ (n0 : ℕ) (ρ : ℝ) (j : ℕ), 1 ≤ n0 → 4 ≤ ρ →
                  (ρ * (⌊(n0:ℝ) * ρ^j⌋₊ : ℝ) / 2 ≤ (⌊(n0:ℝ) * ρ^(j+1)⌋₊ : ℝ) - (⌊(n0:ℝ) * ρ^j⌋₊ : ℝ)) ∧
                  (ρ * n0 / 2 ≤ (⌊(n0:ℝ) * ρ^(j+1)⌋₊ : ℝ) - (⌊(n0:ℝ) * ρ^j⌋₊ : ℝ)) := by
                intro n0 ρ j hn hρ
                have hn0 : (0:ℝ) ≤ n0 := N0 _
                have hρ0 : 0 ≤ ρ := zero_le_four.trans hρ
                refine G1 n0 ρ ((n0:ℝ) * ρ^j) _ _ (Nat.one_le_cast.mpr hn) ?_ hρ (Nat.floor_le (MN hn0 (pow_nonneg hρ0 j))) ?_
                · exact le_mul_of_one_le_right hn0 (one_le_pow₀ (h14.trans hρ))
                · rw [mul_assoc, ← pow_succ]; exact Nat.sub_one_lt_floor _
              have hstrict : ∀ (n0 : ℕ) (ρ : ℝ) (j : ℕ), 1 ≤ n0 → 4 ≤ ρ →
                  ⌊(n0:ℝ) * ρ^j⌋₊ < ⌊(n0:ℝ) * ρ^(j+1)⌋₊ := by
                intro n0 ρ j hn hρ
                have h := (hgrid n0 ρ j hn hρ).2
                have : (0:ℝ) < ρ * n0 := MP (TT four_pos hρ) (Nat.cast_pos.mpr hn)
                exact (Nat.cast_lt (α := ℝ)).mp (sub_pos.mp ((half_pos this).trans_le h))
              have hGEN : ∀ (M n0 : ℕ) (ρ f : ℝ), 0 < M → 1 ≤ n0 → 4 ≤ ρ → (n0:ℝ) * ρ^M ≤ T → S < M * (K-1) →
                  ((M : ℝ) * ((K : ℝ) - 1) - S) ≤ 4 * M * n0 → 0 ≤ f → f * (M * K) ≤ ((M : ℝ) * ((K : ℝ) - 1) - S) →
                  ρ * K / 512 * f ^ 2 ≤ X := by
                intro M n0 ρ f hM hn hρ hle hS hm hf hfm
                have hM' : (0:ℝ) < M := Nat.cast_pos.mpr hM
                have hρ0 : 0 ≤ ρ := zero_le_four.trans hρ
                have hm0 : 0 ≤ ((M : ℝ) * ((K : ℝ) - 1) - S) := (MN hf (MN hM'.le hKpos.le)).trans hfm
                refine (C3 ρ _ M K f hM' hKpos hρ0 hf hfm).trans ?_
                refine hHC M (fun j => ⌊(n0:ℝ) * ρ^j⌋₊) (ρ * ((M : ℝ) * ((K : ℝ) - 1) - S) / (128 * M)) hM
                  (fun j _ => hstrict n0 ρ j hn hρ) ?_ (DN (MN hρ0 hm0) (MN (Nat.ofNat_nonneg 128) hM'.le)) hS
                  (fun j _ => C1 ρ _ M n0 _ hM' hρ0 hm (hgrid n0 ρ j hn hρ).2)
                  (fun j _ => C2 ρ _ M _ _ hM' hm0 (hgrid n0 ρ j hn hρ).1)
                exact Nat.cast_le.mp (le_trans (Nat.floor_le (MN (N0 _) (pow_nonneg hρ0 _))) hle)
              have hSTK : ∀ (M : ℕ) (ρ : ℝ), 0 < M → 4 ≤ ρ → 4 * ρ^M ≤ T → S = M * (K-1) →
                  ρ / (4096 * M) / (64 * M * K) ≤ X := by
                intro M ρ hM hρ hle hS
                have hM' : (1:ℝ) ≤ M := Nat.one_le_cast.mpr hM
                have hρ0 : 0 ≤ ρ := zero_le_four.trans hρ
                have hpow : ρ ≤ ρ^M := le_self_pow₀ (h14.trans hρ) hM.ne'
                have hf : ∀ j : ℕ, (⌊((2:ℕ):ℝ) * ρ^j⌋₊ : ℝ) ≤ 2 * ρ^j := by
                  intro j
                  have := Nat.floor_le (MN (N0 2) (pow_nonneg hρ0 j))
                  rwa [Nat.cast_ofNat] at this ⊢
                have hTM : 2 * ρ^M ≤ (T:ℝ) - (⌊((2:ℕ):ℝ) * ρ^M⌋₊ : ℝ) := by linarith only [hf M, hle]
                have hsucc : ρ^M = ρ * ρ^(M-1) := by rw [← pow_succ', Nat.sub_add_cancel hM]
                refine hHS M (fun j => ⌊((2:ℕ):ℝ) * ρ^j⌋₊) (ρ / (4096 * M)) hM
                  (fun j _ => hstrict 2 ρ j one_le_two hρ) ?_
                  (DN hρ0 (MN (Nat.ofNat_nonneg 4096) (zero_le_one.trans hM'))) hS ?_
                  (fun j _ => D2 ρ M _ _ hM' (hgrid 2 ρ j one_le_two hρ).1) ?_ ?_
                · exact (Nat.cast_lt (α := ℝ)).mp (by
                    show (⌊((2:ℕ):ℝ) * ρ^M⌋₊ : ℝ) < T
                    linarith only [hTM, hpow, hρ])
                · intro j _
                  refine D1 ρ M _ hM' hρ0 ?_
                  have h := (hgrid 2 ρ j one_le_two hρ).2
                  rw [Nat.cast_ofNat, mul_div_assoc, div_self (two_ne_zero), mul_one] at h
                  rw [Nat.cast_ofNat]
                  exact h
                · exact D1 ρ M _ hM' hρ0 (by linarith only [hTM, hpow, hρ])
                · refine D2 ρ M _ _ hM' ?_
                  have h := ML (hf (M-1)) hρ0
                  rw [mul_left_comm, ← hsucc] at h
                  exact (half_le_self (MN hρ0 (N0 _))).trans (h.trans hTM)
              -- indices
              obtain ⟨q, hq⟩ : ∃ q, qIdx S K = q := ⟨_, rfl⟩
              have hSle : S ≤ (q+1) * (K-1) ∧ (S = 0 → q = 0) ∧ (S ≠ 0 → ∃ n : ℕ, 2 ≤ n ∧ n ≤ K ∧ S + n = (q+1) * (K-1) + 2) := by
                clear hHC hHS
                rw [← hq]
                unfold qIdx
                split_ifs with h
                · refine ⟨by omega, fun _ => rfl, fun h' => absurd h h'⟩
                · obtain ⟨d, rfl⟩ : ∃ d, K = d + 1 := ⟨K - 1, (Nat.sub_add_cancel hK.le).symm⟩
                  obtain ⟨s, rfl⟩ : ∃ s, S = s + 1 := Nat.exists_eq_succ_of_ne_zero h
                  rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
                  have h1 := Nat.div_add_mod s d
                  have h2 := Nat.mod_lt s (Nat.lt_of_succ_lt_succ hK)
                  have h3 : (s / d + 1) * d = d * (s / d) + d := by rw [Nat.add_mul, Nat.mul_comm, Nat.one_mul]
                  rw [h3]
                  generalize d * (s / d) = p at h1
                  generalize s % d = r at h1 h2
                  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_lt h2
                  clear hK hT hq hgrid hstrict hGEN hSTK h3 hKm h
                  refine ⟨by omega, fun h' => absurd h' (Nat.succ_ne_zero s), fun _ => ⟨e + 2, Nat.le_add_left 2 e, by omega, by omega⟩⟩
              obtain ⟨hSle, hq0, hnex⟩ := hSle
              have hSleR : (S:ℝ) ≤ ((q:ℝ)+1) * ((K:ℝ) - 1) := by
                have h1 : (S:ℝ) ≤ (((q+1) * (K-1) : ℕ) : ℝ) := Nat.cast_le.mpr hSle
                rwa [Nat.cast_mul, hKm, Nat.cast_add, Nat.cast_one] at h1
              have hSlt : ∀ M, q + 2 ≤ M → S < M * (K-1) := by
                intro M hM
                have h1 : (q+2) * (K-1) ≤ M * (K-1) := Nat.mul_le_mul_right _ hM
                have h3 : (q+2) * (K-1) = (q+1)*(K-1) + (K-1) := by ring
                have h4 : 0 < K - 1 := Nat.sub_pos_of_lt hK
                exact lt_of_le_of_lt hSle (lt_of_lt_of_le (by rw [h3]; exact Nat.lt_add_of_pos_right h4) h1)
              have hqn : (0:ℝ) ≤ q := N0 _
              have hq2 : (0:ℝ) < (q:ℝ) + 2 := add_pos_of_nonneg_of_pos hqn two_pos
              have hq1 : (1:ℝ) ≤ (q:ℝ) + 1 := le_add_of_nonneg_left hqn
              have hq1p : (0:ℝ) < (q:ℝ) + 1 := TT zero_lt_one hq1
              have hTK2 : (2:ℝ) ≤ T / K := by rw [LD hKpos]; exact hT1
              have hTKpos : (0:ℝ) < T / K := DP hTpos hKpos
              have hlogTK : Real.log (T / K) ≤ L := by
                rw [← hLdef]
                exact Real.log_le_log hTKpos (div_le_self hTpos.le (one_le_two.trans hK1))
              have hlogTK0 : 0 < Real.log (T / K) := Real.log_pos (one_lt_two.trans_le hTK2)
              obtain ⟨x, hxdef⟩ : ∃ x, Real.exp (Real.log (T / K) / ((q:ℝ)+2)) = x := ⟨_, rfl⟩
              have hlogx : Real.log x = Real.log (T / K) / ((q:ℝ)+2) := by rw [← hxdef, Real.log_exp]
              have hxpos : 0 < x := by rw [← hxdef]; exact Real.exp_pos _
              have hBeq : gapRateBLower K S T = K * x := by
                unfold gapRateBLower
                rw [hq, ← hxdef, P 1 K T _ hKpos hTpos, Real.rpow_one]
              have hBmain : 1 / 10^6 / L * (K * x) ≤ X := by
                by_cases hx : x ≤ 64
                · exact FT L K X _ hL hKpos.le hX0 (by rw [mul_comm]; exact MR hx hKpos.le)
                rw [not_le] at hx
                have hℓ : 4 ≤ Real.log x := by
                  have h1 : Real.log (2^6) ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith only [hx])
                  rw [Real.log_pow, Nat.cast_ofNat] at h1
                  linarith only [h1, hlog2]
                by_cases hqL : ((q:ℝ)+2) * ((q:ℝ)+2) ≤ L
                · have hxK : 0 ≤ x * K := MN hxpos.le hKpos.le
                  have hpow : x^(q+2) = T / K := by
                    have := E1 (T/K) (q+2) hTKpos (Nat.succ_pos _)
                    rwa [Nat.cast_add, Nat.cast_ofNat, hxdef] at this
                  refine FB L (K*x) (x * K) ((1/(4*((q:ℝ)+2)))^2) X hL0 hxK (SQ _ L hq2 hqL)
                    (by linarith only [hxK]) ?_
                  · have hMc : ((q+2:ℕ):ℝ) = (q:ℝ) + 2 := by rw [Nat.cast_add, Nat.cast_ofNat]
                    refine hGEN (q+2) K x _ (Nat.succ_pos _) hK.le (h464.trans hx.le) ?_ (hSlt _ le_rfl) ?_
                      (DN zero_le_one (MP NP hq2).le) ?_
                    · rw [hpow, MC hKpos.ne']
                    · rw [hMc]
                      linarith only [MP hq2 hKpos, hq2, N0 S]
                    · rw [hMc, DM, O1, DI (MP NP hq2)]
                      have h1 : (1:ℝ) * (K/4) ≤ ((q:ℝ) + 2) * ((K:ℝ) - 1) - S := by linarith only [hSleR, hK1]
                      linarith only [MR h1 hq2.le]
                · rw [not_le] at hqL
                  generalize hℓdef : Real.log x = ℓ at hℓ hlogx
                  have hℓpos : 0 < ℓ := TT four_pos hℓ
                  have hqℓ : ((q:ℝ)+2) * ℓ = Real.log (T/K) := by
                    rw [hlogx, MC hq2.ne']
                  have hℓq : ℓ ≤ (q:ℝ)+2 := by
                    by_contra hcon
                    rw [not_le] at hcon
                    linarith only [ML hcon.le hq2.le, hqL, hqℓ, hlogTK]
                  have hℓL : ℓ * ℓ ≤ L := by linarith only [MR hℓq hℓpos.le, hqℓ, hlogTK]
                  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈((q:ℝ)+2)/ℓ⌉₊ := ⟨_, rfl⟩
                  have hN1 : (q:ℝ)+2 ≤ N * ℓ := by rw [hN, ← DI hℓpos]; exact Nat.le_ceil _
                  have hN2 : N * ℓ ≤ 2 * ((q:ℝ)+2) := by
                    have h1 : (N:ℝ) < ((q:ℝ)+2)/ℓ + 1 := by
                      rw [hN]; exact Nat.ceil_lt_add_one (DN hq2.le hℓpos.le)
                    have h2 := MR h1.le hℓpos.le
                    rw [add_mul, div_mul_cancel₀ _ hℓpos.ne'] at h2
                    linarith only [h2, hℓq]
                  have hN0 : (0:ℝ) ≤ N := N0 _
                  have hMc : ((q+2+N:ℕ):ℝ) = (q:ℝ) + 2 + N := by rw [Nat.cast_add, Nat.cast_add, Nat.cast_ofNat]
                  have hMpos : 0 < q + 2 + N := Nat.add_pos_left (Nat.succ_pos _) _
                  have hpow := E1 (T/K) (q+2+N) hTKpos hMpos
                  have hρlow : x / 8 ≤ Real.exp (Real.log (T/K) / ((q+2+N:ℕ):ℝ)) := by
                    refine (R3 x hxpos).trans (Real.exp_le_exp.mpr ?_)
                    rw [hℓdef]
                    exact R1 ((q:ℝ)+2) N _ ℓ _ hq2 hMc hN0 hℓ hN2 hqℓ
                  generalize Real.exp (Real.log (T/K) / ((q+2+N:ℕ):ℝ)) = ρ at hpow hρlow
                  refine FB L (K*x) (ρ * K) ((1/(4*ℓ))^2) X hL0 (MN ((DP hxpos NP).le.trans hρlow) hKpos.le) (SQ ℓ L hℓpos hℓL)
                    (by linarith only [MR hρlow hKpos.le]) ?_
                  · refine hGEN (q+2+N) K ρ _ hMpos hK.le (by linarith only [hx, hρlow]) ?_ (hSlt _ (Nat.le_add_right _ _)) ?_
                      (DN zero_le_one (MP NP hℓpos).le) ?_
                    · rw [hpow, MC hKpos.ne']
                    · rw [hMc]
                      linarith only [MP hq2 hKpos, hq2, MN hN0 hKpos.le, hN0, N0 S]
                    · exact R2 ((q:ℝ)+2) N _ ℓ S K hq2 hMc hN0 hℓ hN2 hN1 hK1 (by linarith only [hSleR])
              have hBx : (0:ℝ) ≤ K * x := MN hKpos.le hxpos.le
              have hc : (1:ℝ) / 10^8 ≤ 1 / 10^6 := by norm_num
              have hcoef : ∀ v : ℝ, 0 ≤ v → 1 / 10^6 / L * v ≤ X → 1 / 10^8 / L * v ≤ X := by
                intro v hv h
                refine le_trans (MR ?_ hv) h
                exact div_le_div_of_nonneg_right hc hL0.le
              have hAeq : ∀ n : ℝ, (K:ℝ) - (rIdx S K : ℝ) = n → 0 < n →
                  gapRateA K S T = n^2 / K * Real.exp (Real.log (T / n) / ((q:ℝ)+1)) := by
                intro n hr hn
                unfold gapRateA
                rw [hr, hq, DM, P 2 n T _ hn hTpos, Real.rpow_two, DM]
              have hAfin : 1 / 10^8 / L * gapRateA K S T ≤ X := by
                by_cases hS0 : S = 0
                · have hn : (0:ℝ) < (K:ℝ) + 1 := add_pos hKpos one_pos
                  have hA := hAeq ((K:ℝ)+1) (by
                    unfold rIdx; rw [hq, hq0 hS0, hS0]; norm_num) hn
                  rw [hq0 hS0, Nat.cast_zero, zero_add, div_one, Real.exp_log (DP hTpos hn)] at hA
                  have e : ((K:ℝ)+1)^2 / K * (T / ((K:ℝ)+1)) = ((K:ℝ)+1) / K * T := by field_simp
                  rw [hA, e]
                  apply F0 L K T X hL hK1 hTpos.le
                  have key := hHC 1 (fun j => j * T) ((T:ℝ)/16) one_pos ?_ (by rw [one_mul]) (DN hTpos.le (Nat.ofNat_nonneg 16)) ?_ ?_ ?_
                  · rw [hS0] at key
                    rw [Nat.cast_one, Nat.cast_zero] at key
                    exact key
                  · intro j hj
                    rw [Nat.lt_one_iff.mp hj, zero_mul, zero_add, one_mul]
                    exact Nat.cast_pos.mp hTpos
                  · rw [hS0, one_mul]; exact Nat.sub_pos_of_lt hK
                  · intro j hj
                    rw [Nat.lt_one_iff.mp hj, zero_mul, zero_add, one_mul, Nat.cast_zero, sub_zero]
                  · intro j hj
                    rw [Nat.lt_one_iff.mp hj, zero_mul, zero_add, one_mul, Nat.cast_zero, sub_zero, mul_zero, mul_zero, hS0,
                      Nat.cast_one, Nat.cast_zero, O1, sub_zero]
                    exact MN (by linarith only [hK1]) hTpos.le
                -- S ≥ 1
                obtain ⟨n, hn2, hnK, hSn⟩ := hnex hS0
                have hSnR : (S:ℝ) + n = ((q:ℝ)+1) * ((K:ℝ)-1) + 2 := by
                  have h1 := congrArg (Nat.cast (R := ℝ)) hSn
                  rwa [Nat.cast_add, Nat.cast_add, Nat.cast_mul, hKm, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h1
                have hn2R : (2:ℝ) ≤ n := Nat.ofNat_le_cast.mpr hn2
                have hnKR : (n:ℝ) ≤ K := Nat.cast_le.mpr hnK
                have hnpos : (0:ℝ) < n := TT two_pos hn2R
                have hA := hAeq n (by
                  unfold rIdx
                  rw [hq]
                  push_cast
                  linarith only [hSnR]) hnpos
                have hTn : (2:ℝ) ≤ T / n := by rw [LD hnpos]; linarith only [hnKR, hT1]
                have hTnpos : (0:ℝ) < T / n := DP hTpos hnpos
                have hnn : (n:ℝ)^2 / K ≤ K := by
                  rw [DI hKpos, sq]; exact mul_self_le_mul_self hnpos.le hnKR
                have hnn0 : 0 ≤ (n:ℝ)^2 / K := DN (sq_nonneg _) hKpos.le
                by_cases hqL : ((q:ℝ)+1) * ((q:ℝ)+1) ≤ L
                · have hzpow := E1 (T/n) (q+1) hTnpos (Nat.succ_pos _)
                  have hMc : ((q+1:ℕ):ℝ) = (q:ℝ) + 1 := by rw [Nat.cast_add, Nat.cast_one]
                  rw [hMc] at hzpow
                  have hzpos : 0 < Real.exp (Real.log (T / n) / ((q:ℝ)+1)) := Real.exp_pos _
                  rw [hA]
                  generalize Real.exp (Real.log (T / n) / ((q:ℝ)+1)) = z at hzpow hzpos
                  clear hA hAeq hBmain hBeq
                  by_cases hz8 : z ≤ 8
                  · apply hcoef _ (MN hnn0 hzpos.le)
                    apply FT L K X _ hL hKpos.le hX0
                    linarith only [mul_le_mul hnn hz8 hzpos.le hKpos.le, hKpos]
                  rw [not_le] at hz8
                  by_cases hn3 : 3 ≤ n
                  · have hn3R : (3:ℝ) ≤ n := Nat.ofNat_le_cast.mpr hn3
                    have hm : (((q+1:ℕ):ℝ) * ((K:ℝ) - 1) - S) = n - 2 := by rw [hMc]; linarith only [hSnR]
                    apply FA L z n ((q:ℝ)+1) K X hq1p hKpos hzpos.le hqL
                    refine hGEN (q+1) n z _ (Nat.succ_pos _) (one_le_two.trans hn2) (h48.trans hz8.le) ?_
                      (lt_of_add_lt_add_right ((Nat.add_lt_add_left hn3 S).trans_eq hSn)) ?_
                      (DN hnpos.le (MP three_pos (MP hq1p hKpos)).le) ?_
                    · rw [hzpow, MC hnpos.ne']
                    · rw [hm, hMc]
                      linarith only [MR hq1 hnpos.le, hnpos]
                    · rw [hm, hMc, mul_comm (3:ℝ), ← DV, DM, div_mul_cancel₀ _ (MP hq1p hKpos).ne']
                      linarith only [hn3R]
                  · have hn : n = 2 := le_antisymm (Nat.le_of_lt_succ (not_le.mp hn3)) hn2
                    rw [hn] at hSn
                    rw [hn, Nat.cast_ofNat] at hzpow ⊢
                    have he2 : Real.exp (Real.log 2 / ((q:ℝ)+1)) ≤ 2 := by
                      exact (Real.exp_le_exp.mpr (div_le_self (Real.log_nonneg one_le_two) hq1)).trans_eq (Real.exp_log two_pos)
                    have he := E1 2 (q+1) two_pos (Nat.succ_pos _)
                    rw [hMc] at he
                    have hep : 0 < Real.exp (Real.log 2 / ((q:ℝ)+1)) := Real.exp_pos _
                    generalize Real.exp (Real.log 2 / ((q:ℝ)+1)) = e2 at he2 he hep
                    have hρz : z / 2 ≤ z / e2 := div_le_div_of_nonneg_left hzpos.le hep he2
                    apply FS L z (z/e2) ((q:ℝ)+1) K X hq1p hKpos hzpos.le hqL hρz
                    have h := hSTK (q+1) (z/e2) (Nat.succ_pos _) (by linarith only [hz8, hρz]) (by
                      rw [div_pow, hzpow, he]; linarith only) (Nat.add_right_cancel hSn)
                    rwa [hMc] at h
                · rw [not_le] at hqL
                  have hAB : gapRateA K S T ≤ 3 * (K * x) := by
                    rw [hA]
                    apply Q2 n K x _ (Real.exp 1) hnpos hnKR hxpos.le (by linarith only [Real.exp_one_lt_d9])
                    have hTn' : Real.log (T / n) = Real.log (T/K) + (Real.log K - Real.log n) := by
                      rw [Real.log_div hTpos.ne' hnpos.ne', Real.log_div hTpos.ne' hKpos.ne']; ring
                    have h1 := Q1 ((q:ℝ)+1) (Real.log (T/K)) (Real.log K - Real.log n) hq1
                      (sub_nonneg.mpr (Real.log_le_log hnpos hnKR)) (by linarith only [hlogTK, hqL])
                    rw [← hTn', add_assoc, one_add_one_eq_two] at h1
                    refine le_trans (Real.exp_le_exp.mpr h1) (le_of_eq ?_)
                    rw [Real.exp_add, Real.exp_add, Real.exp_sub, Real.exp_log hKpos, Real.exp_log hnpos, hxdef]
                  refine le_trans (ML hAB (DN (DN zero_le_one (pow_nonneg (Nat.ofNat_nonneg 10) 8)) hL0.le)) ?_
                  have h3 : 1 / 10^8 / L * (3 * (K * x)) = (3/100) * (1 / 10^6 / L * (K * x)) := by ring
                  rw [h3]
                  have hX : 0 ≤ X := (DN hKpos.le (Nat.ofNat_nonneg 384)).trans hX0
                  linarith only [hBmain, hX]
              rcases max_choice (gapRateA K S T) (gapRateBLower K S T) with h | h <;> rw [h]
              · exact hAfin
              · rw [hBeq]
                exact hcoef _ hBx hBmain
            have COMB :
                ∀ (K T S : ℕ) (ω : Fin T → Fin K × Bool) (M : ℕ) (τ : ℕ → ℕ), 0 < K → (∀ j < M, τ j < τ (j+1)) → τ M ≤ T →
              switchCost (fun t => ((ω t).1, if (ω t).2 then (1:ℝ) else -1) : BanditHistory K T) 1 T ≤ S →
              M * (K - 1) ≤ S + ∑ j ∈ Finset.range M, (Finset.univ.filter (fun k : Fin K => ∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → (ω t).1 ≠ k)).card := by
              clear FIN
              classical
              intro K T S ω M τ hK0 hτ hτM hS
              classical
              obtain ⟨a, ha⟩ : ∃ a : ℕ → Fin K, ∀ t : Fin T, a t = (ω t).1 :=
                ⟨fun s => if h : s < T then (ω ⟨s, h⟩).1 else ⟨0, hK0⟩, fun t => by simp [t.2]⟩
              obtain ⟨n, hn⟩ : ∃ n : ℕ → ℕ → ℕ, ∀ u v, n u v =
                  ((Finset.Ico u v).filter (fun s => a s ≠ a (s+1))).card := ⟨_, fun _ _ => rfl⟩
              have hadd : ∀ u v w, u ≤ v → v ≤ w → n u v + n v w = n u w := by
                intro u v w h1 h2
                rw [hn, hn, hn, ← Finset.Ico_union_Ico_eq_Ico h1 h2, Finset.filter_union,
                  Finset.card_union_of_disjoint]
                exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive u v w)
              have hone : ∀ u, n u (u+1) = if a u ≠ a (u+1) then 1 else 0 := by
                intro u
                rw [hn, Nat.Ico_succ_singleton, Finset.filter_singleton]
                split_ifs <;> simp
              have himg : ∀ u m, ((Finset.Ico u (u+1+m)).image a).card ≤ 1 + n u (u+m) := by
                intro u m
                induction m with
                | zero => simp [Nat.Ico_succ_singleton]
                | succ m ih =>
                  have e1 : u + 1 + (m+1) = (u+1+m)+1 := by ring
                  have e2 : u + (m+1) = (u+m)+1 := by ring
                  rw [e1, e2, ← hadd u (u+m) (u+m+1) (by omega) (by omega), hone]
                  have hI : Finset.Ico u (u+1+m+1) = insert (u+1+m) (Finset.Ico u (u+1+m)) := by
                    ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
                  rw [hI, Finset.image_insert]
                  split_ifs with h
                  · have := Finset.card_insert_le (a (u+1+m)) ((Finset.Ico u (u+1+m)).image a)
                    omega
                  · have hm : a (u+1+m) ∈ (Finset.Ico u (u+1+m)).image a := by
                      rw [Finset.mem_image]
                      refine ⟨u+m, by rw [Finset.mem_Ico]; omega, ?_⟩
                      have e3 : u+1+m = u+m+1 := by ring
                      rw [e3]; exact not_not.mp h
                    rw [Finset.insert_eq_of_mem hm]; omega
              have himg' : ∀ u v, u < v → ((Finset.Ico u v).image a).card ≤ 1 + n u (v-1) := by
                intro u v h
                have := himg u (v-1-u)
                have e1 : u+1+(v-1-u) = v := by omega
                have e2 : u+(v-1-u) = v-1 := by omega
                rwa [e1, e2] at this
              have htot : n 0 (T-1) ≤ S := by
                refine le_trans ?_ hS
                rw [hn]
                unfold switchCost
                apply Finset.card_le_card_of_injOn (fun s => s+1)
                · intro s hs
                  simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_setOf_eq] at hs
                  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
                  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
                  have h1 : s < T := by omega
                  have h2 : s + 1 < T := by omega
                  have e1 := ha ⟨s, h1⟩
                  have e2 := ha ⟨s+1, h2⟩
                  have c1 : 1 ≤ s + 1 ∧ s + 1 ≤ T := by omega
                  have c2 : 1 ≤ s + 1 + 1 ∧ s + 1 + 1 ≤ T := by omega
                  unfold act actA actions
                  rw [dif_pos c1, dif_pos c2]
                  intro h
                  have h' := Option.some.inj h
                  apply hs.2
                  simp only at e1 e2
                  rw [e1, e2]
                  exact h'
                · intro x _ y _ h
                  simpa using h
              have hτle : ∀ j, j ≤ M → τ j ≤ τ M := by
                intro j hj
                have key : ∀ d, j + d ≤ M → τ j ≤ τ (j+d) := by
                  intro d
                  induction d with
                  | zero => intro _; exact le_rfl
                  | succ d ih => intro h; exact (ih (by omega)).trans (hτ (j+d) (by omega)).le
                have := key (M-j) (by omega)
                rwa [show j + (M-j) = M by omega] at this
              have hmiss : ∀ j, j < M → (Finset.univ.filter (fun k : Fin K => ∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → (ω t).1 ≠ k)).card + ((Finset.Ico (τ j) (τ (j+1))).image a).card = K := by
                intro j hj
                have hle := hτle (j+1) hj
                have : (Finset.univ.filter (fun k : Fin K => ∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → (ω t).1 ≠ k)) = ((Finset.Ico (τ j) (τ (j+1))).image a)ᶜ := by
                  ext k
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, Finset.mem_image,
                    Finset.mem_Ico, not_exists, not_and, and_imp]
                  constructor
                  · intro h s h1 h2 h3
                    have hs : s < T := by omega
                    exact h ⟨s, hs⟩ h1 h2 (by rw [← ha]; exact h3)
                  · intro h t h1 h2 h3
                    exact h t h1 h2 (by rw [ha]; exact h3)
                rw [this, Finset.card_compl, Fintype.card_fin]
                have := Finset.card_le_univ ((Finset.Ico (τ j) (τ (j+1))).image a)
                rw [Fintype.card_fin] at this
                omega
              have hsum : ∀ m, m ≤ M → ∑ j ∈ Finset.range m, n (τ j) (τ (j+1) - 1) ≤ n 0 (τ m - 1) := by
                intro m
                induction m with
                | zero => intro _; simp
                | succ m ih =>
                  intro hm
                  rw [Finset.sum_range_succ]
                  have h1 := ih (by omega)
                  have h2 := hτ m (by omega)
                  have h3 := hadd 0 (τ m - 1) (τ m) (by omega) (by omega)
                  have h4 := hadd 0 (τ m) (τ (m+1) - 1) (by omega) (by omega)
                  omega
              have hj : ∀ j ∈ Finset.range M, K - 1 ≤ n (τ j) (τ (j+1) - 1) + (Finset.univ.filter (fun k : Fin K => ∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → (ω t).1 ≠ k)).card := by
                intro j hj
                have hj' := Finset.mem_range.mp hj
                have h1 := hmiss j hj'
                have h2 := himg' (τ j) (τ (j+1)) (hτ j hj')
                omega
              have h1 := Finset.sum_le_sum hj
              rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Finset.sum_add_distrib] at h1
              have h2 := hsum M le_rfl
              have h3 := hadd 0 (τ M - 1) (T-1) (by omega) (by omega)
              omega
            have STUCKCOMB :
                ∀ (K T : ℕ) (ω : Fin T → Fin K × Bool) (M : ℕ) (τ : ℕ → ℕ), 1 < K → 0 < M → (∀ j < M, τ j < τ (j+1)) → τ M < T →
              switchCost (fun t => ((ω t).1, if (ω t).2 then (1:ℝ) else -1) : BanditHistory K T) 1 T ≤ M * (K - 1) →
              (∃ j < M, ∃ k : Fin K, ∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → (ω t).1 ≠ k) ∨
              ∃ l : Fin K, (∀ t : Fin T, τ M ≤ (t:ℕ) → (ω t).1 = l) ∧
                ∃ v, v ≤ τ M ∧ (∀ t : Fin T, τ (M-1) ≤ (t:ℕ) → (t:ℕ) < v → (ω t).1 ≠ l) ∧
                  ∀ i, i ≠ l → ∃ t : Fin T, τ (M-1) ≤ (t:ℕ) ∧ (t:ℕ) < v ∧ (ω t).1 = i := by
              clear FIN COMB
              classical
              intro K T ω M τ hK1 hM hτ hτM hS
              have hK0 : 0 < K := by omega
              classical
              obtain ⟨a, ha⟩ : ∃ a : ℕ → Fin K, ∀ t : Fin T, a t = (ω t).1 :=
                ⟨fun s => if h : s < T then (ω ⟨s, h⟩).1 else ⟨0, hK0⟩, fun t => by simp [t.2]⟩
              obtain ⟨n, hn⟩ : ∃ n : ℕ → ℕ → ℕ, ∀ u v, n u v =
                  ((Finset.Ico u v).filter (fun s => a s ≠ a (s+1))).card := ⟨_, fun _ _ => rfl⟩
              have hadd : ∀ u v w, u ≤ v → v ≤ w → n u v + n v w = n u w := by
                intro u v w h1 h2
                rw [hn, hn, hn, ← Finset.Ico_union_Ico_eq_Ico h1 h2, Finset.filter_union,
                  Finset.card_union_of_disjoint]
                exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive u v w)
              have hone : ∀ u, n u (u+1) = if a u ≠ a (u+1) then 1 else 0 := by
                intro u
                rw [hn, Nat.Ico_succ_singleton, Finset.filter_singleton]
                split_ifs <;> simp
              have himg : ∀ u m, ((Finset.Ico u (u+1+m)).image a).card ≤ 1 + n u (u+m) := by
                intro u m
                induction m with
                | zero => exact (Finset.card_image_le.trans (by rw [Nat.card_Ico, Nat.add_zero, Nat.add_sub_cancel_left])).trans (Nat.le_add_right _ _)
                | succ m ih =>
                  have e1 : u + 1 + (m+1) = (u+1+m)+1 := by ring
                  have e2 : u + (m+1) = (u+m)+1 := by ring
                  rw [e1, e2, ← hadd u (u+m) (u+m+1) (Nat.le_add_right _ _) (Nat.le_succ _), hone]
                  have hI : Finset.Ico u (u+1+m+1) = insert (u+1+m) (Finset.Ico u (u+1+m)) := by
                    rw [← Finset.insert_Ico_right_eq_Ico_add_one ((Nat.le_add_right u 1).trans (Nat.le_add_right _ m))]
                  rw [hI, Finset.image_insert]
                  split_ifs with h
                  · have := Finset.card_insert_le (a (u+1+m)) ((Finset.Ico u (u+1+m)).image a)
                    omega
                  · have hm : a (u+1+m) ∈ (Finset.Ico u (u+1+m)).image a := by
                      rw [Finset.mem_image]
                      refine ⟨u+m, by rw [Finset.mem_Ico]; omega, ?_⟩
                      have e3 : u+1+m = u+m+1 := by ring
                      rw [e3]; exact not_not.mp h
                    rw [Finset.insert_eq_of_mem hm]; omega
              have himg' : ∀ u v, u < v → ((Finset.Ico u v).image a).card ≤ 1 + n u (v-1) := by
                intro u v h
                have := himg u (v-1-u)
                have e2 : u+(v-1-u) = v-1 := Nat.add_sub_cancel' (Nat.le_sub_one_of_lt h)
                have e1 : u+1+(v-1-u) = v := by rw [Nat.add_right_comm, e2, Nat.sub_add_cancel (Nat.one_le_of_lt h)]
                rwa [e1, e2] at this
              have htot : n 0 (T-1) ≤ M * (K-1) := by
                refine le_trans ?_ hS
                rw [hn]
                unfold switchCost
                apply Finset.card_le_card_of_injOn (fun s => s+1)
                · intro s hs
                  simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_setOf_eq] at hs
                  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
                  have h2 : s + 1 < T := Nat.add_lt_of_lt_sub hs.1.2
                  have h1 : s < T := Nat.lt_of_succ_lt h2
                  refine ⟨Nat.lt_succ_of_le h1, Nat.le_add_left 1 s, h2, Nat.le_add_left 1 s, h2, ?_⟩
                  have e1 := ha ⟨s, h1⟩
                  have e2 := ha ⟨s+1, h2⟩
                  have c1 : 1 ≤ s + 1 ∧ s + 1 ≤ T := ⟨Nat.le_add_left 1 s, h1⟩
                  have c2 : 1 ≤ s + 1 + 1 ∧ s + 1 + 1 ≤ T := ⟨Nat.le_add_left 1 _, h2⟩
                  unfold act actA actions
                  rw [dif_pos c1, dif_pos c2]
                  intro h
                  have h' := Option.some.inj h
                  apply hs.2
                  simp only at e1 e2
                  rw [e1, e2]
                  exact h'
                · intro x _ y _ h
                  exact Nat.succ.inj h
              have hτle : ∀ j, j ≤ M → τ j ≤ τ M := by
                intro j hj
                have key : ∀ d, j + d ≤ M → τ j ≤ τ (j+d) := by
                  intro d
                  induction d with
                  | zero => intro _; exact le_rfl
                  | succ d ih => intro h; exact (ih (Nat.le_of_succ_le h)).trans (hτ (j+d) h).le
                have := key (M-j) (Nat.add_sub_cancel' hj).le
                rwa [Nat.add_sub_cancel' hj] at this
              have hsum : ∀ m, m ≤ M → ∑ j ∈ Finset.range m, n (τ j) (τ (j+1) - 1) ≤ n 0 (τ m - 1) := by
                intro m
                induction m with
                | zero => intro _; simp
                | succ m ih =>
                  intro hm
                  rw [Finset.sum_range_succ]
                  have h1 := ih (Nat.le_of_succ_le hm)
                  have h2 := hτ m hm
                  have h3 := hadd 0 (τ m - 1) (τ m) (Nat.zero_le _) (Nat.sub_le _ _)
                  have h4 := hadd 0 (τ m) (τ (m+1) - 1) (Nat.zero_le _) (Nat.le_sub_one_of_lt h2)
                  rw [← h4, ← h3]
                  exact Nat.add_le_add_right (h1.trans (Nat.le_add_right _ _)) _
              by_cases hm : ∃ j < M, ∃ k : Fin K, ∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → (ω t).1 ≠ k
              · exact Or.inl hm
              right
              have hfull : ∀ j, j < M → (Finset.Ico (τ j) (τ (j+1))).image a = Finset.univ := by
                intro j hj
                have hle := hτle (j+1) hj
                ext k
                simp only [Finset.mem_univ, iff_true, Finset.mem_image, Finset.mem_Ico]
                by_contra hcon
                apply hm
                refine ⟨j, hj, k, fun t h1 h2 h3 => hcon ⟨t, ⟨h1, h2⟩, ?_⟩⟩
                rw [ha]; exact h3
              have hj : ∀ j ∈ Finset.range (M-1), K - 1 ≤ n (τ j) (τ (j+1) - 1) := by
                intro j hj
                have hj' : j < M := by exact Nat.lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.sub_le _ _)
                have h2 := himg' (τ j) (τ (j+1)) (hτ j hj')
                rw [hfull j hj', Finset.card_univ, Fintype.card_fin] at h2
                omega
              have h1 := Finset.sum_le_sum hj
              rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at h1
              have h2 := hsum (M-1) (Nat.sub_le _ _)
              have hM1 : M - 1 + 1 = M := Nat.sub_add_cancel hM
              have hlast : τ (M-1) < τ M := by have := hτ (M-1) (Nat.sub_lt hM Nat.one_pos); rwa [hM1] at this
              have hfl : (Finset.Ico (τ (M-1)) (τ M)).image a = Finset.univ := by
                have := hfull (M-1) (Nat.sub_lt hM Nat.one_pos); rwa [hM1] at this
              obtain ⟨u, hu⟩ : ∃ u, u = τ (M-1) := ⟨_, rfl⟩
              rw [← hu] at hlast hfl h2 ⊢
              have hMK : M * (K-1) = (M-1)*(K-1) + (K-1) := by
                conv_lhs => rw [← hM1]
                rw [Nat.add_mul, Nat.one_mul]
              have hT1 : τ M ≤ T - 1 := Nat.le_sub_one_of_lt hτM
              have h3 := hadd 0 (u-1) u (Nat.zero_le _) (Nat.sub_le _ _)
              have h4 := hadd 0 u (T-1) (Nat.zero_le _) (hlast.le.trans hT1)
              have hbud : n u (T-1) ≤ K - 1 := by
                rw [← h4, ← h3, hMK] at htot
                have h5 := (Nat.add_le_add_right (h1.trans (h2.trans (Nat.le_add_right _ (n (u-1) u)))) (n u (T-1))).trans htot
                exact Nat.le_of_add_le_add_left h5
              clear h1 h2 h3 h4 hMK htot hS hM1
              have hM1' : τ M - 1 + 1 = τ M := Nat.sub_add_cancel (Nat.one_le_of_lt hlast)
              have hex : ∃ v, (Finset.Ico u (v+1)).image a = Finset.univ := by
                refine ⟨τ M - 1, ?_⟩
                rw [hM1']; exact hfl
              obtain ⟨v, hv⟩ : ∃ v, v = Nat.find hex := ⟨_, rfl⟩
              have hv1 : (Finset.Ico u (v+1)).image a = Finset.univ := by rw [hv]; exact Nat.find_spec hex
              have hv2 : ∀ w < v, (Finset.Ico u (w+1)).image a ≠ Finset.univ := by
                intro w hw; rw [hv] at hw; exact Nat.find_min hex hw
              have hvM : v ≤ τ M - 1 := by
                rw [hv]; apply Nat.find_min' hex
                rw [hM1']; exact hfl
              have hcardu : ∀ s : Finset (Fin K), s = Finset.univ → s.card = K := by
                intro s hs; rw [hs, Finset.card_univ, Fintype.card_fin]
              have huv : u < v := by
                by_contra hcon
                have hc := hcardu _ hv1
                have hsub : (Finset.Ico u (v+1)) ⊆ {u} := by
                  intro x hx; rw [Finset.mem_Ico] at hx; rw [Finset.mem_singleton]
                  exact le_antisymm ((Nat.le_of_lt_succ hx.2).trans (Nat.le_of_not_lt hcon)) hx.1
                have h5 := (Finset.card_image_le (s := Finset.Ico u (v+1)) (f := a)).trans (Finset.card_le_card hsub)
                rw [Finset.card_singleton, hc] at h5
                exact Nat.not_le_of_lt hK1 h5
              have hv1' : v - 1 + 1 = v := Nat.sub_add_cancel (Nat.one_le_of_lt huv)
              have huv1 : u ≤ v - 1 := Nat.le_sub_one_of_lt huv
              have hvT : v ≤ T - 1 := hvM.trans ((Nat.sub_le _ _).trans hT1)
              have hvlt : v < τ M := Nat.lt_of_le_of_lt hvM (Nat.sub_lt (Nat.one_le_of_lt hlast) Nat.one_pos)
              have hprev : (Finset.Ico u v).image a ≠ Finset.univ := by
                have := hv2 (v-1) (Nat.sub_lt (Nat.one_le_of_lt huv) Nat.one_pos)
                rwa [hv1'] at this
              have hI : Finset.Ico u (v+1) = insert v (Finset.Ico u v) :=
                (Finset.insert_Ico_right_eq_Ico_add_one huv.le).symm
              rw [hI, Finset.image_insert] at hv1
              have hnot : a v ∉ (Finset.Ico u v).image a := by
                intro h
                rw [Finset.insert_eq_of_mem h] at hv1
                exact hprev hv1
              have hc := hcardu _ hv1
              rw [Finset.card_insert_of_notMem hnot] at hc
              have h5 := himg' u v huv
              have h6 := hadd u (v-1) v huv1 (Nat.sub_le _ _)
              have h7 := hadd u v (T-1) huv.le hvT
              have h8 := hone (v-1)
              rw [hv1'] at h8
              rw [if_pos] at h8
              swap
              · intro h
                apply hnot
                rw [Finset.mem_image]
                exact ⟨v-1, Finset.mem_Ico.mpr ⟨huv1, Nat.sub_lt (Nat.one_le_of_lt huv) Nat.one_pos⟩, h⟩
              have h9 : n v (T-1) = 0 := by
                clear hvM hvT huv1 hv1' hvlt hM1' hT1 hlast hτM huv hK0 hM
                omega
              rw [hn, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h9
              have hconst : ∀ m, v + m < T → a (v+m) = a v := by
                intro m
                induction m with
                | zero => intro _; rfl
                | succ m ih =>
                  intro h
                  have h10 := @h9 (v+m) (Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, Nat.lt_sub_of_add_lt h⟩)
                  rw [not_not] at h10
                  rw [show v + (m+1) = v+m+1 from rfl, ← h10]
                  exact ih (Nat.lt_of_succ_lt h)
              refine ⟨a v, ?_, v, hvlt.le, ?_, ?_⟩
              · intro t ht
                rw [← ha]
                have e : v + ((t:ℕ) - v) = t := Nat.add_sub_cancel' (hvlt.le.trans ht)
                have := hconst ((t:ℕ) - v) (by rw [e]; exact t.2)
                rwa [e] at this
              · intro t h1 h2 h3
                apply hnot
                rw [Finset.mem_image]
                exact ⟨t, Finset.mem_Ico.mpr ⟨h1, h2⟩, by rw [ha]; exact h3⟩
              · intro i hi
                have : i ∈ insert (a v) ((Finset.Ico u v).image a) := by rw [hv1]; exact Finset.mem_univ _
                rw [Finset.mem_insert] at this
                rcases this with h | h
                · exact absurd h hi
                · rw [Finset.mem_image] at h
                  obtain ⟨s, hs, hs'⟩ := h
                  rw [Finset.mem_Ico] at hs
                  have hsT : s < T := hs.2.trans (hvlt.trans hτM)
                  refine ⟨⟨s, hsT⟩, hs.1, hs.2, ?_⟩
                  rw [← ha]; exact hs'
            have BRIDGE :
                ∀ (K : ℕ) (π : BanditPolicy K), ∃ p : (n : ℕ) → (Fin n → Fin K × Bool) → Fin K → ℝ,
              (∀ n ω a, 0 ≤ p n ω a) ∧ (∀ n ω, ∑ a, p n ω a = 1) ∧
              ∀ μ : Fin K → ℝ, (∀ i, |μ i| ≤ 1/2) → ∃ ν : StochasticBandit K, AdmissibleEnvironment ν ∧
                (∀ i, banditArmMean ν i = μ i) ∧
                ∀ n, banditMeasure ν π n = ∑ ω : Fin n → Fin K × Bool,
                  ENNReal.ofReal (∏ t : Fin n, (p t (fun i => ω ⟨i, i.2.trans t.2⟩) (ω t).1 *
                    ((1 + μ (ω t).1 * (if (ω t).2 then (1:ℝ) else -1)) / 2))) •
                  Measure.dirac (fun t => ((ω t).1, if (ω t).2 then (1:ℝ) else -1) : BanditHistory K n) := by
              clear FIN COMB STUCKCOMB
              classical
              intro K π
              refine ⟨fun n ω a => ((π.select n (fun t => ((ω t).1, if (ω t).2 then (1:ℝ) else -1))) {a}).toReal,
                fun n ω a => ENNReal.toReal_nonneg, ?_, ?_⟩
              · intro n ω
                have h1 : ∑ a, (π.select n (fun t => ((ω t).1, if (ω t).2 then (1:ℝ) else -1))) {a} = 1 := by
                  rw [MeasureTheory.sum_measure_singleton, Finset.coe_univ, measure_univ]
                rw [← ENNReal.toReal_sum (fun a _ => measure_ne_top _ _), h1]
                exact ENNReal.toReal_one
              · intro μ hμ
                have hlo : ∀ i, 0 ≤ 1 + μ i := fun i =>
                  neg_le_iff_add_nonneg'.mp ((neg_le_neg one_half_lt_one.le).trans (abs_le.mp (hμ i)).1)
                have hhi : ∀ i, 0 ≤ 1 - μ i := fun i => sub_nonneg.mpr ((abs_le.mp (hμ i)).2.trans one_half_lt_one.le)
                have hlo2 : ∀ i, 0 ≤ (1 + μ i)/2 := fun i => div_nonneg (hlo i) zero_le_two
                have hhi2 : ∀ i, 0 ≤ (1 - μ i)/2 := fun i => div_nonneg (hhi i) zero_le_two
                have hsum : ∀ i, ENNReal.ofReal ((1 + μ i)/2) + ENNReal.ofReal ((1 - μ i)/2) = 1 := by
                  intro i
                  rw [← ENNReal.ofReal_add (hlo2 i) (hhi2 i), ← add_div, add_add_sub_cancel, one_add_one_eq_two,
                    div_self two_ne_zero, ENNReal.ofReal_one]
                let ν : StochasticBandit K :=
                  { P := fun i => ENNReal.ofReal ((1 + μ i)/2) • Measure.dirac (1:ℝ) +
                      ENNReal.ofReal ((1 - μ i)/2) • Measure.dirac (-1:ℝ)
                    prob := fun i => ⟨by rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one, hsum i]⟩ }
                have hid : ∀ (c x : ℝ) (f : ℝ → ℝ), Integrable f (ENNReal.ofReal c • Measure.dirac x) := fun c x f =>
                  (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
                have hint : ∀ i (f : ℝ → ℝ), Integrable f (ν.P i) := fun i f =>
                  (hid _ _ f).add_measure (hid _ _ f)
                have hmean : ∀ i, banditArmMean ν i = μ i := by
                  intro i
                  change ∫ x, x ∂(ENNReal.ofReal ((1 + μ i)/2) • Measure.dirac (1:ℝ) +
                      ENNReal.ofReal ((1 - μ i)/2) • Measure.dirac (-1:ℝ)) = μ i
                  rw [integral_add_measure (hid _ _ _) (hid _ _ _), integral_smul_measure, integral_smul_measure,
                    integral_dirac, integral_dirac, ENNReal.toReal_ofReal (hlo2 i),
                    ENNReal.toReal_ofReal (hhi2 i)]
                  simp only [smul_eq_mul]
                  ring
                have hlint : ∀ i (g : ℝ → ENNReal), ∫⁻ x, g x ∂(ν.P i) =
                    ∑ b : Bool, ENNReal.ofReal ((1 + μ i * (if b then (1:ℝ) else -1))/2) * g (if b then (1:ℝ) else -1) := by
                  intro i g
                  change ∫⁻ x, g x ∂(ENNReal.ofReal ((1 + μ i)/2) • Measure.dirac (1:ℝ) +
                      ENNReal.ofReal ((1 - μ i)/2) • Measure.dirac (-1:ℝ)) = _
                  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
                    lintegral_dirac, lintegral_dirac]
                  rw [Fintype.sum_bool, if_pos (rfl : true = true), if_neg Bool.false_ne_true, mul_one, mul_neg_one,
                    ← sub_eq_add_neg]
                  rfl
                refine ⟨ν, ⟨⟨fun i => hint i id, ?_⟩, ?_⟩, hmean, ?_⟩
                · intro i
                  have hae : ∀ᵐ x ∂(ν.P i), x ∈ Set.Icc (-1:ℝ) 1 := by
                    change ∀ᵐ x ∂(ENNReal.ofReal ((1 + μ i)/2) • Measure.dirac (1:ℝ) +
                      ENNReal.ofReal ((1 - μ i)/2) • Measure.dirac (-1:ℝ)), x ∈ Set.Icc (-1:ℝ) 1
                    rw [ae_add_measure_iff]
                    have h11 : (-1:ℝ) ≤ 1 := neg_le_self zero_le_one
                    exact ⟨Measure.ae_smul_measure ((ae_dirac_iff measurableSet_Icc).mpr ⟨h11, le_rfl⟩) _,
                      Measure.ae_smul_measure ((ae_dirac_iff measurableSet_Icc).mpr ⟨le_rfl, h11⟩) _⟩
                  have : IsProbabilityMeasure (ν.P i) := ν.prob i
                  have h := hasSubgaussianMGF_of_mem_Icc (μ := ν.P i) (X := fun x : ℝ => x)
                    measurable_id.aemeasurable hae
                  have e : ((‖(1:ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal) = 1 ^ 2 := by
                    congr 1
                    ext
                    simp only [NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs]
                    norm_num
                  rw [e] at h
                  exact h
                · intro i j
                  rw [hmean, hmean]
                  exact (norm_sub_le (μ i) (μ j)).trans ((add_le_add (hμ i) (hμ j)).trans_eq (add_halves 1))
                · -- the measure identity
                  have hstep : ∀ (n : ℕ) (h : BanditHistory K n) (g : Fin K × ℝ → ENNReal), Measurable g →
                      ∫⁻ ab, g ab ∂(banditStepKernel ν π n h) =
                        ∑ ab : Fin K × Bool, (π.select n h {ab.1} *
                          ENNReal.ofReal ((1 + μ ab.1 * (if ab.2 then (1:ℝ) else -1))/2)) *
                          g (ab.1, if ab.2 then (1:ℝ) else -1) := by
                    intro n h g hg
                    rw [banditStepKernel, Kernel.lintegral_compProd _ _ _ hg]
                    have : ∀ a : Fin K, ∫⁻ x, g (a, x) ∂((Kernel.comap (mγ := (inferInstance : MeasurableSpace (BanditHistory K n × Fin K))) (banditRewardKernel ν) (Prod.snd : BanditHistory K n × Fin K → Fin K) measurable_snd) (h, a)) =
                        ∑ b : Bool, ENNReal.ofReal ((1 + μ a * (if b then (1:ℝ) else -1))/2) *
                          g (a, if b then (1:ℝ) else -1) := by
                      intro a
                      rw [Kernel.comap_apply]
                      exact hlint a (fun x => g (a, x))
                    simp_rw [this]
                    rw [lintegral_fintype, Fintype.sum_prod_type]
                    refine Finset.sum_congr rfl fun a _ => ?_
                    rw [Finset.sum_mul]
                    refine Finset.sum_congr rfl fun b _ => ?_
                    ring
                  have key : ∀ (n : ℕ) (f : BanditHistory K n → ENNReal), Measurable f →
                      ∫⁻ h, f h ∂(banditMeasure ν π n) = ∑ ω : Fin n → Fin K × Bool,
                        ENNReal.ofReal (∏ t : Fin n, (((π.select t (fun i : Fin t =>
                          ((ω ⟨i, i.2.trans t.2⟩).1, if (ω ⟨i, i.2.trans t.2⟩).2 then (1:ℝ) else -1))) {(ω t).1}).toReal *
                          ((1 + μ (ω t).1 * (if (ω t).2 then (1:ℝ) else -1)) / 2))) *
                        f (fun t => ((ω t).1, if (ω t).2 then (1:ℝ) else -1)) := by
                    intro n
                    induction n with
                    | zero =>
                      intro f hf
                      rw [banditMeasure, lintegral_dirac' _ hf, Fintype.sum_unique]
                      simp only [Finset.univ_eq_empty, Finset.prod_empty, ENNReal.ofReal_one, one_mul]
                      congr 1
                      funext t
                      exact t.elim0
                    | succ n ih =>
                      intro f hf
                      refine (lintegral_map hf measurable_banditHistorySnoc).trans ?_
                      refine (Measure.lintegral_compProd (hf.comp measurable_banditHistorySnoc)).trans ?_
                      have hm : Measurable fun h : BanditHistory K n =>
                          ∫⁻ ab, f (Fin.snoc (α := fun _ => Fin K × ℝ) h ab) ∂(banditStepKernel ν π n h) :=
                        (hf.comp measurable_banditHistorySnoc).lintegral_kernel_prod_right'
                      refine (ih _ hm).trans ?_
                      have hg : ∀ h : BanditHistory K n, Measurable fun ab : Fin K × ℝ =>
                          f (Fin.snoc (α := fun _ => Fin K × ℝ) h ab) := fun h =>
                        hf.comp (measurable_banditHistorySnoc.comp (measurable_const.prodMk measurable_id))
                      rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => Fin K × Bool)).sum_comp, Fintype.sum_prod_type,
                        Finset.sum_comm]
                      refine Finset.sum_congr rfl fun ω _ => ?_
                      rw [hstep n _ _ (hg _), Finset.mul_sum]
                      refine Finset.sum_congr rfl fun ab _ => ?_
                      have hsn : ((Fin.snocEquiv (fun _ : Fin (n+1) => Fin K × Bool)) (ab, ω)) =
                          Fin.snoc (α := fun _ => Fin K × Bool) ω ab := rfl
                      rw [hsn, Fin.prod_univ_castSucc]
                      have e1 : ∀ t : Fin n, (Fin.snoc (α := fun _ => Fin K × Bool) ω ab) t.castSucc = ω t :=
                        fun t => Fin.snoc_castSucc (α := fun _ => Fin K × Bool) ab ω t
                      have e2 : (Fin.snoc (α := fun _ => Fin K × Bool) ω ab) (Fin.last n) = ab :=
                        Fin.snoc_last (α := fun _ => Fin K × Bool) ab ω
                      have e3 : ∀ (i : ℕ) (hi : i < n) (hi' : i < n + 1),
                          (Fin.snoc (α := fun _ => Fin K × Bool) ω ab) ⟨i, hi'⟩ = ω ⟨i, hi⟩ :=
                        fun i hi hi' => e1 ⟨i, hi⟩
                      have e4 : (fun t : Fin (n+1) => (((Fin.snoc (α := fun _ => Fin K × Bool) ω ab) t).1,
                          if ((Fin.snoc (α := fun _ => Fin K × Bool) ω ab) t).2 then (1:ℝ) else -1)) =
                          Fin.snoc (α := fun _ => Fin K × ℝ) (fun t => ((ω t).1, if (ω t).2 then (1:ℝ) else -1))
                            (ab.1, if ab.2 then (1:ℝ) else -1) := by
                        funext t
                        refine Fin.lastCases ?_ (fun t => ?_) t
                        · rw [e2, Fin.snoc_last (α := fun _ => Fin K × ℝ)]
                        · rw [e1, Fin.snoc_castSucc (α := fun _ => Fin K × ℝ)]
                      rw [e4, e2]
                      have e5 : ∀ t : Fin n, (fun i : Fin (t.castSucc : Fin (n+1)) =>
                          (((Fin.snoc (α := fun _ => Fin K × Bool) ω ab) ⟨i, i.2.trans t.castSucc.2⟩).1,
                          if ((Fin.snoc (α := fun _ => Fin K × Bool) ω ab) ⟨i, i.2.trans t.castSucc.2⟩).2 then (1:ℝ) else -1)) =
                          (fun i : Fin t => ((ω ⟨i, i.2.trans t.2⟩).1, if (ω ⟨i, i.2.trans t.2⟩).2 then (1:ℝ) else -1)) := by
                        intro t; funext i
                        have hi : (i : ℕ) < n := lt_of_lt_of_le i.2 (le_of_lt t.2)
                        rw [e3 i hi]
                      have e6 : (fun i : Fin (Fin.last n : Fin (n+1)) =>
                          (((Fin.snoc (α := fun _ => Fin K × Bool) ω ab) ⟨i, i.2.trans (Fin.last n).2⟩).1,
                          if ((Fin.snoc (α := fun _ => Fin K × Bool) ω ab) ⟨i, i.2.trans (Fin.last n).2⟩).2 then (1:ℝ) else -1)) =
                          (fun t : Fin n => ((ω t).1, if (ω t).2 then (1:ℝ) else -1)) := by
                        funext i
                        have hi : (i : ℕ) < n := i.2
                        rw [e3 i hi]; rfl
                      have e7 : ∀ t : Fin n, ((π.select (t.castSucc : Fin (n+1)) (fun i : Fin (t.castSucc : Fin (n+1)) =>
                          (((Fin.snoc (α := fun _ => Fin K × Bool) ω ab) ⟨i, i.2.trans t.castSucc.2⟩).1,
                          if ((Fin.snoc (α := fun _ => Fin K × Bool) ω ab) ⟨i, i.2.trans t.castSucc.2⟩).2 then (1:ℝ) else -1)))
                            {((Fin.snoc (α := fun _ => Fin K × Bool) ω ab) t.castSucc).1}) =
                          (π.select t (fun i : Fin t => ((ω ⟨i, i.2.trans t.2⟩).1, if (ω ⟨i, i.2.trans t.2⟩).2 then (1:ℝ) else -1)))
                            {(ω t).1} := by
                        intro t
                        rw [e5 t, e1 t]; rfl
                      have e8 : ((π.select (Fin.last n : Fin (n+1)) (fun i : Fin (Fin.last n : Fin (n+1)) =>
                          (((Fin.snoc (α := fun _ => Fin K × Bool) ω ab) ⟨i, i.2.trans (Fin.last n).2⟩).1,
                          if ((Fin.snoc (α := fun _ => Fin K × Bool) ω ab) ⟨i, i.2.trans (Fin.last n).2⟩).2 then (1:ℝ) else -1)))
                            {ab.1}) =
                          (π.select n (fun t : Fin n => ((ω t).1, if (ω t).2 then (1:ℝ) else -1))) {ab.1} := by
                        rw [e6]; rfl
                      rw [e8]
                      simp_rw [e7, e1]
                      have hβ : ∀ (a : Fin K) (b : Bool), 0 ≤ (1 + μ a * (if b then (1:ℝ) else -1)) / 2 := by
                        intro a b
                        cases b
                        · rw [if_neg Bool.false_ne_true, mul_neg_one, ← sub_eq_add_neg]; exact hhi2 a
                        · rw [if_pos (rfl : true = true), mul_one]; exact hlo2 a
                      rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun t _ =>
                        mul_nonneg ENNReal.toReal_nonneg (hβ _ _)),
                        ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _)]
                      ring
                  intro n
                  refine Measure.ext_of_lintegral _ fun f hf => ?_
                  rw [key n f hf, lintegral_finsetSum_measure]
                  refine Finset.sum_congr rfl fun ω _ => ?_
                  rw [lintegral_smul_measure, lintegral_dirac' _ hf]
                  rfl
            have REDUCE :
                ∀ (K S T : ℕ) (π : BanditPolicy K), IsAdmissiblePolicy S T π →
              ∃ Q : (Fin T → Fin K × Bool) → ℝ, (∀ ω, 0 ≤ Q ω) ∧
              (∀ μ : Fin K → ℝ, (∀ i, |μ i| ≤ 1/2) → ∑ ω, (Q ω * ∏ s, (1 + μ (ω s).1 * (if (ω s).2 then (1:ℝ) else -1))) = 1) ∧
              (∀ μ : Fin K → ℝ, (∀ i, |μ i| ≤ 1/2) → ∀ (t : Fin T) (g : (Fin T → Fin K × Bool) → ℝ) (φ : Fin K × Bool → ℝ),
                (∀ ω ω', (∀ i, i < t → ω i = ω' i) → g ω = g ω') →
                ∑ ω, (Q ω * ∏ s, (1 + μ (ω s).1 * (if (ω s).2 then (1:ℝ) else -1))) * (g ω * (φ (ω t) - ∑ b : Bool, (1 + μ (ω t).1 * (if b then (1:ℝ) else -1)) / 2 * φ ((ω t).1, b))) = 0) ∧
              (∀ ω, Q ω ≠ 0 → switchCost (fun t => ((ω t).1, if (ω t).2 then (1:ℝ) else -1) : BanditHistory K T) 1 T ≤ S) ∧
              (∀ (μ : Fin K → ℝ) (k : Fin K) (d : ℝ), 0 < d → (∀ i, |μ i| ≤ 1/2) → (∀ i, i ≠ k → μ i + d ≤ μ k) → 1 < K →
                ∃ ν : StochasticBandit K, AdmissibleEnvironment ν ∧
                  d * ∑ ω, (Q ω * ∏ s, (1 + μ (ω s).1 * (if (ω s).2 then (1:ℝ) else -1))) * (d * ((Finset.univ.filter (fun t : Fin T => (ω t).1 ≠ k)).card : ℝ)) ≤
                    sourceGap ν * banditRegret ν π T) := by
              clear FIN COMB STUCKCOMB
              classical
              intro K S T π hπ
              obtain ⟨p, hp0, hp1, hν⟩ := BRIDGE K π
              have hsum : ∀ (n : ℕ) (F : (Fin (n+1) → Fin K × Bool) → ℝ),
                  ∑ ω, F ω = ∑ ω' : Fin n → Fin K × Bool, ∑ ab : Fin K × Bool, F (Fin.snoc (α := fun _ => Fin K × Bool) ω' ab) := by
                intro n F
                rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => Fin K × Bool)).sum_comp F, Fintype.sum_prod_type_right]
                rfl
              obtain ⟨W, hW⟩ : ∃ W : (Fin K → ℝ) → (n : ℕ) → (Fin n → Fin K × Bool) → ℝ, ∀ μ n ω, W μ n ω =
                  (∏ t : Fin n, p t (fun i => ω ⟨i, i.2.trans t.2⟩) (ω t).1 / 2) *
                    ∏ s : Fin n, (1 + μ (ω s).1 * (if (ω s).2 then (1:ℝ) else -1)) := ⟨_, fun _ _ _ => rfl⟩
              have hstep : ∀ (μ : Fin K → ℝ) (n : ℕ) (ω : Fin n → Fin K × Bool) (ab : Fin K × Bool),
                  W μ (n+1) (Fin.snoc (α := fun _ => Fin K × Bool) ω ab) = W μ n ω *
                  (p n ω ab.1 * ((1 + μ ab.1 * (if ab.2 then (1:ℝ) else -1)) / 2)) := by
                intro μ n ω ab
                rw [hW, hW]
                have hpre : ∀ (m : ℕ) (hm : m ≤ n), (fun i : Fin m => (Fin.snoc (α := fun _ => Fin K × Bool) ω ab : Fin (n+1) → Fin K × Bool) ⟨i, by omega⟩) = fun i : Fin m => ω ⟨i, by omega⟩ := by
                  intro m hm
                  funext i
                  have hi : (i : ℕ) < n := by omega
                  simp [Fin.snoc, hi]
                rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
                simp only [Fin.snoc_castSucc, Fin.snoc_last]
                have e1 : ∀ t : Fin n, p (t.castSucc : Fin (n+1)) (fun i => (Fin.snoc (α := fun _ => Fin K × Bool) ω ab : Fin (n+1) → Fin K × Bool) ⟨i, i.2.trans t.castSucc.2⟩) (ω t).1 = p t (fun i => ω ⟨i, i.2.trans t.2⟩) (ω t).1 := by
                  intro t
                  exact congrFun (congrArg (p t) (hpre t t.2.le)) _
                have e2 : p (Fin.last n : Fin (n+1)) (fun i => (Fin.snoc (α := fun _ => Fin K × Bool) ω ab : Fin (n+1) → Fin K × Bool) ⟨i, i.2.trans (Fin.last n).2⟩) ab.1 = p n ω ab.1 :=
                  congrFun (congrArg (p n) (hpre n le_rfl)) _
                rw [Finset.prod_congr rfl (fun t _ => by rw [e1 t]), e2]
                ring
              have hb1 : ∀ x : ℝ, ∑ b : Bool, (1 + x * (if b then (1:ℝ) else -1)) / 2 = 1 := by
                intro x; rw [Fintype.sum_bool, if_pos (rfl : true = true), if_neg Bool.false_ne_true]; ring
              -- summing out the last coordinate
              have hlast : ∀ (μ : Fin K → ℝ) (n : ℕ) (ω : Fin n → Fin K × Bool),
                  ∑ ab : Fin K × Bool, p n ω ab.1 * ((1 + μ ab.1 * (if ab.2 then (1:ℝ) else -1)) / 2) = 1 := by
                intro μ n ω
                rw [Fintype.sum_prod_type]
                simp only [← Finset.mul_sum, hb1, mul_one, hp1]
              have hG1 : ∀ (μ : Fin K → ℝ) (n : ℕ), ∑ ω : Fin n → Fin K × Bool,
                  W μ n ω = 1 := by
                intro μ n
                induction n with
                | zero => rw [Fintype.sum_unique, hW, Fin.prod_univ_zero, Fin.prod_univ_zero, one_mul]
                | succ n ih =>
                  rw [hsum]
                  simp only [hstep, ← Finset.mul_sum, hlast, mul_one]
                  exact ih
              have hGZ : ∀ (μ : Fin K → ℝ) (φ : Fin K × Bool → ℝ) (n : ℕ) (t : Fin n) (g : (Fin n → Fin K × Bool) → ℝ),
                  (∀ ω ω', (∀ i, i < t → ω i = ω' i) → g ω = g ω') →
                  ∑ ω : Fin n → Fin K × Bool,
                  W μ n ω *
                    (g ω * (φ (ω t) - ∑ b : Bool, (1 + μ (ω t).1 * (if b then (1:ℝ) else -1)) / 2 * φ ((ω t).1, b))) = 0 := by
                intro μ φ n
                induction n with
                | zero => intro t; exact t.elim0
                | succ n ih =>
                  intro t g hg
                  rw [hsum]
                  refine Fin.lastCases ?_ (fun t' => ?_) t hg
                  · intro hg
                    apply Finset.sum_eq_zero
                    intro ω _
                    have hgc : ∀ ab ab', g (Fin.snoc (α := fun _ => Fin K × Bool) ω ab) = g (Fin.snoc (α := fun _ => Fin K × Bool) ω ab') := by
                      intro ab ab'
                      apply hg
                      intro i hi
                      have hi' : (i : ℕ) < n := hi
                      simp [Fin.snoc, hi']
                    simp only [hstep, Fin.snoc_last]
                    rw [Fintype.sum_prod_type]
                    apply Finset.sum_eq_zero
                    intro a _
                    rw [Fintype.sum_bool, hgc (a, true) (a, false)]
                    simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
                    ring
                  · intro hg
                    simp only [hstep, Fin.snoc_castSucc]
                    have hgc : ∀ ω ab ab', g (Fin.snoc (α := fun _ => Fin K × Bool) ω ab) = g (Fin.snoc (α := fun _ => Fin K × Bool) ω ab') := by
                      intro ω ab ab'
                      apply hg
                      intro i hi
                      have hi' : (i : ℕ) < n := lt_trans (show (i:ℕ) < (t' : ℕ) from hi) t'.2
                      simp [Fin.snoc, hi']
                    have hne : Nonempty (Fin K × Bool) ∨ IsEmpty (Fin K × Bool) := (isEmpty_or_nonempty _).symm
                    rcases hne with ⟨⟨c⟩⟩ | hE
                    · have := ih t' (fun ω => g (Fin.snoc (α := fun _ => Fin K × Bool) ω c)) (by
                        intro ω ω' h
                        apply hg
                        intro i hi
                        have hi' : (i : ℕ) < n := lt_trans (show (i:ℕ) < (t' : ℕ) from hi) t'.2
                        simp only [Fin.snoc, hi', dite_true]
                        exact h ⟨i, hi'⟩ hi)
                      rw [← this]
                      apply Finset.sum_congr rfl
                      intro ω _
                      simp only [fun ab => hgc ω ab c]
                      rw [← Finset.sum_mul, ← Finset.mul_sum, hlast, mul_one]
                    · apply Finset.sum_eq_zero
                      intro ω _
                      exact Finset.sum_of_isEmpty _
              have hq0 : ∀ ω : Fin T → Fin K × Bool, 0 ≤ ∏ t : Fin T, p t (fun i => ω ⟨i, i.2.trans t.2⟩) (ω t).1 / 2 := by
                intro ω
                exact Finset.prod_nonneg (fun t _ => div_nonneg (hp0 _ _ _) zero_le_two)
              have hw : ∀ (μ : Fin K → ℝ) (ω : Fin T → Fin K × Bool),
                  (∏ t : Fin T, (p t (fun i => ω ⟨i, i.2.trans t.2⟩) (ω t).1 *
                      ((1 + μ (ω t).1 * (if (ω t).2 then (1:ℝ) else -1)) / 2))) =
                  W μ T ω := by
                intro μ ω
                rw [hW, ← Finset.prod_mul_distrib]
                exact Finset.prod_congr rfl (fun t _ => by ring)
              have hw0 : ∀ (μ : Fin K → ℝ), (∀ i, |μ i| ≤ 1/2) → ∀ (ω : Fin T → Fin K × Bool),
                  0 ≤ W μ T ω := by
                intro μ hμ ω
                rw [hW]
                refine mul_nonneg (hq0 ω) ?_
                apply Finset.prod_nonneg
                intro s _
                have := abs_le.mp (hμ (ω s).1)
                split_ifs
                · rw [mul_one]
                  exact neg_le_iff_add_nonneg'.mp ((neg_le_neg one_half_lt_one.le).trans this.1)
                · rw [mul_neg_one, ← sub_eq_add_neg]
                  exact sub_nonneg.mpr (this.2.trans one_half_lt_one.le)
              refine ⟨fun ω => ∏ t : Fin T, p t (fun i => ω ⟨i, i.2.trans t.2⟩) (ω t).1 / 2, hq0, fun μ _ => ?_, fun μ _ t g φ hg => ?_, ?_, ?_⟩
              · exact (Finset.sum_congr rfl fun ω _ => (hW μ T ω).symm).trans (hG1 μ T)
              · refine (Finset.sum_congr rfl fun ω _ => ?_).trans (hGZ μ φ T t g hg)
                rw [hW]
              · intro ω hω
                obtain ⟨ν, hadm, hmean, hmeas⟩ := hν 0 (by intro i; rw [Pi.zero_apply, abs_zero]; exact one_half_pos.le)
                have h := hπ ν hadm
                rw [hmeas T] at h
                by_contra hcon
                rw [ae_iff, Measure.finset_sum_apply, Finset.sum_eq_zero_iff] at h
                have h2 := h ω (Finset.mem_univ _)
                rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at h2
                rcases h2 with h2 | h2
                · rw [hw, hW] at h2
                  simp only [Pi.zero_apply, zero_mul, add_zero, Finset.prod_const_one, mul_one] at h2
                  exact (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne (hq0 ω) (Ne.symm hω))).ne' h2
                · rw [Measure.dirac_apply, Set.indicator_of_mem (by exact hcon)] at h2
                  simp at h2
              · intro μ k d hd hμ hk hK
                obtain ⟨ν, hadm, hmean, hmeas⟩ := hν μ hμ
                refine ⟨ν, hadm, ?_⟩
                have hgap : d ≤ sourceGap ν := by
                  have hb : ∃ i, UniqueBest ν i := ⟨k, fun j hj => by rw [hmean, hmean]; exact (lt_add_of_pos_right _ hd).trans_le (hk j hj)⟩
                  have hck : Classical.choose hb = k := by
                    by_contra hne
                    have h1 := Classical.choose_spec hb
                    have h2 := h1 k (Ne.symm hne)
                    have h3 := hk _ hne
                    rw [hmean, hmean] at h2
                    exact lt_asymm h2 ((lt_add_of_pos_right _ hd).trans_le h3)
                  have hn : (Finset.univ.erase (Classical.choose hb)).Nonempty := by
                    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
                    omega
                  unfold sourceGap
                  rw [dif_pos hb]
                  simp only
                  rw [dif_pos hn]
                  rw [Finset.le_inf'_iff]
                  intro j hj
                  have hj' := (Finset.mem_erase.mp hj).1
                  rw [hck] at hj' ⊢
                  rw [hmean, hmean]
                  exact le_sub_iff_add_le'.mpr (hk j hj')
                have hopt : banditOptimalMean ν = μ k := by
                  unfold banditOptimalMean
                  have : Nonempty (Fin K) := ⟨k⟩
                  apply le_antisymm
                  · apply ciSup_le
                    intro i
                    rw [hmean]
                    by_cases hi : i = k
                    · rw [hi]
                    · exact (le_add_of_nonneg_right hd.le).trans (hk i hi)
                  · rw [← hmean k]
                    exact le_ciSup (Set.finite_range _).bddAbove k
                have hmeasbl : Measurable (fun h : BanditHistory K T => ∑ t, (h t).2) :=
                  Finset.measurable_sum _ (fun t _ => measurable_snd.comp (measurable_pi_apply t))
                have hint : ∫ h, (∑ t, (h t).2) ∂(banditMeasure ν π T) =
                    ∑ ω : Fin T → Fin K × Bool, W μ T ω * ∑ t, (if (ω t).2 then (1:ℝ) else -1) := by
                  rw [hmeas T, integral_finsetSum_measure]
                  · apply Finset.sum_congr rfl
                    intro ω _
                    rw [integral_smul_measure, integral_dirac, hw, ENNReal.toReal_ofReal (hw0 μ hμ ω), smul_eq_mul]
                  · intro ω _
                    exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
                have hreg : banditRegret ν π T = ∑ ω : Fin T → Fin K × Bool, W μ T ω * ∑ t, (μ k - μ (ω t).1) := by
                  have hz : ∑ ω : Fin T → Fin K × Bool, W μ T ω *
                      ∑ t, ((if (ω t).2 then (1:ℝ) else -1) - μ (ω t).1) = 0 := by
                    simp only [Finset.mul_sum]
                    rw [Finset.sum_comm]
                    apply Finset.sum_eq_zero
                    intro t _
                    have := hGZ μ (fun ab => if ab.2 then (1:ℝ) else -1) T t (fun _ => 1) (fun _ _ _ => rfl)
                    rw [← this]
                    apply Finset.sum_congr rfl
                    intro ω _
                    congr 1
                    rw [Fintype.sum_bool]
                    simp only [if_true, Bool.false_eq_true, if_false]
                    ring
                  unfold banditRegret
                  rw [hopt, hint]
                  have e : ∀ ω : Fin T → Fin K × Bool, ∑ t, (μ k - μ (ω t).1) = (T : ℝ) * μ k - ∑ t, (if (ω t).2 then (1:ℝ) else -1) + ∑ t, ((if (ω t).2 then (1:ℝ) else -1) - μ (ω t).1) := by
                    intro ω
                    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                    ring
                  refine ((Finset.sum_congr rfl (fun ω _ => by rw [e ω, mul_add, mul_sub])).trans ?_).symm
                  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hz, ← Finset.sum_mul, hG1 μ T, one_mul, add_zero]
                have hle : ∑ ω : Fin T → Fin K × Bool, W μ T ω * (d * ((Finset.univ.filter (fun t : Fin T => (ω t).1 ≠ k)).card : ℝ)) ≤ banditRegret ν π T := by
                  rw [hreg]
                  apply Finset.sum_le_sum
                  intro ω _
                  apply mul_le_mul_of_nonneg_left _ (hw0 μ hμ ω)
                  rw [Finset.card_filter]
                  push_cast
                  rw [Finset.mul_sum]
                  apply Finset.sum_le_sum
                  intro t _
                  by_cases h : (ω t).1 = k
                  · rw [if_neg (not_not.mpr h), mul_zero, h, sub_self]
                  · rw [if_pos h, mul_one]
                    exact le_sub_iff_add_le'.mpr (hk _ h)
                refine le_trans (le_of_eq ?_) (mul_le_mul hgap hle (Finset.sum_nonneg (fun ω _ => mul_nonneg (hw0 μ hμ ω) (mul_nonneg hd.le (Nat.cast_nonneg _)))) (hd.le.trans hgap))
                simp only [hW]
            have LRL :
                ∀ (K T : ℕ) (Q : (Fin T → Fin K × Bool) → ℝ), (∀ ω, 0 ≤ Q ω) →
              (∀ μ : Fin K → ℝ, (∀ i, |μ i| ≤ 1/2) → ∑ ω, (Q ω * ∏ s, (1 + μ (ω s).1 * (if (ω s).2 then (1:ℝ) else -1))) = 1) →
              (∀ μ : Fin K → ℝ, (∀ i, |μ i| ≤ 1/2) → ∀ (t : Fin T) (g : (Fin T → Fin K × Bool) → ℝ) (φ : Fin K × Bool → ℝ),
                (∀ ω ω', (∀ i, i < t → ω i = ω' i) → g ω = g ω') →
                ∑ ω, (Q ω * ∏ s, (1 + μ (ω s).1 * (if (ω s).2 then (1:ℝ) else -1))) * (g ω * (φ (ω t) - ∑ b : Bool, (1 + μ (ω t).1 * (if b then (1:ℝ) else -1)) / 2 * φ ((ω t).1, b))) = 0) →
              ∀ (μ0 : Fin K → ℝ) (k : Fin K) (y δ : ℝ) (u : ℕ) (A : (Fin T → Fin K × Bool) → Prop) (As : Fin T → (Fin T → Fin K × Bool) → Prop),
                (∀ i, |μ0 i| ≤ 1/2) → 0 ≤ μ0 k → μ0 k ≤ y → y ≤ 2 * δ → δ ≤ 1/4 →
                (∀ s ω ω', (∀ i, i < s → ω i = ω' i) → (As s ω ↔ As s ω')) →
                (∀ (s : Fin T) ω, u ≤ (s:ℕ) → (ω s).1 = k → (A ω ↔ As s ω)) →
                ((∑ ω, (Q ω * ∏ s, (1 + μ0 (ω s).1 * (if (ω s).2 then (1:ℝ) else -1))) * (if A ω then (1:ℝ) else 0)) -
                  32 * δ^2 * ∑ ω, (Q ω * ∏ s, (1 + μ0 (ω s).1 * (if (ω s).2 then (1:ℝ) else -1))) * ((Finset.univ.filter (fun t : Fin T => (t:ℕ) < u ∧ (ω t).1 = k)).card : ℝ)) / 2 ≤
                ∑ ω, (Q ω * ∏ s, (1 + (Function.update μ0 k y) (ω s).1 * (if (ω s).2 then (1:ℝ) else -1))) * (if A ω then (1:ℝ) else 0) := by
              clear FIN COMB STUCKCOMB BRIDGE REDUCE
              classical
              have nlog : ∀ z y δ : ℝ, 0 ≤ z → z ≤ y → y ≤ 2 * δ → y ≤ 1/2 → -(6 * δ^2) ≤
                  (1 + z * 1) / 2 * (1 - (1 + z * 1) / (1 + y * 1)) + (1 + z * -1) / 2 * (1 - (1 + z * -1) / (1 + y * -1)) := by
                intro z y δ h0 h1 h2 h3
                have y0 : 0 ≤ y := le_trans h0 h1
                have q0 : y * y ≤ 1/2 * (1/2) := mul_le_mul h3 h3 y0 one_half_pos.le
                have q1 : (y - z) * (y - z) ≤ (2 * δ) * (2 * δ) :=
                  mul_le_mul ((sub_le_self y h0).trans h2) ((sub_le_self y h0).trans h2) (sub_nonneg.2 h1) (y0.trans h2)
                have q2 := sq_nonneg δ
                have p1 : 0 < 1 + y := add_pos_of_pos_of_nonneg one_pos y0
                have p2 : 0 < 1 - y := sub_pos.2 (lt_of_le_of_lt h3 one_half_lt_one)
                have p3 := mul_pos p1 p2
                have id : (1 + z * 1) / 2 * (1 - (1 + z * 1) / (1 + y * 1)) + (1 + z * -1) / 2 * (1 - (1 + z * -1) / (1 + y * -1)) =
                    -((y - z) * (y - z) / ((1 + y) * (1 - y))) := by
                  rw [mul_one, mul_one, mul_neg_one, mul_neg_one, ← sub_eq_add_neg, ← sub_eq_add_neg, one_sub_div p1.ne', one_sub_div p2.ne',
                    mul_div_assoc', mul_div_assoc', div_add_div _ _ p1.ne' p2.ne', ← neg_div]
                  congr 1
                  ring
                rw [id]
                refine neg_le_neg ?_
                rw [div_le_iff₀ p3]
                refine q1.trans ?_
                have e : 6 * δ^2 * ((1 + y) * (1 - y)) = 6 * δ^2 - 6 * (δ^2 * (y * y)) := by ring
                have e2 : 2 * δ * (2 * δ) = 4 * δ^2 := by ring
                rw [e, e2]
                have q3 := mul_le_mul_of_nonneg_left q0 q2
                linarith only [q3, q2]
              have npt : ∀ l lg : ℝ, 0 < l → lg ≤ l - 1 → (l < 1/2 → Real.log 2 + lg ≤ 2 * l - 1) → ∀ p : Prop,
                  ∀ _ : Decidable p, ((if p then (1:ℝ) else 0) - (l - 1 - lg) * (100/19)) / 2 ≤ l * (if p then (1:ℝ) else 0) := by
                intro l lg h0 h1 h2 p _
                split_ifs
                · by_cases h : l < 1/2
                  · have h3 := h2 h
                    have h4 := Real.log_two_gt_d9
                    linarith only [h0, h3, h4, h]
                  · rw [not_lt] at h
                    linarith only [h, h1]
                · rw [mul_zero]
                  linarith only [h1]
              have nfin : ∀ a d s e : ℝ, 0 ≤ d * s → -(6 * d) * s ≤ e → (a - 32 * d * s) / 2 ≤ (a - (1 - 1 - e) * (100/19)) / 2 := by
                intro a d s e h1 h2
                have : -(6 * d) * s = -(6 * (d * s)) := by ring
                rw [this] at h2
                rw [mul_assoc]
                linarith only [h1, h2]
              intro K T Q hQ h1 hZ μ0 k y δ u A As hμ0 hk0 hky hyδ hδ hAs hA
              classical
              have hy : y ≤ 1/2 := hyδ.trans (by linarith only [hδ])
              have hy0 : 0 ≤ y := le_trans hk0 hky
              obtain ⟨sg, hsg⟩ : ∃ sg : Bool → ℝ, ∀ b, (if b then (1:ℝ) else -1) = sg b := ⟨_, fun _ => rfl⟩
              have hsgt : sg true = 1 := by rw [← hsg]; simp
              have hsgf : sg false = -1 := by rw [← hsg]; simp
              simp only [hsg] at h1 hZ ⊢
              have hfac : ∀ (a : Fin K) (b : Bool), 0 < 1 + μ0 a * sg b := by
                intro a b
                have := abs_le.1 (hμ0 a)
                cases b
                · rw [hsgf]; linarith [this.2]
                · rw [hsgt]; linarith [this.1]
              have hfacy : ∀ (b : Bool), 0 < 1 + y * sg b := by
                intro b
                cases b
                · rw [hsgf]; linarith
                · rw [hsgt]; linarith
              obtain ⟨W, hW⟩ : ∃ W : (Fin T → Fin K × Bool) → ℝ, ∀ ω, Q ω * ∏ s, (1 + μ0 (ω s).1 * sg (ω s).2) = W ω := ⟨_, fun _ => rfl⟩
              have hW0 : ∀ ω, 0 ≤ W ω := by
                intro ω
                rw [← hW]
                exact mul_nonneg (hQ ω) (Finset.prod_nonneg fun s _ => (hfac _ _).le)
              have hZ0 := hZ μ0 hμ0
              have h10 := h1 μ0 hμ0
              simp only [hW] at hZ0 h10 ⊢
              obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin K × Bool → ℝ, ∀ p, ρ p = if p.1 = k then (1 + y * sg p.2) / (1 + μ0 k * sg p.2) else 1 := ⟨_, fun _ => rfl⟩
              have hρpos : ∀ p, 0 < ρ p := by
                intro p
                rw [hρ]
                split_ifs
                · exact div_pos (hfacy _) (hfac _ _)
                · norm_num
              obtain ⟨L, hL⟩ : ∃ L : ℕ → (Fin T → Fin K × Bool) → ℝ, ∀ n ω, L n ω = ∏ s ∈ Finset.univ.filter (fun s : Fin T => (s:ℕ) < n), ρ (ω s) := ⟨_, fun _ _ => rfl⟩
              have hLpos : ∀ n ω, 0 < L n ω := by
                intro n ω
                rw [hL]
                exact Finset.prod_pos fun s _ => hρpos _
              have hLdep : ∀ (t : Fin T) (ω ω' : Fin T → Fin K × Bool), (∀ i, i < t → ω i = ω' i) → L t ω = L t ω' := by
                intro t ω ω' h
                rw [hL, hL]
                refine Finset.prod_congr rfl fun s hs => ?_
                rw [h s (Finset.mem_filter.1 hs).2]
              have hfilt : ∀ t : Fin T, (Finset.univ.filter (fun s : Fin T => (s:ℕ) < (t:ℕ) + 1)) =
                  insert t (Finset.univ.filter (fun s : Fin T => (s:ℕ) < (t:ℕ))) := by
                intro t
                ext s
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
                omega
              have hfiltbig : ∀ n, T ≤ n → (Finset.univ.filter (fun s : Fin T => (s:ℕ) < n + 1)) =
                  (Finset.univ.filter (fun s : Fin T => (s:ℕ) < n)) := by
                intro n hn
                ext s
                have := s.2
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                omega
              have hLstep : ∀ (t : Fin T) ω, L ((t:ℕ) + 1) ω = L t ω * ρ (ω t) := by
                intro t ω
                rw [hL, hL, hfilt, Finset.prod_insert (by simp), mul_comm]
              have hLbig : ∀ n, T ≤ n → ∀ ω, L (n+1) ω = L n ω := by
                intro n hn ω
                rw [hL, hL, hfiltbig n hn]
              have hW1 : ∀ ω, Q ω * ∏ s, (1 + (Function.update μ0 k y) (ω s).1 * sg (ω s).2) = W ω * L T ω := by
                intro ω
                rw [← hW, hL, mul_assoc]
                rw [Finset.filter_true_of_mem (fun s _ => s.2), ← Finset.prod_mul_distrib]
                congr 1
                refine Finset.prod_congr rfl fun s _ => ?_
                rw [hρ]
                by_cases h : (ω s).1 = k
                · rw [if_pos h, h, Function.update_self]
                  have := (hfac k (ω s).2).ne'
                  rw [mul_div_assoc', eq_div_iff this]
                  ring
                · rw [if_neg h, Function.update_of_ne h, mul_one]
              simp only [hW1]
              -- mean one of ρ
              have hρ1 : ∀ a : Fin K, ∑ b : Bool, (1 + μ0 a * sg b) / 2 * ρ (a, b) = 1 := by
                intro a
                rw [Fintype.sum_bool, hρ, hρ]
                by_cases h : a = k
                · subst h
                  have e1 := (hfac a true).ne'
                  have e2 := (hfac a false).ne'
                  simp only [if_true]
                  have g : ∀ c d : ℝ, c ≠ 0 → c/2*(d/c) = d/2 := by
                    intro c d hc
                    field_simp
                  rw [g _ _ e1, g _ _ e2, hsgt, hsgf]
                  ring
                · simp only [if_neg h]
                  rw [hsgt, hsgf]
                  ring
              have hmart : ∀ (t : Fin T) (g : (Fin T → Fin K × Bool) → ℝ),
                  (∀ ω ω', (∀ i, i < t → ω i = ω' i) → g ω = g ω') →
                  ∑ ω, W ω * (g ω * (ρ (ω t) - 1)) = 0 := by
                intro t g hg
                have := hZ0 t g ρ hg
                simpa only [hρ1] using this
              have hEL : ∀ n, ∑ ω, W ω * L n ω = 1 := by
                intro n
                induction n with
                | zero => rw [← h10]; refine Finset.sum_congr rfl fun ω _ => ?_; rw [hL]; simp
                | succ n ih =>
                  by_cases hn : n < T
                  · have e := hmart ⟨n, hn⟩ (L n) (hLdep ⟨n, hn⟩)
                    rw [← ih]
                    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
                    refine Eq.trans ?_ e
                    refine Finset.sum_congr rfl fun ω _ => ?_
                    rw [hLstep ⟨n, hn⟩ ω]
                    ring
                  · rw [← ih]
                    refine Finset.sum_congr rfl fun ω _ => ?_
                    rw [hLbig n (not_lt.1 hn)]
              have hEA : ∀ n, u ≤ n → ∑ ω, W ω * L n ω * (if A ω then (1:ℝ) else 0) = ∑ ω, W ω * L u ω * (if A ω then (1:ℝ) else 0) := by
                intro n hun
                induction n, hun using Nat.le_induction with
                | base => rfl
                | succ n hun ih =>
                  rw [← ih]
                  by_cases hn : n < T
                  · have e := hmart ⟨n, hn⟩ (fun ω => L n ω * (if As ⟨n, hn⟩ ω then (1:ℝ) else 0)) (by
                      intro ω ω' h
                      show L n ω * _ = L n ω' * _
                      have e1 := hLdep ⟨n, hn⟩ ω ω' h
                      have e2 : As ⟨n, hn⟩ ω ↔ As ⟨n, hn⟩ ω' := hAs _ _ _ h
                      have e1' : L n ω = L n ω' := e1
                      rw [e1']
                      simp only [e2])
                    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
                    refine Eq.trans ?_ e
                    refine Finset.sum_congr rfl fun ω _ => ?_
                    rw [hLstep ⟨n, hn⟩ ω]
                    show W ω * (L n ω * _) * _ - W ω * L n ω * _ = _
                    by_cases hk : (ω ⟨n, hn⟩).1 = k
                    · simp only [hA ⟨n, hn⟩ ω hun hk]
                      ring
                    · have : ρ (ω ⟨n, hn⟩) = 1 := by rw [hρ, if_neg hk]
                      rw [this]
                      ring
                  · refine Finset.sum_congr rfl fun ω _ => ?_
                    rw [hLbig n (not_lt.1 hn)]
              have hLT : ∑ ω, W ω * L T ω * (if A ω then (1:ℝ) else 0) = ∑ ω, W ω * L u ω * (if A ω then (1:ℝ) else 0) := by
                rcases le_total u T with h | h
                · exact hEA T h
                · refine Finset.sum_congr rfl fun ω _ => ?_
                  have : L T ω = L u ω := by
                    rw [hL, hL]
                    congr 1
                    ext s
                    have := s.2
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                    omega
                  rw [this]
              -- log step
              have hlogstep : ∀ a : Fin K, - (6 * δ^2) * (if a = k then (1:ℝ) else 0) ≤ ∑ b : Bool, (1 + μ0 a * sg b) / 2 * Real.log (ρ (a, b)) := by
                intro a
                rw [Fintype.sum_bool]
                by_cases h : a = k
                · subst h
                  have e1 := hfac a true
                  have l1 : 1 - (ρ (a, true))⁻¹ ≤ Real.log (ρ (a, true)) := Real.one_sub_inv_le_log_of_pos (hρpos _)
                  have l2 : 1 - (ρ (a, false))⁻¹ ≤ Real.log (ρ (a, false)) := Real.one_sub_inv_le_log_of_pos (hρpos _)
                  have e2 := hfac a false
                  rw [hρ, if_pos rfl, inv_div] at l1 l2
                  rw [if_pos rfl, mul_one]
                  rw [hρ, hρ, if_pos rfl, if_pos rfl]
                  rw [hsgt] at e1 l1 ⊢
                  rw [hsgf] at e2 l2 ⊢
                  exact (nlog _ _ _ hk0 hky hyδ hy).trans (add_le_add
                    (mul_le_mul_of_nonneg_left l1 (half_pos e1).le) (mul_le_mul_of_nonneg_left l2 (half_pos e2).le))
                · have : ∀ b, ρ (a, b) = 1 := fun b => by rw [hρ, if_neg h]
                  rw [this, this, if_neg h, Real.log_one, mul_zero, mul_zero, mul_zero, add_zero]
              obtain ⟨N, hN⟩ : ∃ N : ℕ → (Fin T → Fin K × Bool) → ℝ, ∀ n ω, ((Finset.univ.filter (fun t : Fin T => (t:ℕ) < n ∧ (ω t).1 = k)).card : ℝ) = N n ω := ⟨_, fun _ _ => rfl⟩
              simp only [hN]
              have hN' : ∀ n ω, N n ω = ∑ s ∈ Finset.univ.filter (fun s : Fin T => (s:ℕ) < n), (if (ω s).1 = k then (1:ℝ) else 0) := by
                intro n ω
                rw [← hN, Finset.sum_boole, Finset.filter_filter]
              have hlogL : ∀ n ω, Real.log (L n ω) = ∑ s ∈ Finset.univ.filter (fun s : Fin T => (s:ℕ) < n), Real.log (ρ (ω s)) := by
                intro n ω
                rw [hL, Real.log_prod (fun s _ => (hρpos _).ne')]
              have hElog : ∀ n, - (6 * δ^2) * ∑ ω, W ω * N n ω ≤ ∑ ω, W ω * Real.log (L n ω) := by
                intro n
                simp only [hN', hlogL, Finset.mul_sum]
                rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ (α := Fin T → Fin K × Bool))]
                refine Finset.sum_le_sum fun t _ => ?_
                have e := hZ0 t (fun _ => 1) (fun p => Real.log (ρ p)) (fun _ _ _ => rfl)
                have e' : ∑ ω, W ω * Real.log (ρ (ω t)) = ∑ ω, W ω * ∑ b : Bool, (1 + μ0 (ω t).1 * sg b) / 2 * Real.log (ρ ((ω t).1, b)) := by
                  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
                  refine Eq.trans ?_ e
                  refine Finset.sum_congr rfl fun ω _ => ?_
                  ring
                rw [e']
                refine Finset.sum_le_sum fun ω _ => ?_
                have := mul_le_mul_of_nonneg_left (hlogstep (ω t).1) (hW0 ω)
                rw [mul_left_comm]
                exact this
              rw [hLT]
              have hN0 : 0 ≤ ∑ ω, W ω * N u ω := by
                refine Finset.sum_nonneg fun ω _ => mul_nonneg (hW0 ω) ?_
                rw [← hN]; exact Nat.cast_nonneg _
              have hpt : ∀ ω, W ω * ((if A ω then (1:ℝ) else 0) - (L u ω - 1 - Real.log (L u ω)) * (100/19)) / 2 ≤ W ω * L u ω * (if A ω then (1:ℝ) else 0) := by
                intro ω
                rw [mul_assoc, mul_div_assoc]
                refine mul_le_mul_of_nonneg_left ?_ (hW0 ω)
                have p := hLpos u ω
                have b1 : Real.log (L u ω) ≤ L u ω - 1 := Real.log_le_sub_one_of_pos p
                refine npt _ _ p b1 (fun hh => ?_) (A ω) _
                have b2 : Real.log (2 * L u ω) ≤ 2 * L u ω - 1 := Real.log_le_sub_one_of_pos (mul_pos two_pos p)
                rwa [Real.log_mul two_ne_zero p.ne'] at b2
              refine le_trans ?_ (Finset.sum_le_sum fun ω _ => hpt ω)
              have hsum : ∑ ω, W ω * ((if A ω then (1:ℝ) else 0) - (L u ω - 1 - Real.log (L u ω)) * (100/19)) / 2 =
                  (∑ ω, W ω * (if A ω then (1:ℝ) else 0) - (∑ ω, W ω * L u ω - ∑ ω, W ω - ∑ ω, W ω * Real.log (L u ω)) * (100/19)) / 2 := by
                rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_div]
                refine Finset.sum_congr rfl fun ω _ => ?_
                ring
              rw [hsum, hEL, h10]
              exact nfin _ _ _ _ (mul_nonneg (sq_nonneg _) hN0) (hElog u)
            have CORE :
                ∀ (K T : ℕ) (Q : (Fin T → Fin K × Bool) → ℝ), (∀ ω, 0 ≤ Q ω) →
              (∀ μ : Fin K → ℝ, (∀ i, |μ i| ≤ 1/2) → ∑ ω, (Q ω * ∏ s, (1 + μ (ω s).1 * (if (ω s).2 then (1:ℝ) else -1))) = 1) →
              (∀ μ : Fin K → ℝ, (∀ i, |μ i| ≤ 1/2) → ∀ (t : Fin T) (g : (Fin T → Fin K × Bool) → ℝ) (φ : Fin K × Bool → ℝ),
                (∀ ω ω', (∀ i, i < t → ω i = ω' i) → g ω = g ω') →
                ∑ ω, (Q ω * ∏ s, (1 + μ (ω s).1 * (if (ω s).2 then (1:ℝ) else -1))) * (g ω * (φ (ω t) - ∑ b : Bool, (1 + μ (ω t).1 * (if b then (1:ℝ) else -1)) / 2 * φ ((ω t).1, b))) = 0) →
              ∀ (M : ℕ) (τ : ℕ → ℕ) (δ : ℕ → ℝ) (μ0 : Fin K → ℝ) (m R : ℝ), 0 < K → 0 < M → τ M ≤ T → 0 < m → 0 ≤ R →
                (∀ j < M, τ j < τ (j+1)) → (∀ j < M, 0 < δ j ∧ δ j ≤ 1/4) → (∀ i, 0 ≤ μ0 i) → (∀ j < M, ∀ i, μ0 i ≤ δ j) →
                (∀ j < M, δ j ^ 2 * (τ j : ℝ) ≤ m / (64 * M)) →
                (∀ j < M, R ≤ δ j ^ 2 * ((τ (j+1) : ℝ) - τ j)) →
                m ≤ ∑ ω, (Q ω * ∏ s, (1 + μ0 (ω s).1 * (if (ω s).2 then (1:ℝ) else -1))) * ∑ j ∈ Finset.range M, ((Finset.univ.filter (fun k : Fin K => ∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → (ω t).1 ≠ k)).card : ℝ) →
                ∃ (μ : Fin K → ℝ) (k : Fin K) (d : ℝ), 0 < d ∧ (∀ i, |μ i| ≤ 1/2) ∧ (∀ i, i ≠ k → μ i + d ≤ μ k) ∧
                R * m / (4 * M * K) ≤ d * ∑ ω, (Q ω * ∏ s, (1 + μ (ω s).1 * (if (ω s).2 then (1:ℝ) else -1))) * (d * ((Finset.univ.filter (fun t : Fin T => (ω t).1 ≠ k)).card : ℝ)) := by
              clear FIN COMB STUCKCOMB BRIDGE REDUCE
              classical
              intro K T Q hQ h1 hZ M τ δ μ0 m R hK hM hτM hm hR hτ hδ hμ0 hμδ hδτ hRδ hmiss
              have hMr : (0:ℝ) < M := Nat.cast_pos.mpr hM
              have hKr : (0:ℝ) < K := Nat.cast_pos.mpr hK
              have hμ0' : ∀ i, |μ0 i| ≤ 1/2 := fun i => by
                rw [abs_of_nonneg (hμ0 i)]
                exact (hμδ 0 hM i).trans ((hδ 0 hM).2.trans (by norm_num))
              have main : ∀ (Ω : Type) (inst : Fintype Ω) (W : (Fin K → ℝ) → Ω → ℝ) (I N : ℕ → Fin K → Ω → ℝ) (D : Fin K → Ω → ℝ),
                  (∀ μ, (∀ i, |μ i| ≤ 1/2) → ∀ ω, 0 ≤ W μ ω) → (∑ ω, W μ0 ω = 1) →
                  (∀ j < M, ∀ k, (∑ ω, W μ0 ω * I j k ω - 32 * (δ j)^2 * ∑ ω, W μ0 ω * N j k ω) / 2 ≤
                    ∑ ω, W (Function.update μ0 k (2 * δ j)) ω * I j k ω) →
                  (∀ j < M, ∀ ω, ∑ k, N j k ω ≤ (τ j : ℝ)) →
                  (∀ j < M, ∀ k ω, ((τ (j+1) : ℝ) - τ j) * I j k ω ≤ D k ω) →
                  (m ≤ ∑ ω, W μ0 ω * ∑ j ∈ Finset.range M, ∑ k, I j k ω) →
                  ∃ (μ : Fin K → ℝ) (k : Fin K) (d : ℝ), 0 < d ∧ (∀ i, |μ i| ≤ 1/2) ∧ (∀ i, i ≠ k → μ i + d ≤ μ k) ∧
                    R * m / (4 * M * K) ≤ d * ∑ ω, W μ ω * (d * D k ω) := by
                clear LRL h1 hZ hQ
                intro Ω inst W I N D hW hone hLR hN hD hms
                obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, ∀ j, a j = ∑ k, ∑ ω, W μ0 ω * I j k ω := ⟨_, fun _ => rfl⟩
                obtain ⟨b, hb⟩ : ∃ b : ℕ → Fin K → ℝ, ∀ j k, b j k = ∑ ω, W (Function.update μ0 k (2 * δ j)) ω * I j k ω := ⟨_, fun _ _ => rfl⟩
                have hA : m ≤ ∑ j ∈ Finset.range M, a j := by
                  refine hms.trans (le_of_eq ?_)
                  have e : ∀ ω, W μ0 ω * ∑ j ∈ Finset.range M, ∑ k, I j k ω = ∑ j ∈ Finset.range M, ∑ k, W μ0 ω * I j k ω := fun ω => by
                    rw [Finset.mul_sum]
                    exact Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
                  rw [Finset.sum_congr rfl fun ω _ => e ω, Finset.sum_comm]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [Finset.sum_comm, ha]
                have hB : ∀ j < M, a j / 2 - m / (4 * M) ≤ ∑ k, b j k := by
                  intro j hj
                  have hs := Finset.sum_le_sum fun (k : Fin K) (_ : k ∈ Finset.univ) => hLR j hj k
                  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ← ha] at hs
                  rw [Finset.sum_congr rfl fun k _ => hb j k]
                  refine le_trans ?_ hs
                  have hN' : ∑ k, ∑ ω, W μ0 ω * N j k ω ≤ (τ j : ℝ) := by
                    rw [Finset.sum_comm]
                    calc ∑ ω, ∑ k, W μ0 ω * N j k ω ≤ ∑ ω, W μ0 ω * (τ j : ℝ) := by
                          refine Finset.sum_le_sum fun ω _ => ?_
                          rw [← Finset.mul_sum]
                          exact mul_le_mul_of_nonneg_left (hN j hj ω) (hW μ0 hμ0' ω)
                      _ = τ j := by rw [← Finset.sum_mul, hone, one_mul]
                  have h3 := mul_le_mul_of_nonneg_left hN' (sq_nonneg (δ j))
                  have h4 := hδτ j hj
                  have h5 : m / (4 * M) = 32 * (m / (64 * M)) / 2 := by
                    rw [← mul_div_assoc, div_div, mul_comm (32:ℝ), show (64 * (M:ℝ)) * 2 = 4 * M * 32 by ring, mul_div_mul_right _ _ (by norm_num)]
                  rw [h5, mul_assoc, sub_div]
                  exact sub_le_sub_left (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (h3.trans h4) (by norm_num)) zero_le_two) _
                obtain ⟨j, hjM, hj⟩ : ∃ j ∈ Finset.range M, m / 4 / M ≤ ∑ k, b j k := by
                  refine Finset.exists_le_of_sum_le ⟨0, Finset.mem_range.mpr hM⟩ ?_
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hMr.ne']
                  have hs := Finset.sum_le_sum fun j (hj : j ∈ Finset.range M) => hB j (Finset.mem_range.mp hj)
                  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← div_div,
                    mul_div_cancel₀ _ hMr.ne'] at hs
                  refine le_trans (le_sub_iff_add_le.mpr ?_) hs
                  rw [show m / 4 + m / 4 = m / 2 by ring]
                  exact div_le_div_of_nonneg_right hA zero_le_two
                have hj' := Finset.mem_range.mp hjM
                obtain ⟨k, _, hk⟩ : ∃ k ∈ (Finset.univ : Finset (Fin K)), m / 4 / M / K ≤ b j k := by
                  refine Finset.exists_le_of_sum_le ⟨⟨0, hK⟩, Finset.mem_univ _⟩ ?_
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ hKr.ne']
                  exact hj
                obtain ⟨hδ0, hδ4⟩ := hδ j hj'
                have hμ1 : ∀ i, |Function.update μ0 k (2 * δ j) i| ≤ 1/2 := by
                  intro i
                  by_cases hi : i = k
                  · rw [hi, Function.update_self, abs_of_nonneg (mul_nonneg zero_le_two hδ0.le)]
                    exact (mul_le_mul_of_nonneg_left hδ4 zero_le_two).trans (by norm_num)
                  · rw [Function.update_of_ne hi]
                    exact hμ0' i
                refine ⟨Function.update μ0 k (2 * δ j), k, δ j, hδ0, hμ1, ?_, ?_⟩
                · intro i hi
                  rw [Function.update_of_ne hi, Function.update_self]
                  exact (add_le_add (hμδ j hj' i) le_rfl).trans_eq (two_mul _).symm
                · have hfin : δ j ^ 2 * ((τ (j+1) : ℝ) - τ j) * b j k ≤
                      δ j * ∑ ω, W (Function.update μ0 k (2 * δ j)) ω * (δ j * D k ω) := by
                    rw [hb, Finset.mul_sum, Finset.mul_sum]
                    refine Finset.sum_le_sum fun ω _ => ?_
                    have hw := hW _ hμ1 ω
                    have h7 := mul_le_mul_of_nonneg_left (hD j hj' k ω) (mul_nonneg (sq_nonneg (δ j)) hw)
                    generalize W (Function.update μ0 k (2 * δ j)) ω = w at h7 ⊢
                    refine le_trans (le_of_eq ?_) (le_trans h7 (le_of_eq ?_)) <;> ring
                  refine le_trans ?_ hfin
                  have h8 : R * m / (4 * M * K) = R * (m / 4 / M / K) := by
                    rw [div_div, div_div, mul_div_assoc, mul_assoc]
                  rw [h8]
                  exact mul_le_mul (hRδ j hj') hk (div_nonneg (div_nonneg (div_nonneg hm.le (by norm_num)) hMr.le) hKr.le)
                    (hR.trans (hRδ j hj'))
              have hmono : ∀ j < M, τ (j+1) ≤ T := by
                intro j hj'
                have hmono : ∀ i, j + 1 + i ≤ M → τ (j+1) ≤ τ (j+1+i) := by
                  intro i
                  induction i with
                  | zero => intro _; exact le_rfl
                  | succ i ih => exact fun hi => (ih (Nat.le_of_succ_le hi)).trans (hτ (j+1+i) hi).le
                have := hmono (M - (j+1)) (Nat.add_sub_cancel' hj').le
                rw [Nat.add_sub_cancel' hj'] at this
                exact this.trans hτM
              have hcardD : ∀ j < M, ∀ (k : Fin K) (a : Fin T → Fin K),
                  ((τ (j+1) : ℝ) - τ j) * (if (∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → a t ≠ k) then (1:ℝ) else 0)
                    ≤ ((Finset.univ.filter (fun t : Fin T => a t ≠ k)).card : ℝ) := by
                intro j hj' k a
                split_ifs with h
                · rw [mul_one]
                  have hc : (Finset.Ico (τ j) (τ (j+1))).card ≤ (Finset.univ.filter (fun t : Fin T => a t ≠ k)).card := by
                    refine Finset.card_le_card_of_surjOn (fun t : Fin T => (t:ℕ)) ?_
                    intro s hs
                    rw [Finset.mem_coe, Finset.mem_Ico] at hs
                    refine ⟨⟨s, lt_of_lt_of_le hs.2 (hmono j hj')⟩, ?_, rfl⟩
                    rw [Finset.mem_coe, Finset.mem_filter]
                    exact ⟨Finset.mem_univ _, h _ hs.1 hs.2⟩
                  rw [Nat.card_Ico] at hc
                  rw [← Nat.cast_sub (hτ j hj').le]
                  exact Nat.cast_le.mpr hc
                · rw [mul_zero]
                  exact Nat.cast_nonneg _
              have hcardN : ∀ (j : ℕ) (a : Fin T → Fin K),
                  ∑ k : Fin K, ((Finset.univ.filter (fun t : Fin T => (t:ℕ) < τ j ∧ a t = k)).card : ℝ) ≤ τ j := by
                intro j a
                have e1 : ∑ k : Fin K, (Finset.univ.filter (fun t : Fin T => (t:ℕ) < τ j ∧ a t = k)).card
                    = (Finset.univ.filter (fun t : Fin T => (t:ℕ) < τ j)).card := by
                  rw [Finset.card_eq_sum_card_fiberwise (f := a) (t := Finset.univ) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
                  refine Finset.sum_congr rfl fun k _ => ?_
                  rw [Finset.filter_filter]
                have e2 : (Finset.univ.filter (fun t : Fin T => (t:ℕ) < τ j)).card ≤ τ j := by
                  refine (Finset.card_le_card_of_injOn (t := Finset.range (τ j)) (fun t : Fin T => (t:ℕ)) ?_ ?_).trans (Finset.card_range _).le
                  · intro t ht
                    rw [Finset.mem_coe, Finset.mem_filter] at ht
                    exact Finset.mem_coe.mpr (Finset.mem_range.mpr ht.2)
                  · intro a _ b _ h
                    exact Fin.ext h
                rw [← Nat.cast_sum]
                exact Nat.cast_le.mpr (e1.le.trans e2)
              refine main (Fin T → Fin K × Bool) inferInstance
                (fun μ ω => Q ω * ∏ s, (1 + μ (ω s).1 * (if (ω s).2 then (1:ℝ) else -1)))
                (fun j k ω => if (∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → (ω t).1 ≠ k) then (1:ℝ) else 0)
                (fun j k ω => ((Finset.univ.filter (fun t : Fin T => (t:ℕ) < τ j ∧ (ω t).1 = k)).card : ℝ))
                (fun k ω => ((Finset.univ.filter (fun t : Fin T => (ω t).1 ≠ k)).card : ℝ))
                ?_ (h1 μ0 hμ0') ?_ (fun j _ ω => hcardN j (fun t => (ω t).1)) (fun j hj k ω => hcardD j hj k (fun t => (ω t).1)) ?_
              · intro μ hμ ω
                refine mul_nonneg (hQ ω) (Finset.prod_nonneg fun s _ => ?_)
                have h := abs_le.mp (hμ (ω s).1)
                split_ifs
                · rw [mul_one]
                  exact neg_le_iff_add_nonneg'.mp (le_trans (by norm_num) h.1)
                · rw [mul_neg, mul_one, ← sub_eq_add_neg]
                  exact sub_nonneg.mpr (h.2.trans (by norm_num))
              · intro j hj k
                have key2 := LRL K T Q hQ h1 hZ μ0 k (2 * δ j) (δ j) (τ j)
                  (fun ω => ∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → (ω t).1 ≠ k)
                  (fun s ω => τ (j+1) ≤ (s:ℕ) ∧ ∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → (ω t).1 ≠ k)
                  hμ0' (hμ0 k) ((hμδ j hj k).trans (le_mul_of_one_le_left (hδ j hj).1.le one_le_two)) le_rfl (hδ j hj).2
                  (fun s ω ω' hag => and_congr_right fun hs => forall_congr' fun t =>
                    imp_congr_right fun _ => imp_congr_right fun ht' => by
                      rw [hag t (Fin.lt_def.mpr (lt_of_lt_of_le ht' hs))])
                  (fun s ω hs hk => ⟨fun h => ⟨not_lt.mp fun hc => h s hs hc hk, h⟩, fun h => h.2⟩)
                refine le_trans (le_of_eq ?_) (key2.trans (le_of_eq ?_))
                · congr 3
                  funext ω
                  congr
                · exact Finset.sum_congr rfl fun ω _ => by congr
              · refine hmiss.trans (le_of_eq ?_)
                refine Finset.sum_congr rfl fun ω _ => ?_
                congr 1
                refine Finset.sum_congr rfl fun j _ => ?_
                exact (Finset.sum_boole _ _).symm
            have STUCK :
                ∀ (K T : ℕ) (Q : (Fin T → Fin K × Bool) → ℝ), (∀ ω, 0 ≤ Q ω) →
              (∀ μ : Fin K → ℝ, (∀ i, |μ i| ≤ 1/2) → ∑ ω, (Q ω * ∏ s, (1 + μ (ω s).1 * (if (ω s).2 then (1:ℝ) else -1))) = 1) →
              (∀ μ : Fin K → ℝ, (∀ i, |μ i| ≤ 1/2) → ∀ (t : Fin T) (g : (Fin T → Fin K × Bool) → ℝ) (φ : Fin K × Bool → ℝ),
                (∀ ω ω', (∀ i, i < t → ω i = ω' i) → g ω = g ω') →
                ∑ ω, (Q ω * ∏ s, (1 + μ (ω s).1 * (if (ω s).2 then (1:ℝ) else -1))) * (g ω * (φ (ω t) - ∑ b : Bool, (1 + μ (ω t).1 * (if b then (1:ℝ) else -1)) / 2 * φ ((ω t).1, b))) = 0) →
              ∀ (M : ℕ) (τ : ℕ → ℕ) (δ : ℕ → ℝ) (R : ℝ), 1 < K → 0 < M → τ M < T → 0 ≤ R →
                (∀ ω, Q ω ≠ 0 → switchCost (fun t => ((ω t).1, if (ω t).2 then (1:ℝ) else -1) : BanditHistory K T) 1 T ≤ M * (K - 1)) →
                (∀ j < M, τ j < τ (j+1)) → (∀ j < M, 0 < δ j ∧ δ j ≤ 1/4) → (∀ j < M, δ (M-1) ≤ δ j) →
                (∀ j < M, δ j ^ 2 * (τ j : ℝ) ≤ 1 / (2048 * M)) →
                (∀ j < M, R ≤ δ j ^ 2 * ((τ (j+1) : ℝ) - τ j)) →
                R ≤ δ (M-1) ^ 2 * ((T : ℝ) - τ M) →
                ∃ (μ : Fin K → ℝ) (k : Fin K) (d : ℝ), 0 < d ∧ (∀ i, |μ i| ≤ 1/2) ∧ (∀ i, i ≠ k → μ i + d ≤ μ k) ∧
                R / (64 * M * K) ≤ d * ∑ ω, (Q ω * ∏ s, (1 + μ (ω s).1 * (if (ω s).2 then (1:ℝ) else -1))) * (d * ((Finset.univ.filter (fun t : Fin T => (ω t).1 ≠ k)).card : ℝ)) := by
              clear FIN COMB BRIDGE REDUCE
              classical
              intro K T Q hQ h1 hZ M τ δ R hK hM hτT hR hS hτ hδ hδm hδτ hRw hRT
              have hSC := STUCKCOMB K T
              suffices H : ∀ W : (Fin K → ℝ) → (Fin T → Fin K × Bool) → ℝ,
                  (∀ μ : Fin K → ℝ, (∀ i, |μ i| ≤ 1/2) → ∑ ω, W μ ω = 1) →
                  (∀ μ : Fin K → ℝ, (∀ i, |μ i| ≤ 1/2) → ∀ ω, 0 ≤ W μ ω) →
                  (∀ μ ω, W μ ω ≠ 0 → Q ω ≠ 0) →
                  (∀ (μ0 : Fin K → ℝ) (k : Fin K) (y δ : ℝ) (u : ℕ) (A : (Fin T → Fin K × Bool) → Prop) (As : Fin T → (Fin T → Fin K × Bool) → Prop),
                    (∀ i, |μ0 i| ≤ 1/2) → 0 ≤ μ0 k → μ0 k ≤ y → y ≤ 2 * δ → δ ≤ 1/4 →
                    (∀ s ω ω', (∀ i, i < s → ω i = ω' i) → (As s ω ↔ As s ω')) →
                    (∀ (s : Fin T) ω, u ≤ (s:ℕ) → (ω s).1 = k → (A ω ↔ As s ω)) →
                    ((∑ ω, W μ0 ω * (if A ω then (1:ℝ) else 0)) -
                      32 * δ^2 * ∑ ω, W μ0 ω * ((Finset.univ.filter (fun t : Fin T => (t:ℕ) < u ∧ (ω t).1 = k)).card : ℝ)) / 2 ≤
                    ∑ ω, W (Function.update μ0 k y) ω * (if A ω then (1:ℝ) else 0)) →
                  (∀ (μ0 : Fin K → ℝ) (m : ℝ), 0 < m → (∀ i, 0 ≤ μ0 i) → (∀ j < M, ∀ i, μ0 i ≤ δ j) →
                    (∀ j < M, δ j ^ 2 * (τ j : ℝ) ≤ m / (64 * M)) →
                    m ≤ ∑ ω, W μ0 ω * ∑ j ∈ Finset.range M, ((Finset.univ.filter (fun k : Fin K => ∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → (ω t).1 ≠ k)).card : ℝ) →
                    ∃ (μ : Fin K → ℝ) (k : Fin K) (d : ℝ), 0 < d ∧ (∀ i, |μ i| ≤ 1/2) ∧ (∀ i, i ≠ k → μ i + d ≤ μ k) ∧
                      R * m / (4 * M * K) ≤ d * ∑ ω, W μ ω * (d * ((Finset.univ.filter (fun t : Fin T => (ω t).1 ≠ k)).card : ℝ))) →
                  ∃ (μ : Fin K → ℝ) (k : Fin K) (d : ℝ), 0 < d ∧ (∀ i, |μ i| ≤ 1/2) ∧ (∀ i, i ≠ k → μ i + d ≤ μ k) ∧
                    R / (64 * M * K) ≤ d * ∑ ω, W μ ω * (d * ((Finset.univ.filter (fun t : Fin T => (ω t).1 ≠ k)).card : ℝ)) from
                H (fun μ ω => Q ω * ∏ s, (1 + μ (ω s).1 * (if (ω s).2 then (1:ℝ) else -1))) h1
                  (by
                    intro μ hμ ω
                    refine mul_nonneg (hQ ω) (Finset.prod_nonneg fun s _ => ?_)
                    have := abs_le.mp (hμ (ω s).1)
                    split_ifs <;> linarith only [this.1, this.2])
                  (fun μ ω h h0 => h (by show Q ω * _ = 0; rw [h0, zero_mul]))
                  (LRL K T Q hQ h1 hZ)
                  (fun μ0 m hm a b c e => CORE K T Q hQ h1 hZ M τ δ μ0 m R (Nat.lt_of_succ_lt hK) hM hτT.le hm hR hτ hδ a b c hRw e)
              intro W hW1 hW0 hWQ hLRL hCORE
              clear hZ h1 hQ LRL CORE STUCKCOMB
              -- basic window facts
              have hMlt : M - 1 < M := Nat.sub_lt hM one_pos
              have hM1 : M - 1 + 1 = M := Nat.sub_add_cancel hM
              have huM : τ (M-1) < τ M := by have := hτ (M-1) hMlt; rwa [hM1] at this
              have hMR : (1:ℝ) ≤ M := by exact_mod_cast hM
              have hKR : (2:ℝ) ≤ K := by exact_mod_cast hK
              obtain ⟨hdpos, hd4⟩ := hδ (M-1) hMlt
              have hdu : δ (M-1) ^ 2 * (τ (M-1) : ℝ) ≤ 1 / 2048 := by
                refine (hδτ (M-1) hMlt).trans ?_
                exact one_div_le_one_div_of_le (by norm_num) (by linarith only [hMR])
              -- the events
              let G : Fin K → (Fin T → Fin K × Bool) → Prop := fun l ω =>
                ∃ v, v ≤ τ M ∧ (∀ t : Fin T, τ (M-1) ≤ (t:ℕ) → (t:ℕ) < v → (ω t).1 ≠ l) ∧
                    ∀ i, i ≠ l → ∃ t : Fin T, τ (M-1) ≤ (t:ℕ) ∧ (t:ℕ) < v ∧ (ω t).1 = i
              have hGdisj : ∀ l l' ω, l ≠ l' → G l ω → G l' ω → False := by
                rintro l l' ω hne ⟨v, -, hv1, hv2⟩ ⟨v', -, hv1', hv2'⟩
                rcases le_total v v' with h | h
                · obtain ⟨t, ht1, ht2, ht3⟩ := hv2 l' hne.symm
                  exact hv1' t ht1 (lt_of_lt_of_le ht2 h) ht3
                · obtain ⟨t, ht1, ht2, ht3⟩ := hv2' l hne
                  exact hv1 t ht1 (lt_of_lt_of_le ht2 h) ht3
              have h0b : ∀ i, |(0 : Fin K → ℝ) i| ≤ 1/2 := by intro i; rw [Pi.zero_apply, abs_zero]; exact one_half_pos.le
              -- pick k
              obtain ⟨k, hk⟩ : ∃ k : Fin K, ∑ ω, W 0 ω * (if G k ω then (1:ℝ) else 0) ≤ 1/2 := by
                by_contra hcon
                push Not at hcon
                have ha := hcon ⟨0, by omega⟩
                have hb := hcon ⟨1, hK⟩
                have hsum : ∑ ω, W 0 ω * (if G ⟨0, by omega⟩ ω then (1:ℝ) else 0) +
                    ∑ ω, W 0 ω * (if G ⟨1, hK⟩ ω then (1:ℝ) else 0) ≤ ∑ ω, W 0 ω := by
                  rw [← Finset.sum_add_distrib]
                  refine Finset.sum_le_sum fun ω _ => ?_
                  have hw := hW0 0 h0b ω
                  have := hGdisj ⟨0, by omega⟩ ⟨1, hK⟩ ω (fun h => absurd (congrArg Fin.val h) Nat.zero_ne_one)
                  by_cases hA : G ⟨0, by omega⟩ ω <;> by_cases hB : G ⟨1, hK⟩ ω
                  · exact (this hA hB).elim
                  · rw [if_pos hA, if_neg hB, mul_one, mul_zero, add_zero]
                  · rw [if_neg hA, if_pos hB, mul_one, mul_zero, zero_add]
                  · rw [if_neg hA, if_neg hB, mul_zero, add_zero]
                    exact hw
                rw [hW1 0 h0b] at hsum
                linarith only [hsum, ha, hb]
              set d := δ (M-1) with hd
              obtain ⟨Gc, hGc⟩ : ∃ Gc : (Fin T → Fin K × Bool) → Prop, ∀ ω, Gc ω ↔ ¬ G k ω := ⟨_, fun _ => Iff.rfl⟩
              have hcomplB : ∑ ω, W 0 ω * (if Gc ω then (1:ℝ) else 0) ≥ 1/2 := by
                have : ∑ ω, W 0 ω * (if Gc ω then (1:ℝ) else 0) + ∑ ω, W 0 ω * (if G k ω then (1:ℝ) else 0) = ∑ ω, W 0 ω := by
                  rw [← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl fun ω _ => ?_
                  by_cases hA : G k ω
                  · rw [if_neg (show ¬ Gc ω from fun hh => (hGc ω).mp hh hA), if_pos hA, mul_zero, mul_one, zero_add]
                  · rw [if_pos ((hGc ω).mpr hA), if_neg hA, mul_zero, mul_one, add_zero]
                rw [hW1 0 h0b] at this
                linarith only [this, hk]
              obtain ⟨μ1, hμ1⟩ : ∃ μ1 : Fin K → ℝ, μ1 = Function.update (0 : Fin K → ℝ) k d := ⟨_, rfl⟩
              have hμ1k : μ1 k = d := by rw [hμ1, Function.update_self]
              have hμ1ne : ∀ i, i ≠ k → μ1 i = 0 := fun i h => by rw [hμ1, Function.update_of_ne h]; rfl
              have hμ1nn : ∀ i, 0 ≤ μ1 i := by
                intro i
                by_cases h : i = k
                · rw [h, hμ1k]; exact hdpos.le
                · rw [hμ1ne i h]
              have hμ1le : ∀ i, μ1 i ≤ d := by
                intro i
                by_cases h : i = k
                · rw [h, hμ1k]
                · rw [hμ1ne i h]; exact hdpos.le
              have hd2 : d ≤ 1/2 := hd4.trans (by norm_num)
              have hμ1b : ∀ i, |μ1 i| ≤ 1/2 := by
                intro i
                rw [abs_of_nonneg (hμ1nn i)]
                exact (hμ1le i).trans hd2
              have hG1 : 1/8 ≤ ∑ ω, W μ1 ω * (if Gc ω then (1:ℝ) else 0) := by
                have key := hLRL 0 k d d (τ (M-1)) Gc
                  (fun s ω => ¬ ∃ v, v ≤ (s:ℕ) ∧ v ≤ τ M ∧ (∀ t : Fin T, τ (M-1) ≤ (t:ℕ) → (t:ℕ) < v → (ω t).1 ≠ k) ∧
                    ∀ i, i ≠ k → ∃ t : Fin T, τ (M-1) ≤ (t:ℕ) ∧ (t:ℕ) < v ∧ (ω t).1 = i)
                  h0b le_rfl hdpos.le (by linarith only [hdpos]) hd4
                  (by
                    have aux : ∀ (s : Fin T) (ω ω' : Fin T → Fin K × Bool), (∀ i, i < s → ω i = ω' i) →
                      (∃ v, v ≤ (s:ℕ) ∧ v ≤ τ M ∧ (∀ t : Fin T, τ (M-1) ≤ (t:ℕ) → (t:ℕ) < v → (ω t).1 ≠ k) ∧
                        ∀ i, i ≠ k → ∃ t : Fin T, τ (M-1) ≤ (t:ℕ) ∧ (t:ℕ) < v ∧ (ω t).1 = i) →
                      (∃ v, v ≤ (s:ℕ) ∧ v ≤ τ M ∧ (∀ t : Fin T, τ (M-1) ≤ (t:ℕ) → (t:ℕ) < v → (ω' t).1 ≠ k) ∧
                        ∀ i, i ≠ k → ∃ t : Fin T, τ (M-1) ≤ (t:ℕ) ∧ (t:ℕ) < v ∧ (ω' t).1 = i) := by
                      rintro s ω ω' hag ⟨v, hvs, hvM, hv1, hv2⟩
                      refine ⟨v, hvs, hvM, fun t ht1 ht2 => ?_, fun i hi => ?_⟩
                      · rw [← hag t (Fin.lt_def.mpr (lt_of_lt_of_le ht2 hvs))]
                        exact hv1 t ht1 ht2
                      · obtain ⟨t, ht1, ht2, ht3⟩ := hv2 i hi
                        refine ⟨t, ht1, ht2, ?_⟩
                        rw [← hag t (Fin.lt_def.mpr (lt_of_lt_of_le ht2 hvs))]
                        exact ht3
                    intro s ω ω' hag
                    exact not_congr ⟨aux s ω ω' hag, aux s ω' ω (fun i hi => (hag i hi).symm)⟩)
                  (by
                    intro s ω hus hsk
                    refine (hGc ω).trans (not_congr ⟨?_, ?_⟩)
                    · rintro ⟨v, hvM, hv1, hv2⟩
                      refine ⟨v, ?_, hvM, hv1, hv2⟩
                      by_contra hlt
                      exact hv1 s hus (not_le.mp hlt) hsk
                    · rintro ⟨v, -, hvM, hv1, hv2⟩
                      exact ⟨v, hvM, hv1, hv2⟩)
                have hN : ∑ ω, W 0 ω * ((Finset.univ.filter (fun t : Fin T => (t:ℕ) < τ (M-1) ∧ (ω t).1 = k)).card : ℝ)
                    ≤ (τ (M-1) : ℝ) := by
                  calc _ ≤ ∑ ω, W 0 ω * (τ (M-1) : ℝ) := by
                        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (hW0 0 h0b ω)
                        have hc : (Finset.univ.filter (fun t : Fin T => (t:ℕ) < τ (M-1) ∧ (ω t).1 = k)).card ≤
                            (Finset.range (τ (M-1))).card := by
                          refine Finset.card_le_card_of_injOn (fun t => (t:ℕ)) ?_ ?_
                          · intro t ht
                            exact Finset.mem_coe.mpr (Finset.mem_range.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).2.1)
                          · intro a _ b _ hab
                            exact Fin.ext hab
                        rw [Finset.card_range] at hc
                        exact Nat.cast_le.mpr hc
                    _ = (τ (M-1) : ℝ) := by rw [← Finset.sum_mul, hW1 0 h0b, one_mul]
                have key' : ((∑ ω, W 0 ω * (if Gc ω then (1:ℝ) else 0)) -
                    32 * d^2 * ∑ ω, W 0 ω * ((Finset.univ.filter (fun t : Fin T => (t:ℕ) < τ (M-1) ∧ (ω t).1 = k)).card : ℝ)) / 2
                    ≤ ∑ ω, W μ1 ω * (if Gc ω then (1:ℝ) else 0) := by
                  rw [hμ1]; exact key
                clear key
                have h32 : 32 * d^2 * ∑ ω, W 0 ω * ((Finset.univ.filter (fun t : Fin T => (t:ℕ) < τ (M-1) ∧ (ω t).1 = k)).card : ℝ)
                    ≤ 32 * (d^2 * (τ (M-1) : ℝ)) := by
                  rw [← mul_assoc]
                  exact mul_le_mul_of_nonneg_left hN (mul_nonneg (by norm_num) (sq_nonneg d))
                clear hN
                refine le_trans ?_ key'
                linarith only [h32, hdu, hcomplB]
              -- events under P^{(k)}
              let Mi : (Fin T → Fin K × Bool) → Prop := fun ω => ∃ j < M, ∃ k : Fin K, ∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → (ω t).1 ≠ k
              let St : (Fin T → Fin K × Bool) → Prop := fun ω => ∃ l : Fin K, l ≠ k ∧ ∀ t : Fin T, τ M ≤ (t:ℕ) → (ω t).1 = l
              have hif : ∀ (p : Prop) [Decidable p], (0:ℝ) ≤ if p then (1:ℝ) else 0 := by
                intro p _
                split_ifs
                · exact zero_le_one
                · exact le_rfl
              have hcover : ∀ ω, W μ1 ω * (if Gc ω then (1:ℝ) else 0) ≤
                  W μ1 ω * (if Mi ω then (1:ℝ) else 0) + W μ1 ω * (if St ω then (1:ℝ) else 0) := by
                intro ω
                have hw := hW0 μ1 hμ1b ω
                by_cases hw0 : W μ1 ω = 0
                · rw [hw0, zero_mul, zero_mul, zero_mul, add_zero]
                by_cases hG : G k ω
                · rw [if_neg (show ¬ Gc ω from fun hh => (hGc ω).mp hh hG), mul_zero]
                  exact add_nonneg (mul_nonneg hw (hif _)) (mul_nonneg hw (hif _))
                · rcases hSC ω M τ hK hM hτ hτT (hS ω (hWQ μ1 ω hw0)) with hmi | ⟨l, hl, hGl⟩
                  · have hmi' : Mi ω := hmi
                    rw [if_pos ((hGc ω).mpr hG), if_pos hmi']
                    exact le_add_of_nonneg_right (mul_nonneg hw (hif _))
                  · have hst : St ω := by
                      refine ⟨l, ?_, hl⟩
                      rintro rfl
                      exact hG hGl
                    rw [if_pos ((hGc ω).mpr hG), if_pos hst]
                    exact le_add_of_nonneg_left (mul_nonneg hw (hif _))
              have hcover' := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => hcover ω)
              rw [Finset.sum_add_distrib] at hcover'
              by_cases hcase : 1/16 ≤ ∑ ω, W μ1 ω * (if St ω then (1:ℝ) else 0)
              · -- stuck on a wrong arm
                refine ⟨μ1, k, d, hdpos, hμ1b, ?_, ?_⟩
                · intro i hi
                  rw [hμ1ne i hi, hμ1k, zero_add]
                · have hTM : (0:ℝ) < (T:ℝ) - τ M := by
                    exact sub_pos.mpr (Nat.cast_lt.mpr hτT)
                  have hcard : ∀ ω, St ω → (T:ℝ) - τ M ≤ ((Finset.univ.filter (fun t : Fin T => (ω t).1 ≠ k)).card : ℝ) := by
                    rintro ω ⟨l, hlk, hl⟩
                    have hc : (Finset.Ico (τ M) T).card ≤ (Finset.univ.filter (fun t : Fin T => (ω t).1 ≠ k)).card := by
                      refine Finset.card_le_card_of_surjOn (fun t : Fin T => (t:ℕ)) ?_
                      intro n hn
                      rw [Finset.mem_coe, Finset.mem_Ico] at hn
                      refine ⟨⟨n, hn.2⟩, ?_, rfl⟩
                      rw [Finset.mem_coe, Finset.mem_filter]
                      refine ⟨Finset.mem_univ _, ?_⟩
                      rw [hl ⟨n, hn.2⟩ hn.1]
                      exact hlk
                    rw [Nat.card_Ico] at hc
                    have hc' : ((T - τ M : ℕ) : ℝ) ≤ ((Finset.univ.filter (fun t : Fin T => (ω t).1 ≠ k)).card : ℝ) := Nat.cast_le.mpr hc
                    rwa [Nat.cast_sub hτT.le] at hc'
                  have hlow : d * ((T:ℝ) - τ M) * ∑ ω, W μ1 ω * (if St ω then (1:ℝ) else 0) ≤
                      ∑ ω, W μ1 ω * (d * ((Finset.univ.filter (fun t : Fin T => (ω t).1 ≠ k)).card : ℝ)) := by
                    rw [Finset.mul_sum]
                    refine Finset.sum_le_sum fun ω _ => ?_
                    have hw := hW0 μ1 hμ1b ω
                    by_cases hst : St ω
                    · rw [if_pos hst]
                      rw [mul_one, mul_comm]
                      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hcard ω hst) hdpos.le) hw
                    · rw [if_neg hst]
                      rw [mul_zero, mul_zero]
                      exact mul_nonneg hw (mul_nonneg hdpos.le (Nat.cast_nonneg _))
                  have hfin : R / (64 * M * K) ≤ d * ∑ ω, W μ1 ω * (d * ((Finset.univ.filter (fun t : Fin T => (ω t).1 ≠ k)).card : ℝ)) := by
                    have e1 : d * (d * ((T:ℝ) - τ M) * ∑ ω, W μ1 ω * (if St ω then (1:ℝ) else 0)) ≤
                      d * ∑ ω, W μ1 ω * (d * ((Finset.univ.filter (fun t : Fin T => (ω t).1 ≠ k)).card : ℝ)) :=
                      mul_le_mul_of_nonneg_left hlow hdpos.le
                    have e2 : R * (1/16) ≤ (d^2 * ((T:ℝ) - τ M)) * ∑ ω, W μ1 ω * (if St ω then (1:ℝ) else 0) :=
                      mul_le_mul hRT hcase (by norm_num) (mul_nonneg (sq_nonneg d) hTM.le)
                    have e3 : R / (64 * M * K) ≤ R * (1/16) := by
                      have hMK : (2:ℝ) ≤ M * K := by
                        have := mul_le_mul hMR hKR zero_le_two (zero_le_one.trans hMR)
                        rwa [one_mul] at this
                      have h16 : (16:ℝ) ≤ 64 * M * K := by rw [mul_assoc]; linarith only [hMK]
                      rw [div_eq_mul_one_div]
                      exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by norm_num) h16) hR
                    calc _ ≤ _ := e3
                      _ ≤ _ := e2
                      _ = _ := by rw [sq, mul_assoc d d, mul_assoc d]
                      _ ≤ _ := e1
                  exact hfin
              · -- missed pairs
                push Not at hcase
                have hMi : 1/16 ≤ ∑ ω, W μ1 ω * (if Mi ω then (1:ℝ) else 0) := by linarith only [hcover', hcase, hG1]
                have hmiss : 1/16 ≤ ∑ ω, W μ1 ω * ∑ j ∈ Finset.range M, ((Finset.univ.filter (fun k : Fin K => ∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → (ω t).1 ≠ k)).card : ℝ) := by
                  refine hMi.trans (Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (hW0 μ1 hμ1b ω))
                  by_cases hmi : Mi ω
                  · rw [if_pos hmi]
                    obtain ⟨j, hj, k', hk'⟩ := hmi
                    have hc : 1 ≤ (Finset.univ.filter (fun k : Fin K => ∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → (ω t).1 ≠ k)).card := by
                      refine Finset.card_pos.mpr ⟨k', ?_⟩
                      rw [Finset.mem_filter]
                      exact ⟨Finset.mem_univ _, hk'⟩
                    calc (1:ℝ) ≤ ((Finset.univ.filter (fun k : Fin K => ∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → (ω t).1 ≠ k)).card : ℝ) := by rw [← Nat.cast_one]; exact Nat.cast_le.mpr hc
                      _ ≤ _ := Finset.single_le_sum (f := fun j => ((Finset.univ.filter (fun k : Fin K => ∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → (ω t).1 ≠ k)).card : ℝ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_range.mpr hj)
                  · rw [if_neg hmi]
                    exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
                obtain ⟨μ, k', d', hd', hμ, hgap, hval⟩ := hCORE μ1 (1/16) (by norm_num) hμ1nn
                  (fun j hj i => (hμ1le i).trans (hδm j hj))
                  (fun j hj => (hδτ j hj).trans (by rw [div_div]; exact one_div_le_one_div_of_le (by linarith only [hMR]) (by linarith only [hMR]))) hmiss
                refine ⟨μ, k', d', hd', hμ, hgap, le_trans (le_of_eq ?_) hval⟩
                rw [mul_one_div, div_div]
                congr 1
                ring
            clear BRIDGE LRL STUCKCOMB
            classical
            obtain ⟨C, hC, hFIN⟩ := FIN
            refine ⟨C, hC, fun K S T hK hT π hπ => ?_⟩
            obtain ⟨Q, hQ, h1, hZ, hS, hgap⟩ := REDUCE K S T π hπ
            clear REDUCE
            have hK0 : 0 < K := Nat.lt_of_succ_lt hK
            have hKR : (2:ℝ) ≤ K := Nat.ofNat_le_cast.mpr hK
            have hKpos : (0:ℝ) < K := lt_of_lt_of_le two_pos hKR
            -- choice of gaps
            have hdel : ∀ (a τ D R : ℝ), 0 < a → R ≤ D/16 → R * τ ≤ a * D →
                0 < Real.sqrt (a / max (16*a) τ) ∧ Real.sqrt (a / max (16*a) τ) ≤ 1/4 ∧
                (Real.sqrt (a / max (16*a) τ))^2 * τ ≤ a ∧ R ≤ (Real.sqrt (a / max (16*a) τ))^2 * D := by
              intro a τ D R ha h16 hR
              have h16a : 0 < 16 * a := mul_pos (by norm_num) ha
              have hmax : 0 < max (16*a) τ := lt_max_of_lt_left h16a
              have hq : 0 < a / max (16*a) τ := div_pos ha hmax
              refine ⟨Real.sqrt_pos.mpr hq, ?_, ?_, ?_⟩
              · rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ hmax]
                exact (show a = (1/4)^2 * (16*a) by ring).le.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg _))
              · rw [Real.sq_sqrt hq.le, div_mul_eq_mul_div, div_le_iff₀ hmax]
                exact mul_le_mul_of_nonneg_left (le_max_right _ _) ha.le
              · rw [Real.sq_sqrt hq.le, div_mul_eq_mul_div, le_div_iff₀ hmax]
                rcases max_choice (16*a) τ with h | h <;> rw [h]
                · refine (show R * (16*a) = a * (R * 16) by ring).le.trans (mul_le_mul_of_nonneg_left ?_ ha.le)
                  exact (le_div_iff₀ (by norm_num)).mp h16
                · exact hR
            have hgoal : ∀ (Y : EReal), (∀ (μ : Fin K → ℝ) (k : Fin K) (d : ℝ), 0 < d → (∀ i, |μ i| ≤ 1/2) → (∀ i, i ≠ k → μ i + d ≤ μ k) → 1 < K →
                ((d * ∑ ω, (Q ω * ∏ s, (1 + μ (ω s).1 * (if (ω s).2 then (1:ℝ) else -1))) * (d * ((Finset.univ.filter (fun t : Fin T => (ω t).1 ≠ k)).card : ℝ)) : ℝ) : EReal) ≤ Y) →
                ((C / Real.log T * max (gapRateA K S T) (gapRateBLower K S T) : ℝ) : EReal) ≤ Y := by
              intro Y hY
              have coreX : ∀ (M : ℕ) (τ : ℕ → ℕ) (δ : ℕ → ℝ) (m R : ℝ), 0 < M → τ M ≤ T → 0 < m → 0 ≤ R →
                  (∀ j < M, τ j < τ (j+1)) → (∀ j < M, 0 < δ j ∧ δ j ≤ 1/4) →
                  (∀ j < M, δ j ^ 2 * (τ j : ℝ) ≤ m / (64 * M)) →
                  (∀ j < M, R ≤ δ j ^ 2 * ((τ (j+1) : ℝ) - τ j)) →
                  (∀ ω, Q ω ≠ 0 → m ≤ ∑ j ∈ Finset.range M, ((Finset.univ.filter (fun k : Fin K => ∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → (ω t).1 ≠ k)).card : ℝ)) →
                  ((R * m / (4 * M * K) : ℝ) : EReal) ≤ Y := by
                intro M τ δ m R hM hτM hm hR hτ hδ hδτ hRδ hmiss
                have hzero : ∀ i : Fin K, |(0 : Fin K → ℝ) i| ≤ 1/2 := fun i => by
                  rw [Pi.zero_apply, abs_zero]; norm_num
                obtain ⟨μ, k, d, hd, hμ, hk, hv⟩ := CORE K T Q hQ h1 hZ M τ δ 0 m R hK0 hM hτM hm hR hτ hδ
                  (fun i => le_rfl) (fun j hj i => (hδ j hj).1.le) hδτ hRδ (by
                    have hone := h1 0 hzero
                    refine ((one_mul m).symm.trans (congrArg₂ (HMul.hMul : ℝ → ℝ → ℝ) hone.symm rfl)).le.trans ?_
                    rw [Finset.sum_mul]
                    refine Finset.sum_le_sum fun ω _ => ?_
                    by_cases hq : Q ω = 0
                    · simp only [hq, zero_mul, le_refl]
                    · refine mul_le_mul_of_nonneg_left (hmiss ω hq) (mul_nonneg (hQ ω) (Finset.prod_nonneg fun s _ => ?_))
                      rw [Pi.zero_apply, zero_mul, add_zero]
                      exact zero_le_one)
                exact le_trans (EReal.coe_le_coe_iff.mpr hv) (hY μ k d hd hμ hk hK)
              have stuckX : ∀ (M : ℕ) (τ : ℕ → ℕ) (δ : ℕ → ℝ) (R : ℝ), 0 < M → τ M < T → 0 ≤ R → S = M * (K - 1) →
                  (∀ j < M, τ j < τ (j+1)) → (∀ j < M, 0 < δ j ∧ δ j ≤ 1/4) → (∀ j < M, δ (M-1) ≤ δ j) →
                  (∀ j < M, δ j ^ 2 * (τ j : ℝ) ≤ 1 / (2048 * M)) →
                  (∀ j < M, R ≤ δ j ^ 2 * ((τ (j+1) : ℝ) - τ j)) →
                  R ≤ δ (M-1) ^ 2 * ((T : ℝ) - τ M) → ((R / (64 * M * K) : ℝ) : EReal) ≤ Y := by
                intro M τ δ R hM hτM hR hSM hτ hδ hδm hδτ hRδ hRT
                obtain ⟨μ, k, d, hd, hμ, hk, hv⟩ := STUCK K T Q hQ h1 hZ M τ δ R hK hM hτM hR
                  (fun ω hω => hSM ▸ hS ω hω) hτ hδ hδm hδτ hRδ hRT
                exact le_trans (EReal.coe_le_coe_iff.mpr hv) (hY μ k d hd hμ hk hK)
              clear hY hgap h1 hZ CORE STUCK
              have hT0 : (((K : ℝ) / 384 : ℝ) : EReal) ≤ Y := by
                have h3 : K ≤ 3 * (K/2) := by omega
                have hk3 : ((K/2 : ℕ) : ℝ) ≤ (K:ℝ)/2 := Nat.cast_div_le
                have h1' : 1 ≤ K/2 := Nat.div_pos hK two_pos
                have h4 : 1 * (K/2) ≤ T := (one_mul _).trans_le ((Nat.div_le_self K 2).trans ((Nat.le_mul_of_pos_left _ two_pos).trans hT))
                have hle := Nat.div_le_self K 2
                generalize K/2 = n at h3 hk3 h1' h4 hle
                have hk2 : (K:ℝ) ≤ 3 * (n:ℝ) := (Nat.cast_le.mpr h3).trans_eq (by rw [Nat.cast_mul, Nat.cast_ofNat])
                have hn : (0:ℝ) < n := Nat.cast_pos.mpr h1'
                have hcard : ∀ a : Fin T → Fin K, (K:ℝ)/2 ≤
                    ((Finset.univ.filter (fun k : Fin K => ∀ t : Fin T, 0 * n ≤ (t:ℕ) → (t:ℕ) < (0+1) * n → a t ≠ k)).card : ℝ) := by
                  intro a
                  have hsub : (Finset.univ.filter (fun k : Fin K => ¬ ∀ t : Fin T, 0 * n ≤ (t:ℕ) → (t:ℕ) < (0+1) * n → a t ≠ k)).card ≤ n := by
                    have : (Finset.univ.filter (fun k : Fin K => ¬ ∀ t : Fin T, 0 * n ≤ (t:ℕ) → (t:ℕ) < (0+1) * n → a t ≠ k)) ⊆
                        (Finset.range n).attach.image (fun t => a ⟨t.1, lt_of_lt_of_le (Finset.mem_range.mp t.2) (by rwa [one_mul] at h4)⟩) := by
                      intro k hk
                      rw [Finset.mem_filter] at hk
                      obtain ⟨t, ht⟩ := not_forall.mp hk.2
                      obtain ⟨_, ht⟩ := not_forall.mp ht
                      obtain ⟨ht, hk⟩ := not_forall.mp ht
                      rw [zero_add, one_mul] at ht
                      exact Finset.mem_image.mpr ⟨⟨t, Finset.mem_range.mpr ht⟩, Finset.mem_attach _ _, not_not.mp hk⟩
                    exact (Finset.card_le_card this).trans (Finset.card_image_le.trans (by rw [Finset.card_attach, Finset.card_range]))
                  have hadd := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin K)))
                    (fun k : Fin K => ∀ t : Fin T, 0 * n ≤ (t:ℕ) → (t:ℕ) < (0+1) * n → a t ≠ k)
                  rw [Finset.card_univ, Fintype.card_fin] at hadd
                  have hge : K ≤ (Finset.univ.filter (fun k : Fin K => ∀ t : Fin T, 0 * n ≤ (t:ℕ) → (t:ℕ) < (0+1) * n → a t ≠ k)).card + n :=
                    hadd.symm.le.trans (Nat.add_le_add_left hsub _)
                  have hge2 := (Nat.cast_le (α := ℝ)).mpr hge
                  rw [Nat.cast_add] at hge2
                  exact le_of_add_le_add_right (((add_le_add le_rfl hk3).trans_eq (add_halves _)).trans hge2)
                have := coreX 1 (fun j => j * n) (fun _ => 1/4) ((K:ℝ)/2) ((1/4)^2 * (n:ℝ)) one_pos h4 (half_pos hKpos)
                  (mul_nonneg (sq_nonneg _) hn.le)
                  (fun j _ => Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self j) h1') (fun j _ => ⟨by norm_num, le_rfl⟩)
                  (fun j hj => by
                    rw [Nat.lt_one_iff.mp hj, Nat.zero_mul, Nat.cast_zero, mul_zero, Nat.cast_one]
                    exact div_nonneg (half_pos hKpos).le (by norm_num))
                  (fun j hj => by
                    rw [Nat.lt_one_iff.mp hj, Nat.zero_mul, Nat.cast_zero, Nat.zero_add, Nat.one_mul, sub_zero])
                  (fun ω _ => by
                    rw [Finset.sum_range_one]
                    exact hcard (fun t => (ω t).1))
                refine le_trans (EReal.coe_le_coe_iff.mpr ?_) this
                rw [Nat.cast_one, mul_one, le_div_iff₀ (mul_pos (by norm_num) hKpos)]
                refine (show (K:ℝ)/384 * (4*K) = K * K * (1/96) by ring).le.trans (le_trans (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hk2 hKpos.le) (by norm_num)) (le_of_eq ?_))
                ring
              have hne_bot : Y ≠ ⊥ := fun h => by
                rw [h] at hT0
                exact absurd hT0 (not_le.mpr (EReal.bot_lt_coe _))
              rcases eq_or_ne Y ⊤ with htop | hne_top
              · rw [htop]; exact le_top
              obtain ⟨X, hX⟩ : ∃ X : ℝ, Y = (X : EReal) := ⟨_, (EReal.coe_toReal hne_top hne_bot).symm⟩
              subst hX
              refine EReal.coe_le_coe_iff.mpr (hFIN K S T X hK hT (EReal.coe_le_coe_iff.mp hT0) ?_ ?_)
              · clear hFIN stuckX hT0
                intro M τ R hM hτ hτT hR hSM h16 h64
                have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
                have ecast : ((M * (K - 1) : ℕ) : ℝ) = (M:ℝ) * ((K:ℝ) - 1) := by
                  rw [Nat.cast_mul, Nat.cast_sub hK0, Nat.cast_one]
                have hmpos : (0:ℝ) < (M : ℝ) * ((K : ℝ) - 1) - S := by
                  rw [← ecast]
                  exact sub_pos.mpr (Nat.cast_lt.mpr hSM)
                have hmle : ∀ ω, Q ω ≠ 0 → (M : ℝ) * ((K : ℝ) - 1) - S ≤ ∑ j ∈ Finset.range M, ((Finset.univ.filter (fun k : Fin K => ∀ t : Fin T, τ j ≤ (t:ℕ) → (t:ℕ) < τ (j+1) → (ω t).1 ≠ k)).card : ℝ) := by
                  intro ω hω
                  have hc := (Nat.cast_le (α := ℝ)).mpr (COMB K T S ω M τ hK0 hτ hτT (hS ω hω))
                  rw [Nat.cast_add, Nat.cast_sum, ecast] at hc
                  exact sub_le_iff_le_add'.mpr hc
                generalize (M : ℝ) * ((K : ℝ) - 1) - S = m at hmpos hmle h64 ⊢
                have h64M : (0:ℝ) < 64 * M := mul_pos (by norm_num) hMR
                have ha : 0 < m / (64 * M) := div_pos hmpos h64M
                have hd := fun j (hj : j < M) => hdel (m / (64*M)) (τ j) ((τ (j+1) : ℝ) - τ j) R ha (h16 j hj)
                  (by
                    rw [div_mul_eq_mul_div, le_div_iff₀ h64M, mul_assoc, mul_comm (τ j : ℝ)]
                    exact h64 j hj)
                exact EReal.coe_le_coe_iff.mp (coreX M τ (fun j => Real.sqrt (m / (64*M) / max (16*(m/(64*M))) (τ j))) m R hM hτT hmpos hR hτ
                  (fun j hj => ⟨(hd j hj).1, (hd j hj).2.1⟩) (fun j hj => (hd j hj).2.2.1) (fun j hj => (hd j hj).2.2.2) hmle)
              · clear hFIN coreX hT0
                intro M τ R hM hτ hτT hR hSM h16 h20 hT16 hT20
                have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
                have hM20 : (0:ℝ) < 2048 * M := mul_pos (by norm_num) hMR
                have ha : (0:ℝ) < 1 / (2048 * M) := div_pos one_pos hM20
                have hmono' : ∀ j < M, τ j ≤ τ (M-1) := by
                  have hmo : ∀ i j, j + i < M → τ j ≤ τ (j+i) := by
                    intro i
                    induction i with
                    | zero => intro j _; exact le_rfl
                    | succ i ih => exact fun j hi => (ih j (Nat.lt_of_succ_lt hi)).trans (hτ (j+i) (Nat.lt_of_succ_lt hi)).le
                  intro j hj
                  have hje : j + (M - 1 - j) = M - 1 := Nat.add_sub_cancel' (Nat.le_sub_one_of_lt hj)
                  have := hmo (M - 1 - j) j (by rw [hje]; exact Nat.sub_lt hM one_pos)
                  rwa [hje] at this
                have hconv : ∀ x D : ℝ, R * (2048 * M * x) ≤ D → R * x ≤ 1 / (2048 * M) * D := fun x D h => by
                  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hM20, mul_assoc, mul_comm x]
                  exact h
                have hd := fun j (hj : j < M) => hdel (1 / (2048*M)) (τ j) ((τ (j+1) : ℝ) - τ j) R ha (h16 j hj) (hconv _ _ (h20 j hj))
                have hdT := hdel (1 / (2048*M)) (τ (M-1)) ((T : ℝ) - τ M) R ha hT16 (hconv _ _ hT20)
                have ha16 : (0:ℝ) < 16 * (1 / (2048 * M)) := mul_pos (by norm_num) ha
                exact EReal.coe_le_coe_iff.mp (stuckX M τ (fun j => Real.sqrt ((1:ℝ) / (2048*(M:ℝ)) / max (16*((1:ℝ)/(2048*(M:ℝ)))) (τ j : ℝ))) R hM hτT hR
                  hSM hτ (fun j hj => ⟨(hd j hj).1, (hd j hj).2.1⟩)
                  (fun j hj => Real.sqrt_le_sqrt (div_le_div_of_nonneg_left ha.le (lt_max_of_lt_left ha16)
                    (max_le_max le_rfl (Nat.cast_le.mpr (hmono' j hj)))))
                  (fun j hj => (hd j hj).2.2.1) (fun j hj => (hd j hj).2.2.2) hdT.2.2.2)
            refine hgoal _ fun μ k d hd hμ hk hK => ?_
            obtain ⟨ν, hν, hle⟩ := hgap μ k d hd hμ hk hK
            unfold gapWeightedWorstRegret
            exact le_trans (EReal.coe_le_coe_iff.mpr hle)
              (le_iSup (fun ν : {ν : StochasticBandit K // AdmissibleEnvironment ν} =>
                ((sourceGap ν.val * banditRegret ν.val π T : ℝ) : EReal)) ⟨ν, hν⟩)
