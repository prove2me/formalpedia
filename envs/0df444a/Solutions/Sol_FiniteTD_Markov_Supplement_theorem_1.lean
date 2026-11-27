-- Prove2me | solution 1 for FiniteTD.Markov.Supplement.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:09:17.92351+00:00
-- url     : https://prove2.me/submissions/383c3192-5e8b-4597-b9e3-48869fc0fd91

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_MeanPathIid

open FiniteTD
open FiniteTD.Markov
open FiniteTD.Markov.Supplement

theorem solution {S : Type} [Fintype S] [Nonempty S] {d : ℕ} [NeZero d]
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (ω : ℝ) (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hω : IsMinEig π φ ω) (hω0 : 0 < ω)
    (hstar : gbar π P γ Rw φ θstar = 0) :
    -- averaged iterate
    (∀ T : ℕ, 1 ≤ T →
      dNormSq π φ (θstar - avgSeq (meanPath π P γ Rw φ ((1 - γ) / 4) θ0) T) ≤
        4 * ‖θstar - θ0‖ ^ 2 / (T * (1 - γ) ^ 2)) ∧
    -- last iterate
    (∀ T : ℕ,
      ‖θstar - meanPath π P γ Rw φ ((1 - γ) / 4) θ0 T‖ ^ 2 ≤
        Real.exp (-((1 - γ) ^ 2 * ω / 4) * T) * ‖θstar - θ0‖ ^ 2) := by
          have hw0 : ∀ p : S × S, 0 ≤ π p.1 * P p.1 p.2 := fun p => mul_nonneg (hπ.1 _) (hP.1 _ _)
          have h1 : ∀ f : S → ℝ, ∑ p : S × S, π p.1 * P p.1 p.2 * f p.1 = ∑ s, π s * f s := by
            intro f
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun s _ => ?_
            dsimp only
            rw [← Finset.sum_mul, ← Finset.mul_sum, hP.2 s, mul_one]
          have h2 : ∀ f : S → ℝ, ∑ p : S × S, π p.1 * P p.1 p.2 * f p.2 = ∑ s, π s * f s := by
            intro f
            rw [Fintype.sum_prod_type, Finset.sum_comm]
            refine Finset.sum_congr rfl fun s _ => ?_
            dsimp only
            rw [← Finset.sum_mul, hπ.2.2 s]
          have hw1 : ∑ p : S × S, π p.1 * P p.1 p.2 = 1 := by
            have := h1 (fun _ => 1)
            simpa [hπ.2.1] using this
          have key : ∀ θ, gbar π P γ Rw φ θ = ∑ p : S × S, (π p.1 * P p.1 p.2 *
              (inner ℝ (φ p.1) (θstar - θ) - γ * inner ℝ (φ p.2) (θstar - θ))) • φ p.1 := by
            intro θ
            have : gbar π P γ Rw φ θ = gbar π P γ Rw φ θ - gbar π P γ Rw φ θstar := by
              rw [hstar, sub_zero]
            rw [this, gbar, gbar, ← Finset.sum_sub_distrib, Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun s' _ => ?_
            simp only [tdDir, smul_smul, ← sub_smul, inner_sub_right]
            congr 1; ring
          have hD0 : ∀ e, 0 ≤ dNormSq π φ e := fun e =>
            Finset.sum_nonneg fun s _ => mul_nonneg (hπ.1 s) (sq_nonneg _)
          have hinner : ∀ θ, (1 - γ) * dNormSq π φ (θstar - θ) ≤
              inner ℝ (θstar - θ) (gbar π P γ Rw φ θ) := by
            intro θ
            rw [key θ, inner_sum]
            simp only [real_inner_smul_right]
            have hc : ∀ s, inner ℝ (θstar - θ) (φ s) = inner ℝ (φ s) (θstar - θ) :=
              fun s => real_inner_comm _ _
            simp only [hc]
            set u : S → ℝ := fun s => inner ℝ (φ s) (θstar - θ) with hu
            have hD : dNormSq π φ (θstar - θ) = ∑ s, π s * u s ^ 2 := rfl
            have e1 := h1 (fun s => u s ^ 2)
            have e2 := h2 (fun s => u s ^ 2)
            have hcross : ∑ p : S × S, π p.1 * P p.1 p.2 * (u p.1 * u p.2) ≤ ∑ s, π s * u s ^ 2 := by
              have : ∑ p : S × S, π p.1 * P p.1 p.2 * (u p.1 * u p.2) ≤ ∑ p : S × S,
                  ((π p.1 * P p.1 p.2 * u p.1 ^ 2) + (π p.1 * P p.1 p.2 * u p.2 ^ 2)) / 2 := by
                refine Finset.sum_le_sum fun p _ => ?_
                have := hw0 p
                nlinarith [mul_nonneg this (sq_nonneg (u p.1 - u p.2))]
              rw [← Finset.sum_div, Finset.sum_add_distrib, e1, e2] at this
              linarith
            have hsplit : ∑ p : S × S, π p.1 * P p.1 p.2 * (u p.1 - γ * u p.2) * u p.1 =
                ∑ p : S × S, π p.1 * P p.1 p.2 * u p.1 ^ 2 -
                  γ * ∑ p : S × S, π p.1 * P p.1 p.2 * (u p.1 * u p.2) := by
              rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun p _ => ?_
              ring
            rw [hsplit, e1, hD]
            nlinarith [mul_le_mul_of_nonneg_left hcross hγ0]
          have hnorm : ∀ θ, ‖gbar π P γ Rw φ θ‖ ^ 2 ≤ 4 * dNormSq π φ (θstar - θ) := by
            intro θ
            rw [key θ]
            set u : S → ℝ := fun s => inner ℝ (φ s) (θstar - θ) with hu
            have hD : dNormSq π φ (θstar - θ) = ∑ s, π s * u s ^ 2 := rfl
            have e1 := h1 (fun s => u s ^ 2)
            have e2 := h2 (fun s => u s ^ 2)
            have hle : ‖∑ p : S × S, (π p.1 * P p.1 p.2 * (u p.1 - γ * u p.2)) • φ p.1‖ ≤
                ∑ p : S × S, π p.1 * P p.1 p.2 * |u p.1 - γ * u p.2| := by
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
              rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 p)]
              exact mul_le_of_le_one_right (mul_nonneg (hw0 p) (abs_nonneg _)) (hφ _)
            have hcs : (∑ p : S × S, π p.1 * P p.1 p.2 * |u p.1 - γ * u p.2|) ^ 2 ≤
                (∑ p : S × S, π p.1 * P p.1 p.2) *
                  ∑ p : S × S, π p.1 * P p.1 p.2 * (u p.1 - γ * u p.2) ^ 2 :=
              Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun p _ => hw0 p)
                (fun p _ => mul_nonneg (hw0 p) (sq_nonneg _))
                (fun p _ => le_of_eq (by rw [mul_pow, sq_abs]; ring))
            have hsq : ∑ p : S × S, π p.1 * P p.1 p.2 * (u p.1 - γ * u p.2) ^ 2 ≤
                ∑ p : S × S, (2 * (π p.1 * P p.1 p.2 * u p.1 ^ 2) +
                  2 * γ ^ 2 * (π p.1 * P p.1 p.2 * u p.2 ^ 2)) := by
              refine Finset.sum_le_sum fun p _ => ?_
              nlinarith [mul_nonneg (hw0 p) (sq_nonneg (u p.1 + γ * u p.2))]
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e1, e2] at hsq
            rw [hw1, one_mul] at hcs
            have hn2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
            have hγ2 : γ ^ 2 ≤ 1 := by nlinarith
            have hDn : 0 ≤ ∑ s, π s * u s ^ 2 := Finset.sum_nonneg fun s _ => mul_nonneg (hπ.1 s) (sq_nonneg _)
            rw [hD]
            nlinarith [mul_le_mul_of_nonneg_right hγ2 hDn]
          have hstep : ∀ θ, ‖θstar - (θ + ((1 - γ) / 4) • gbar π P γ Rw φ θ)‖ ^ 2 ≤
              ‖θstar - θ‖ ^ 2 - (1 - γ) ^ 2 / 4 * dNormSq π φ (θstar - θ) := by
            intro θ
            have e : θstar - (θ + ((1 - γ) / 4) • gbar π P γ Rw φ θ) =
                (θstar - θ) - ((1 - γ) / 4) • gbar π P γ Rw φ θ := by abel
            rw [e, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
            have hi := hinner θ
            have hn := hnorm θ
            have hD := hD0 (θstar - θ)
            have ha : 0 ≤ (1 - γ) / 4 := by linarith
            nlinarith [mul_le_mul_of_nonneg_left hi ha, mul_le_mul_of_nonneg_left hn (sq_nonneg ((1 - γ) / 4))]
          have hrec : ∀ t, ‖θstar - meanPath π P γ Rw φ ((1 - γ) / 4) θ0 (t + 1)‖ ^ 2 ≤
              ‖θstar - meanPath π P γ Rw φ ((1 - γ) / 4) θ0 t‖ ^ 2 -
                (1 - γ) ^ 2 / 4 * dNormSq π φ (θstar - meanPath π P γ Rw φ ((1 - γ) / 4) θ0 t) := by
            intro t
            rw [meanPath]
            exact hstep _
          have htel : ∀ T : ℕ, ‖θstar - meanPath π P γ Rw φ ((1 - γ) / 4) θ0 T‖ ^ 2 +
              (1 - γ) ^ 2 / 4 * ∑ t ∈ Finset.range T,
                dNormSq π φ (θstar - meanPath π P γ Rw φ ((1 - γ) / 4) θ0 t) ≤ ‖θstar - θ0‖ ^ 2 := by
            intro T
            induction T with
            | zero => simp [meanPath]
            | succ n ih =>
              rw [Finset.sum_range_succ]
              have := hrec n
              nlinarith
          have hscale : ∀ (c : ℝ) e, dNormSq π φ (c • e) = c ^ 2 * dNormSq π φ e := by
            intro c e
            simp only [dNormSq, real_inner_smul_right, Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            ring
          have heig : ∀ e, ω * ‖e‖ ^ 2 ≤ dNormSq π φ e := by
            intro e
            by_cases he : e = 0
            · subst he; simp [dNormSq]
            · have hn : 0 < ‖e‖ := norm_pos_iff.mpr he
              have hv : ‖‖e‖⁻¹ • e‖ = 1 := by
                rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
              have := hω.2 ⟨_, hv, rfl⟩
              rw [hscale] at this
              have h2 : ω * ‖e‖ ^ 2 ≤ (‖e‖⁻¹ ^ 2 * dNormSq π φ e) * ‖e‖ ^ 2 :=
                mul_le_mul_of_nonneg_right this (sq_nonneg _)
              rwa [mul_assoc, mul_comm (dNormSq π φ e), ← mul_assoc, ← mul_pow,
                inv_mul_cancel₀ hn.ne', one_pow, one_mul] at h2
          have hpos : 0 < 1 - γ := by linarith
          refine ⟨fun T hT => ?_, fun T => ?_⟩
          · have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
            have hsum : ∑ t ∈ Finset.range T,
                dNormSq π φ (θstar - meanPath π P γ Rw φ ((1 - γ) / 4) θ0 t) ≤
                  4 * ‖θstar - θ0‖ ^ 2 / (1 - γ) ^ 2 := by
              rw [le_div_iff₀ (by positivity)]
              have := htel T
              nlinarith [sq_nonneg ‖θstar - meanPath π P γ Rw φ ((1 - γ) / 4) θ0 T‖]
            have havg : θstar - avgSeq (meanPath π P γ Rw φ ((1 - γ) / 4) θ0) T =
                (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, (θstar - meanPath π P γ Rw φ ((1 - γ) / 4) θ0 t) := by
              rw [avgSeq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, smul_sub,
                ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hTpos.ne', one_smul]
            have hconv : dNormSq π φ (θstar - avgSeq (meanPath π P γ Rw φ ((1 - γ) / 4) θ0) T) ≤
                (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
                  dNormSq π φ (θstar - meanPath π P γ Rw φ ((1 - γ) / 4) θ0 t) := by
              rw [havg]
              simp only [dNormSq, real_inner_smul_right, inner_sum]
              rw [Finset.sum_comm, Finset.mul_sum]
              refine Finset.sum_le_sum fun s _ => ?_
              have hcs : (∑ t ∈ Finset.range T, inner ℝ (φ s)
                    (θstar - meanPath π P γ Rw φ ((1 - γ) / 4) θ0 t)) ^ 2 ≤
                  (∑ t ∈ Finset.range T, (1 : ℝ)) * ∑ t ∈ Finset.range T, inner ℝ (φ s)
                    (θstar - meanPath π P γ Rw φ ((1 - γ) / 4) θ0 t) ^ 2 :=
                Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun _ _ => zero_le_one)
                  (fun _ _ => sq_nonneg _) (fun _ _ => by rw [one_mul])
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
              have hps := hπ.1 s
              set A := ∑ t ∈ Finset.range T, inner ℝ (φ s)
                    (θstar - meanPath π P γ Rw φ ((1 - γ) / 4) θ0 t)
              set B := ∑ t ∈ Finset.range T, inner ℝ (φ s)
                    (θstar - meanPath π P γ Rw φ ((1 - γ) / 4) θ0 t) ^ 2
              have : ((T : ℝ)⁻¹ * A) ^ 2 ≤ (T : ℝ)⁻¹ * B := by
                rw [mul_pow, sq, mul_assoc]
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                rw [inv_mul_le_iff₀ hTpos]
                exact hcs
              calc π s * ((T : ℝ)⁻¹ * A) ^ 2 ≤ π s * ((T : ℝ)⁻¹ * B) :=
                    mul_le_mul_of_nonneg_left this hps
                _ = (T : ℝ)⁻¹ * (π s * B) := by ring
                _ = _ := by simp only [B, Finset.mul_sum]
            have hfin : 4 * ‖θstar - θ0‖ ^ 2 / (T * (1 - γ) ^ 2) =
                (T : ℝ)⁻¹ * (4 * ‖θstar - θ0‖ ^ 2 / (1 - γ) ^ 2) := by
              field_simp
            rw [hfin]
            exact hconv.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
          · induction T with
            | zero => simp [meanPath]
            | succ n ih =>
              have h := hrec n
              have he := heig (θstar - meanPath π P γ Rw φ ((1 - γ) / 4) θ0 n)
              set E := ‖θstar - meanPath π P γ Rw φ ((1 - γ) / 4) θ0 n‖ ^ 2
              set x := (1 - γ) ^ 2 * ω / 4
              have hx := Real.add_one_le_exp (-x)
              have hE0 : 0 ≤ E := sq_nonneg _
              have h3 : ‖θstar - meanPath π P γ Rw φ ((1 - γ) / 4) θ0 (n + 1)‖ ^ 2 ≤
                  Real.exp (-x) * E := by
                have hk : 0 ≤ (1 - γ) ^ 2 / 4 := by positivity
                have hxdef : x = (1 - γ) ^ 2 * ω / 4 := rfl
                nlinarith [mul_le_mul_of_nonneg_left he hk, mul_le_mul_of_nonneg_right hx hE0]
              have hexp : Real.exp (-x * ((n + 1 : ℕ) : ℝ)) = Real.exp (-x) * Real.exp (-x * n) := by
                rw [← Real.exp_add]; congr 1; push_cast; ring
              rw [hexp, mul_assoc]
              exact h3.trans (mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le)
