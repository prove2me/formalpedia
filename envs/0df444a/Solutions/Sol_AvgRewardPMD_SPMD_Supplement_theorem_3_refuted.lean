-- Prove2me | solution 1 for AvgRewardPMD.SPMD.Supplement.theorem_3_refuted
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:30:21.068047+00:00
-- url     : https://prove2.me/submissions/0efd8ea1-25db-4cee-8fb3-c1bfbcc7c8cc

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting
import Definitions.Def_AvgRewardPMD_SPMD_Supplement_Actor

open AvgRewardPMD
open AvgRewardPMD.SPMD
open AvgRewardPMD.SPMD.Supplement

open FoundationsML.ReinforcementLearning MeasureTheory

theorem solution :
    ¬ ∀ (S A : Type) [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
      (P : S → A → S → ℝ) (_hP : IsTransitionKernel P) (_hmix : IsMixing P)
      (_herg : IsErgodic P)
      (c : S → A → ℝ) (h : S → (A → ℝ) → ℝ) (ω : ℝ) (_hω : 0 < ω)
      (_hconv : IsKLStrongConvex h ω)
      (_hclosed : ∀ s, LowerSemicontinuousOn (h s) (stdSimplex ℝ A)) (Γ : ℝ) (_hΓ : IsGammaBound P Γ)
      (πstar : S → A → ℝ) (_hπstar : IsPolicy πstar) (s₀ : S)
      (_hopt : ∀ π' : S → A → ℝ, IsPolicy π' →
        avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀
          ≤ avgCost P π' (fun s a => c s a + h s (π' s)) s₀)
      (νstar : S → ℝ) (_hνstar : MarkovMixing.IsStationary (stateMatrix P πstar) νstar)
      (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ m) (Qhat : ℕ → Ω → S × A → ℝ) (π : ℕ → Ω → S → A → ℝ)
      (bias σ κ : ℝ) (_hbias : 0 ≤ bias) (_hκ : 0 ≤ κ) (K : ℕ) (_hK : 2 ≤ K) (_hσ : 0 < σ)
      (_hcrit : CriticAssumption μ ℱ (fun π' => diffQ P π' (fun s a => c s a + h s (π' s)))
        Qhat π bias κ (K + 1))
      (_hvar : CriticVariance μ ℱ (fun π' => diffQ P π' (fun s a => c s a + h s (π' s)))
        Qhat π σ (K + 1))
      (_hlogarg : 0 < 8 * Γ * (1 - Γ) * ω ^ 2 * stationaryKL νstar uniformPolicy πstar
        + 8 * Γ * (1 - Γ) * ω
          * (avgCost P uniformPolicy (fun s a => c s a + h s (uniformPolicy s)) s₀
            - avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀))
      (q : ℝ)
      (_hq : q = 2 * (1 + Real.log ((8 * Γ * (1 - Γ) * ω ^ 2
          * stationaryKL νstar uniformPolicy πstar
        + 8 * Γ * (1 - Γ) * ω
          * (avgCost P uniformPolicy (fun s a => c s a + h s (uniformPolicy s)) s₀
            - avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀)) / σ ^ 2)))
      (_hqpos : 0 < q)
      (lam : ℝ)
      (_hlam : lam = min ((1 - Γ) / (ω * Γ)) (q * Real.log K / (ω * K)))
      (_hiter : IsSPMDIterates h (fun _ => lam) Qhat π)
      (_hintD : Integrable (fun ξ => stationaryKL νstar (π (K + 1) ξ) πstar) μ),
      ∫ ξ, stationaryKL νstar (π (K + 1) ξ) πstar ∂μ
        ≤ Γ ^ K / ω
            * (avgCost P uniformPolicy (fun s a => c s a + h s (uniformPolicy s)) s₀
              - avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀)
          + Γ ^ K * stationaryKL νstar uniformPolicy πstar
          + σ ^ 2 / (4 * ω ^ 2 * Γ * (1 - Γ) * K) * (1 + q * Real.log K)
          + 2 * bias / (ω * Γ) := by
            intro H
            obtain ⟨L2, hL2⟩ : ∃ L2 : ℝ, L2 = Real.log 2 := ⟨_, rfl⟩
            have hL2gt : 0.6931471803 < L2 := hL2 ▸ Real.log_two_gt_d9
            have hexpL2 : Real.exp L2 = 2 := by rw [hL2, Real.exp_log (by norm_num)]
            obtain ⟨Z, hZ⟩ : ∃ Z : ℝ → ℝ, Z = fun b => Real.exp (b * L2) + Real.exp (-(b * L2)) := ⟨_, rfl⟩
            obtain ⟨v, hv⟩ : ∃ v : Fin 2 → ℝ, v = ![L2, -L2] := ⟨_, rfl⟩
            have hv0 : v 0 = L2 := by rw [hv]; rfl
            have hv1 : v 1 = -L2 := by rw [hv]; rfl
            obtain ⟨w, hw⟩ : ∃ w : ℝ → Fin 2 → ℝ, w = fun b a => Real.exp (b * v a) / Z b := ⟨_, rfl⟩
            have hZpos : ∀ b, 0 < Z b := fun b => by rw [hZ]; positivity
            have hwpos : ∀ b a, 0 < w b a := fun b a => by rw [hw]; exact div_pos (Real.exp_pos _) (hZpos b)
            have hwsum : ∀ b, w b 0 + w b 1 = 1 := fun b => by
              rw [hw]; simp only [hv0, hv1]
              rw [← add_div, div_eq_one_iff_eq (hZpos b).ne', hZ]; ring_nf
            have hlogw : ∀ b a, Real.log (w b a) = b * v a - Real.log (Z b) := fun b a => by
              rw [hw]; simp only
              rw [Real.log_div (Real.exp_pos _).ne' (hZpos b).ne', Real.log_exp]
            have hterm : ∀ x y : ℝ, 0 < y → x * Real.log (x / y) = x * Real.log x - x * Real.log y := by
              intro x y hy
              rcases eq_or_ne x 0 with hx | hx
              · simp [hx]
              · rw [Real.log_div hx hy.ne']; ring
            obtain ⟨h, hh⟩ : ∃ h : Unit → (Fin 2 → ℝ) → ℝ,
                h = fun _ p => ∑ a, (p a * Real.log (p a) - p a * v a) := ⟨_, rfl⟩
            have hh2 : ∀ s p, h s p = p 0 * Real.log (p 0) + p 1 * Real.log (p 1) - (p 0 * v 0 + p 1 * v 1) := by
              intro s p; rw [hh]; simp only [Fin.sum_univ_two]; ring
            -- identity I
            have hI : ∀ b (p : Fin 2 → ℝ), p 0 + p 1 = 1 →
                p 0 * Real.log (p 0) + p 1 * Real.log (p 1) - b * (p 0 * v 0 + p 1 * v 1)
                  = kl p (w b) - Real.log (Z b) := by
              intro b p hp
              simp only [kl, Fin.sum_univ_two]
              rw [hterm _ _ (hwpos b 0), hterm _ _ (hwpos b 1), hlogw, hlogw]
              linear_combination (-Real.log (Z b)) * hp
            -- Gibbs
            have hG : ∀ b (p : Fin 2 → ℝ), p ∈ stdSimplex ℝ (Fin 2) → 0 ≤ kl p (w b) := by
              intro b p hp
              have h1 : ∀ a, p a - w b a ≤ p a * Real.log (p a / w b a) := by
                intro a
                rcases (hp.1 a).eq_or_lt with h0 | h0
                · rw [← h0]; simp; exact (hwpos b a).le
                · have := Real.one_sub_inv_le_log_of_pos (div_pos h0 (hwpos b a))
                  rw [inv_div] at this
                  have h2 := mul_le_mul_of_nonneg_left this h0.le
                  rw [mul_sub, mul_one, mul_div_cancel₀ _ h0.ne'] at h2
                  exact h2
              have hs := hp.2
              simp only [Fin.sum_univ_two] at hs
              simp only [kl, Fin.sum_univ_two]
              linarith [h1 0, h1 1, hwsum b]
            have hklself : ∀ b, kl (w b) (w b) = 0 := by
              intro b; simp only [kl]
              apply Finset.sum_eq_zero; intro a _
              rw [div_self (hwpos b a).ne', Real.log_one, mul_zero]
            obtain ⟨P, hPdef⟩ : ∃ P : Unit → Fin 2 → Unit → ℝ, P = fun _ _ _ => 1 := ⟨_, rfl⟩
            obtain ⟨c, hcdef⟩ : ∃ c : Unit → Fin 2 → ℝ, c = fun _ _ => 0 := ⟨_, rfl⟩
            have hP : IsTransitionKernel P := by
              intro s a; rw [hPdef]; simp
            have hM : ∀ π' : Unit → Fin 2 → ℝ, IsPolicy π' → stateMatrix P π' = 1 := by
              intro π' hπ'
              ext i j
              have := (hπ' i).2
              simp only [stateMatrix, InducedTransition, hPdef, Matrix.of_apply, mul_one]
              rw [this]; cases i; cases j; simp
            have hstat : ∀ M : Matrix Unit Unit ℝ, M = 1 → MarkovMixing.IsStationary M (fun _ => 1) := by
              intro M hM1; subst hM1
              refine ⟨⟨fun _ => zero_le_one, by simp⟩, ?_⟩
              ext i; simp
            have hdist : ∀ ν : Unit → ℝ, MarkovMixing.IsDist ν → ∀ s, ν s = 1 := by
              intro ν hν s; have := hν.2; simpa using this
            have hmix : IsMixing P := by
              refine ⟨1, fun π' hπ' => ⟨fun _ => 1, hstat _ (hM π' hπ'), 1, le_rfl, le_rfl, ?_⟩⟩
              intro q hq
              rw [hM π' hπ']
              have := hdist q hq
              simp [this]
            have herg : IsErgodic P := by
              intro π' hπ'
              rw [hM π' hπ']
              refine ⟨fun x y => ⟨0, by cases x; cases y; simp⟩, ?_⟩
              intro x
              unfold MarkovMixing.period
              have : {d : ℕ | ∀ t ∈ MarkovMixing.returnSet (1 : Matrix Unit Unit ℝ) x, d ∣ t} = {1} := by
                ext d
                simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
                constructor
                · intro hd
                  have : d ∣ 1 := hd 1 ⟨le_rfl, by cases x; simp⟩
                  exact Nat.dvd_one.mp this
                · rintro rfl t _; exact one_dvd t
              rw [this, csSup_singleton]
            have hΓ : IsGammaBound P (1/2) := by
              refine ⟨by norm_num, by norm_num, fun π' _ ν hν s => ?_⟩
              rw [hdist ν hν.1 s]; norm_num
            have hpol : ∀ b, IsPolicy (fun _ : Unit => w b) := by
              intro b s; refine ⟨fun a => (hwpos b a).le, ?_⟩
              simp only [Fin.sum_univ_two]; exact hwsum b
            have havg : ∀ π' : Unit → Fin 2 → ℝ, IsPolicy π' → ∀ s₀,
                avgCost P π' (fun s a => c s a + h s (π' s)) s₀ = h () (π' ()) := by
              intro π' hπ' s₀
              unfold avgCost
              rw [hM π' hπ']
              have hR : InducedReward π' (fun s a => c s a + h s (π' s)) = fun _ => h () (π' ()) := by
                funext s; cases s
                simp only [InducedReward, hcdef, zero_add]
                rw [← Finset.sum_mul, (hπ' ()).2, one_mul]
              rw [hR]
              apply Filter.Tendsto.limUnder_eq
              apply tendsto_const_nhds.congr'
              filter_upwards [Filter.eventually_ne_atTop 0] with T hT
              simp only [one_pow, Matrix.one_mulVec, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              field_simp
            have hdiffQ : ∀ π' : Unit → Fin 2 → ℝ, IsPolicy π' → ∀ x,
                diffQ P π' (fun s a => c s a + h s (π' s)) x = 0 := by
              intro π' hπ' x
              unfold diffQ
              rw [havg π' hπ']
              have hf : (fun y : Unit × Fin 2 => c y.1 y.2 + h y.1 (π' y.1)) = fun _ => h () (π' ()) := by
                funext y; rw [hcdef]; simp
              rw [hf]
              have hpow : ∀ t, (saTransition P π' ^ t).mulVec (fun _ => h () (π' ())) = fun _ => h () (π' ()) := by
                intro t
                induction t with
                | zero => simp
                | succ n ih =>
                  rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
                  funext y
                  simp only [Matrix.mulVec, dotProduct, saTransition, Matrix.of_apply, hPdef, one_mul]
                  rw [← Finset.sum_mul, Fintype.sum_prod_type]
                  simp only [Finset.univ_unique, Finset.sum_singleton]
                  rw [(hπ' default).2, one_mul]
              simp [hpow]
            have hconv : IsKLStrongConvex h 1 := by
              intro s
              refine ⟨zero_le_one, ⟨convex_stdSimplex ℝ (Fin 2), ?_⟩, ?_⟩
              · intro x hx y hy a b ha hb hab
                rw [hh2, hh2, hh2]
                simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
                have c0 := Real.convexOn_mul_log.2 (Set.mem_Ici.2 (hx.1 0)) (Set.mem_Ici.2 (hy.1 0)) ha hb hab
                have c1 := Real.convexOn_mul_log.2 (Set.mem_Ici.2 (hx.1 1)) (Set.mem_Ici.2 (hy.1 1)) ha hb hab
                simp only [smul_eq_mul] at c0 c1
                nlinarith [c0, c1]
              · intro p' _ hp'
                refine ⟨fun a => Real.log (p' a) - v a, fun p hp => ?_⟩
                rw [hh2, hh2]
                simp only [kl, Fin.sum_univ_two]
                rw [hterm _ _ (hp' 0), hterm _ _ (hp' 1)]
                apply le_of_eq; ring
            have hclosed : ∀ s, LowerSemicontinuousOn (h s) (stdSimplex ℝ (Fin 2)) := by
              intro s
              rw [hh]
              exact (continuous_finsetSum _ (fun a _ => ((Real.continuous_mul_log.comp (continuous_apply a)).sub
                ((continuous_apply a).mul continuous_const)))).lowerSemicontinuous.lowerSemicontinuousOn _
            have hsimp : ∀ π' : Unit → Fin 2 → ℝ, IsPolicy π' → π' () ∈ stdSimplex ℝ (Fin 2) :=
              fun π' hπ' => ⟨(hπ' ()).1, (hπ' ()).2⟩
            have hhw1 : h () (w 1) = - Real.log (Z 1) := by
              have := hI 1 (w 1) (hwsum 1); rw [hklself] at this; rw [hh2]; linarith
            have hopt : ∀ π' : Unit → Fin 2 → ℝ, IsPolicy π' →
                avgCost P (fun _ => w 1) (fun s a => c s a + h s ((fun _ => w 1) s)) ()
                  ≤ avgCost P π' (fun s a => c s a + h s (π' s)) () := by
              intro π' hπ'
              rw [havg _ (hpol 1), havg _ hπ']
              have hs := (hπ' ()).2; simp only [Fin.sum_univ_two] at hs
              have := hI 1 (π' ()) hs
              have := hG 1 (π' ()) (hsimp π' hπ')
              rw [hhw1, hh2]; linarith
            obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℝ, β = fun k => 1 - 1 / (1 + 1/1000) ^ k := ⟨_, rfl⟩
            obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (64/1000) / Real.log ((64:ℕ):ℝ) := ⟨_, rfl⟩
            have hlog64 : 1 < Real.log ((64:ℕ):ℝ) := by
              rw [Real.lt_log_iff_exp_lt (by norm_num)]
              have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
            have hqpos : 0 < q := by rw [hqdef]; positivity
            have hqlog : q * Real.log ((64:ℕ):ℝ) = 64/1000 := by
              rw [hqdef]; field_simp
            have hqlt : q < 1 := by
              rw [hqdef, div_lt_one (by linarith)]; exact lt_trans (by norm_num) hlog64
            obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ, lam = min ((1 - 1/2) / (1 * (1/2))) (q * Real.log ((64:ℕ):ℝ) / (1 * ((64:ℕ):ℝ))) := ⟨_, rfl⟩
            have hlam : lam = 1/1000 := by
              rw [hlamdef, hqlog]; norm_num
            have hβrec : ∀ k, (1 + lam) * β (k+1) = lam + β k := by
              intro k; rw [hlam, hβ]; simp only
              rw [pow_succ]; field_simp; ring
            have hiter : IsSPMDIterates h (fun _ => lam) (fun _ _ _ => (0:ℝ)) (fun k (_ : Unit) _ => w (β k)) := by
              intro ξ
              refine ⟨fun s a => ?_, fun k s => ⟨⟨fun a => (hwpos _ a).le, ?_⟩, fun p hp => ?_⟩⟩
              · rw [hβ, hw, hZ]; simp; norm_num
              · simp only [Fin.sum_univ_two]; exact hwsum _
              · simp only [zero_mul, Finset.sum_const_zero, zero_add]
                have hs := hp.2; simp only [Fin.sum_univ_two] at hs
                have E1 := hI (β k) p hs
                have E2 := hI (β (k+1)) p hs
                have E3 := hI (β k) (w (β (k+1))) (hwsum _)
                have E4 := hI (β (k+1)) (w (β (k+1))) (hwsum _)
                rw [hklself] at E4
                have G := hG (β (k+1)) p hp
                have hl : 0 ≤ lam := by rw [hlam]; norm_num
                have hrc := hβrec k
                rw [hh2, hh2]
                nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 + lam) G,
                  congrArg (fun t => t * (p 0 * v 0 + p 1 * v 1)) hrc,
                  congrArg (fun t => t * (w (β (k+1)) 0 * v 0 + w (β (k+1)) 1 * v 1)) hrc,
                  congrArg (fun t => (1 + lam) * t) E2, congrArg (fun t => (1 + lam) * t) E4]
            have hw10 : w 1 0 = 4/5 := by
              rw [hw, hZ]; simp only [hv0, one_mul, Real.exp_neg, hexpL2]; norm_num
            have hw11 : w 1 1 = 1/5 := by
              rw [hw, hZ]; simp only [hv1, one_mul, Real.exp_neg, hexpL2]; norm_num
            have hZ1 : Z 1 = 5/2 := by
              rw [hZ]; simp only [one_mul, Real.exp_neg, hexpL2]; norm_num
            have hZ0 : Z 0 = 2 := by
              rw [hZ]; simp only [zero_mul, neg_zero, Real.exp_zero]; norm_num
            have hZge : ∀ b, 2 ≤ Z b := by
              intro b; rw [hZ]; simp only
              linarith [Real.add_one_le_exp (b * L2), Real.add_one_le_exp (-(b * L2))]
            have hklw1 : ∀ b, kl (w 1) (w b) = Real.log (Z b) - Real.log (Z 1) + (1 - b) * (3/5 * L2) := by
              intro b
              have e1 := hI b (w 1) (hwsum 1)
              have e2 := hI 1 (w 1) (hwsum 1)
              rw [hklself] at e2
              rw [hw10, hw11, hv0, hv1] at e1 e2
              linarith
            have huniff : (uniformPolicy : Unit → Fin 2 → ℝ) = fun _ => w 0 := by
              funext s a
              simp only [uniformPolicy, Fintype.card_fin]
              rw [hw, hZ]; simp; norm_num
            have hw00 : w 0 0 = 1/2 := by rw [hw, hZ]; simp; norm_num
            have hw01 : w 0 1 = 1/2 := by rw [hw, hZ]; simp; norm_num
            have hhw0 : h () (w 0) = -L2 := by
              have := hI 0 (w 0) (hwsum 0); rw [hklself, hZ0, ← hL2] at this; rw [hh2, hw00, hw01, hv0, hv1] at *
              linarith
            have hvU : avgCost P uniformPolicy (fun s a => c s a + h s (uniformPolicy s)) () = -L2 := by
              rw [huniff, havg _ (hpol 0), hhw0]
            have hvS : avgCost P (fun _ => w 1) (fun s a => c s a + h s (w 1)) () = -Real.log (5/2) := by
              rw [havg _ (hpol 1), hhw1, hZ1]
            have hvD : stationaryKL (fun _ : Unit => (1:ℝ)) uniformPolicy (fun _ => w 1) = L2 - Real.log (5/2) + 3/5 * L2 := by
              rw [huniff]; simp only [stationaryKL, Finset.univ_unique, Finset.sum_singleton, one_mul]
              rw [hklw1, hZ0, hZ1, ← hL2]; ring
            obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = Real.sqrt (6/5 * L2 * Real.exp (1 - q/2)) := ⟨_, rfl⟩
            have hσ : 0 < σ := by rw [hσdef]; apply Real.sqrt_pos.2; have := Real.exp_pos (1 - q/2); positivity
            have hσsq : σ ^ 2 = 6/5 * L2 * Real.exp (1 - q/2) := by
              rw [hσdef, Real.sq_sqrt]; have := Real.exp_pos (1 - q/2); positivity
            have key := H Unit (Fin 2) P hP hmix herg c h 1 one_pos hconv hclosed (1/2) hΓ (fun _ => w 1) (hpol 1) ()
              hopt (fun _ => 1) (hstat _ (hM _ (hpol 1))) Unit _ (Measure.dirac ()) (Filtration.const ℕ _ le_rfl)
              (fun _ _ _ => 0) (fun k _ _ => w (β k)) 0 σ 0 le_rfl le_rfl 64 (by norm_num) hσ ?hcrit ?hvar ?hlogarg
              q ?hq hqpos lam hlamdef hiter ?hintD
            case hintD => exact integrable_const _
            case hlogarg =>
              rw [hvU, hvS, hvD]; nlinarith
            case hq =>
              rw [hvU, hvS, hvD, hσsq]
              have hL2pos : (6/5 * L2) ≠ 0 := by positivity
              rw [show 8 * (1 / 2) * (1 - 1 / 2) * 1 ^ 2 * (L2 - Real.log (5 / 2) + 3 / 5 * L2) +
                  8 * (1 / 2) * (1 - 1 / 2) * 1 * (-L2 - -Real.log (5 / 2)) = 6/5 * L2 by ring,
                div_mul_cancel_left₀ hL2pos, ← Real.exp_neg, Real.log_exp]
              ring
            case hcrit =>
              refine ⟨fun k _ s a => measurable_const, fun k _ x => integrable_const _,
                fun k _ => Filter.Eventually.of_forall (fun ξ => ?_),
                fun k _ => ⟨integrable_const _, Filter.Eventually.of_forall (fun ξ => ?_)⟩⟩
              · simp only []
                rw [condExp_const (Filtration.le _ k)]
                simp only [hdiffQ _ (hpol _)]
                simp [span]
              · simp only []
                rw [condExp_const (Filtration.le _ k)]
                simp [span]
            case hvar =>
              refine ⟨hσ.le, fun k _ => ⟨integrable_const _, Filter.Eventually.of_forall (fun ξ => ?_)⟩⟩
              simp only []
              rw [condExp_const (Filtration.le _ k)]
              simp only [hdiffQ _ (hpol _)]
              simp [span]
              positivity
            have hint : ∫ ξ, stationaryKL (fun _ : Unit => (1:ℝ)) (fun _ => w (β (64+1))) (fun _ => w 1) ∂(Measure.dirac ()) = kl (w 1) (w (β 65)) := by
              simp [stationaryKL]
            rw [hint, hvU, hvS, hvD, hσsq, hqlog, hklw1] at key
            have hb : 10/11 ≤ 1 - β 65 := by
              rw [hβ]; simp only
              rw [sub_sub_cancel, le_div_iff₀ (by positivity)]
              norm_num
            have hlZ : Real.log 2 ≤ Real.log (Z (β 65)) := Real.log_le_log (by norm_num) (hZge _)
            have h52 : Real.log (5/2) = L2 + Real.log (5/4) := by
              rw [hL2, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
            have h54 : Real.log (5/4) ≤ 1/4 := by
              have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 5/4 by norm_num); linarith
            have hE : Real.exp (1 - q/2) ≤ 2.7182818286 :=
              le_trans (Real.exp_le_exp.2 (by linarith)) Real.exp_one_lt_d9.le
            have hL2pos : 0 < L2 := by linarith
            have p1 := mul_le_mul_of_nonneg_right hb hL2pos.le
            have p2 := mul_le_mul_of_nonneg_left hE hL2pos.le
            have hpow : ((1:ℝ)/2)^64 ≤ 1/1000 := by norm_num
            have p3 := mul_le_mul_of_nonneg_right hpow hL2pos.le
            rw [hZ1, h52] at key
            rw [← hL2] at hlZ
            have e : (4 * 1 ^ 2 * (1 / 2) * (1 - 1 / 2) * ((64:ℕ):ℝ)) = 64 := by norm_num
            rw [e] at key
            have e2 : ((1:ℝ) / 2) ^ 64 / 1 = (1/2)^64 := by norm_num
            rw [e2] at key
            linarith
