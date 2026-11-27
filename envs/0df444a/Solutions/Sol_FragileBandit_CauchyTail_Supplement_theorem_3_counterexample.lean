-- Prove2me | solution 1 for FragileBandit.CauchyTail.Supplement.theorem_3_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:19:18.233113+00:00
-- url     : https://prove2.me/submissions/2e1156e4-7b96-4db0-b9b6-3a27a9978ac0

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Supplement_ProcessAsymptotics
import Definitions.Def_FragileBandit_CauchyTail_Supplement_PathwiseConvergence

set_option autoImplicit false

open FragileBandit
open FragileBandit.CauchyTail
open FragileBandit.CauchyTail.Supplement

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm
open scoped ENNReal Topology

/-- Counterexample to the full generality of Theorem 3, p.21, (23).
The smooth limiting CGFs do not control information about later rewards revealed early.
See DISPROOF.md for the independent finite-transient construction and the policy. -/
theorem solution :
    ∃ (ν : RestedEnvironment 2) (π : BanditPolicy 2),
      IndependentArms ν ∧
      AssumptionOne ν ∧ AssumptionTwo ν ∧
      FitsFamily (gaussianReal 0 1) ν ∧
      IsGaussianPathwiseConvergent π ∧
      (∀ (i : Fin 2) (θ : ℝ), limitingCGF ν i θ =
        (((if i = 0 then 1 else 0 : ℝ) * θ + θ ^ 2 / 2 : ℝ) : EReal)) ∧
      processMean ν 0 = 1 ∧ processMean ν 1 = 0 ∧
      processTailExponent (gaussianReal 0 1) ν 1 = 1 ∧
      (∀ γ : ℝ, 0 < γ → γ < 1 →
        ∀ᶠ T : ℕ in atTop, ∀ x ∈ tailWindow γ T, processTail ν π 1 T x = 0) ∧
      ¬ UniformTailLower (processTail ν π 1) (processTailExponent (gaussianReal 0 1) ν 1)
      := by
        have hA : meanSet (gaussianReal 0 1) = Set.univ ∧
            ∀ z w : ℝ, dP (gaussianReal 0 1) z w = ENNReal.ofReal ((z - w) ^ 2 / 2) := by
          have hint : ∀ θ : ℝ, ∫ x, Real.exp (θ * x) ∂(gaussianReal 0 1) = Real.exp (θ ^ 2 / 2) := by
            intro θ
            have h := mgf_gaussianReal (p := gaussianReal 0 1) (X := id) (μ := 0) (v := 1) (by simp) θ
            simpa [mgf] using h
          have htilt : ∀ θ : ℝ, tilt (gaussianReal 0 1) θ = gaussianReal θ 1 := by
            intro θ
            unfold tilt Measure.tilted
            rw [hint θ, gaussianReal_of_var_ne_zero 0 one_ne_zero,
              gaussianReal_of_var_ne_zero θ one_ne_zero]
            rw [← withDensity_mul _ (by fun_prop) (by fun_prop)]
            congr 1
            funext x
            simp only [Pi.mul_apply, gaussianPDF]
            rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
            congr 1
            simp only [gaussianPDFReal]
            rw [← Real.exp_sub, mul_assoc, ← Real.exp_add]
            congr 2
            simp
            ring
          have hnat : ∀ θ : ℝ, θ ∈ natParamSet (gaussianReal 0 1) := by
            intro θ
            exact integrable_exp_mul_gaussianReal θ
          have hidint : ∀ θ : ℝ, Integrable id (gaussianReal θ 1) := by
            intro θ
            exact (memLp_id_gaussianReal (μ := θ) (v := 1) 1).integrable (by simp)
          have hex : ∀ z : ℝ, ∃ θ ∈ natParamSet (gaussianReal 0 1),
              Integrable id (tilt (gaussianReal 0 1) θ) ∧ ∫ x, x ∂(tilt (gaussianReal 0 1) θ) = z := by
            intro z
            refine ⟨z, hnat z, ?_, ?_⟩
            · rw [htilt]; exact hidint z
            · rw [htilt]; exact integral_id_gaussianReal
          have hexp : ∀ z : ℝ, expFam (gaussianReal 0 1) z = gaussianReal z 1 := by
            intro z
            have h1 : thetaOf (gaussianReal 0 1) z = z := by
              unfold thetaOf
              rw [dif_pos (hex z)]
              have := (hex z).choose_spec.2.2
              rw [htilt] at this
              rw [integral_id_gaussianReal] at this
              exact this
            unfold expFam
            rw [h1, htilt]
          refine ⟨Set.eq_univ_of_forall fun z => hex z, ?_⟩
          intro z w
          unfold dP
          rw [hexp, hexp]
          have hintw : ∫ x, Real.exp ((z - w) * x) ∂(gaussianReal w 1)
              = Real.exp (w * (z - w) + (z - w) ^ 2 / 2) := by
            have h := mgf_gaussianReal (p := gaussianReal w 1) (X := id) (μ := w) (v := 1) (by simp) (z - w)
            simpa [mgf] using h
          have hzw : gaussianReal z 1 = (gaussianReal w 1).tilted (fun x => (z - w) * x) := by
            rw [← htilt z, ← htilt w]
            unfold tilt
            rw [tilted_tilted (integrable_exp_mul_gaussianReal w)]
            congr 1
            funext x
            simp
            ring
          have hac : gaussianReal z 1 ≪ gaussianReal w 1 := by
            rw [hzw]; exact tilted_absolutelyContinuous _ _
          have hllr : llr (gaussianReal z 1) (gaussianReal w 1) =ᵐ[gaussianReal z 1]
              fun x => (z - w) * x - (w * (z - w) + (z - w) ^ 2 / 2) := by
            have h := log_rnDeriv_tilted_left_self (μ := gaussianReal w 1) (f := fun x => (z - w) * x)
              (integrable_exp_mul_gaussianReal (z - w))
            rw [hintw, Real.log_exp, ← hzw] at h
            exact hac.ae_le h
          have hi1 : Integrable (fun x : ℝ => (z - w) * x) (gaussianReal z 1) :=
            (hidint z).const_mul (z - w)
          have hi : Integrable (llr (gaussianReal z 1) (gaussianReal w 1)) (gaussianReal z 1) :=
            (integrable_congr hllr).2 (hi1.sub (integrable_const _))
          rw [InformationTheory.klDiv_of_ac_of_integrable hac hi]
          congr 1
          rw [integral_congr_ae hllr, integral_sub hi1 (integrable_const _), integral_const_mul,
            integral_id_gaussianReal]
          simp
          ring
        have hB : ∃ ν : RestedEnvironment 2, IndependentArms ν ∧
            (∀ (i : Fin 2) (n : ℕ) (θ : ℝ), 1 ≤ n → scaledCGF ν i n θ =
              (((if i = 0 then 1 else 0 : ℝ) * θ + θ ^ 2 / 2 : ℝ) : EReal)) ∧
            (∃ A : Set (RewardTable 2), MeasurableSet A ∧ (∀ᵐ x ∂ν.law, x ∈ A) ∧
              ∀ x ∈ A, ∃ z : Fin 2 → ℝ, ∀ i (n : ℕ),
                rewardSum x i n = n * (if i = 0 then 1 else 0 : ℝ) + √(n:ℝ) * z i) := by
          let m : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
          let tab : (Fin 2 → ℝ) → RewardTable 2 := fun z i s => m i + (√((s:ℝ) + 1) - √(s:ℝ)) * z i
          have hmeas : Measurable tab := by
            refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun s => ?_
            exact ((measurable_pi_apply i).const_mul _).const_add _
          have hsum : ∀ z i (n : ℕ), rewardSum (tab z) i n = n * m i + √(n:ℝ) * z i := by
            intro z i n
            unfold rewardSum
            induction n with
            | zero => simp
            | succ n ih =>
              rw [Finset.sum_range_succ, ih]
              simp only [tab]
              push_cast
              ring
          have hrec : ∀ (x : RewardTable 2) i (s : ℕ), x i s = rewardSum x i (s+1) - rewardSum x i s := by
            intro x i s
            simp [rewardSum, Finset.sum_range_succ]
          have hrm : ∀ i n, Measurable (fun x : RewardTable 2 => rewardSum x i n) := by
            intro i n
            unfold rewardSum
            exact Finset.measurable_sum _ fun s _ => (measurable_pi_apply s).comp (measurable_pi_apply i)
          let μ : Measure (Fin 2 → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
          have hp : IsProbabilityMeasure (μ.map tab) := Measure.isProbabilityMeasure_map hmeas.aemeasurable
          refine ⟨⟨μ.map tab, hp⟩, ?_, ?_, ?_⟩
          · unfold IndependentArms
            show iIndepFun (fun i (x : RewardTable 2) => x i) (μ.map tab)
            have h1 : iIndepFun (fun (i : Fin 2) (z : Fin 2 → ℝ) =>
                (fun s : ℕ => m i + (√((s:ℝ) + 1) - √(s:ℝ)) * z i : ℕ → ℝ)) μ := by
              exact iIndepFun_pi (μ := fun _ : Fin 2 => gaussianReal 0 1)
                (X := fun (i : Fin 2) (y : ℝ) => (fun s : ℕ => m i + (√((s:ℝ) + 1) - √(s:ℝ)) * y : ℕ → ℝ))
                (fun i => (measurable_pi_lambda _ fun s =>
                  (measurable_id.const_mul _).const_add _).aemeasurable)
            rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply i).aemeasurable)]
            rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_lambda _ fun s =>
                  ((measurable_pi_apply i).const_mul _).const_add _).aemeasurable)] at h1
            rw [Measure.map_map (measurable_pi_lambda _ fun i => measurable_pi_apply i) hmeas]
            have h2 : ∀ i : Fin 2, (μ.map tab).map (fun x : RewardTable 2 => x i) =
                μ.map (fun z => (fun s : ℕ => m i + (√((s:ℝ) + 1) - √(s:ℝ)) * z i : ℕ → ℝ)) := by
              intro i
              rw [Measure.map_map (measurable_pi_apply i) hmeas]
              rfl
            simp_rw [h2]
            exact h1
          · intro i n θ hn
            have hn0 : (0:ℝ) < n := by exact_mod_cast hn
            unfold scaledCGF
            show _ * ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (θ * rewardSum x i n)) ∂(μ.map tab)) = _
            have h1 : ∫⁻ x, ENNReal.ofReal (Real.exp (θ * rewardSum x i n)) ∂(μ.map tab)
                = ENNReal.ofReal (Real.exp (n * (m i * θ + θ ^ 2 / 2))) := by
              have hm1 : Measurable (fun x : RewardTable 2 => ENNReal.ofReal (Real.exp (θ * rewardSum x i n))) :=
                (Real.measurable_exp.comp ((hrm i n).const_mul θ)).ennreal_ofReal
              rw [lintegral_map hm1 hmeas]
              simp_rw [hsum]
              have h2 := (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 1) i).lintegral_comp
                (f := fun y => ENNReal.ofReal (Real.exp (θ * (n * m i + √(n:ℝ) * y))))
                (by fun_prop)
              rw [show (∫⁻ a, ENNReal.ofReal (Real.exp (θ * (↑n * m i + √(n:ℝ) * a i))) ∂μ) = _ from h2]
              have hi : ∀ y : ℝ, Real.exp (θ * (n * m i + √(n:ℝ) * y)) =
                  Real.exp (θ * (n * m i)) * Real.exp ((θ * √(n:ℝ)) * y) := by
                intro y; rw [← Real.exp_add]; ring_nf
              simp_rw [hi]
              rw [← ofReal_integral_eq_lintegral_ofReal]
              · congr 1
                rw [integral_const_mul]
                have h := mgf_gaussianReal (p := gaussianReal 0 1) (X := id) (μ := 0) (v := 1) (by simp)
                  (θ * √(n:ℝ))
                have h' : ∫ x, Real.exp ((θ * √(n:ℝ)) * x) ∂(gaussianReal 0 1)
                    = Real.exp ((θ * √(n:ℝ)) ^ 2 / 2) := by simpa [mgf] using h
                rw [h', ← Real.exp_add, mul_pow, Real.sq_sqrt hn0.le]
                ring_nf
              · exact (integrable_exp_mul_gaussianReal _).const_mul _
              · exact Eventually.of_forall fun y => by positivity
            rw [h1, ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp, ← EReal.coe_mul]
            congr 1
            simp only [m]
            field_simp
          · have hAm : MeasurableSet {x : RewardTable 2 | ∀ i (n:ℕ),
                rewardSum x i n = n * m i + √(n:ℝ) * (x i 0 - m i)} := by
              have he : {x : RewardTable 2 | ∀ i (n:ℕ), rewardSum x i n = n * m i + √(n:ℝ) * (x i 0 - m i)}
                = ⋂ i, ⋂ n : ℕ, {x : RewardTable 2 | rewardSum x i n = n * m i + √(n:ℝ) * (x i 0 - m i)} := by
                ext x; simp
              rw [he]
              refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun n => ?_
              have hx0 : Measurable (fun x : RewardTable 2 => x i 0) :=
                (measurable_pi_apply 0).comp (measurable_pi_apply i)
              exact measurableSet_eq_fun (hrm i n) (((hx0.sub_const _).const_mul _).const_add _)
            refine ⟨{x | ∀ i n, rewardSum x i n = n * m i + √(n:ℝ) * (x i 0 - m i)}, hAm, ?_, ?_⟩
            · have hae : ∀ z, tab z ∈ {x : RewardTable 2 | ∀ i (n:ℕ),
                  rewardSum x i n = n * m i + √(n:ℝ) * (x i 0 - m i)} := by
                intro z i n
                rw [hsum]
                simp [tab]
              exact (ae_map_iff hmeas.aemeasurable hAm).2 (Eventually.of_forall hae)
            · intro x hx
              exact ⟨fun i => x i 0 - m i, hx⟩
        have hC : ∀ (A : ℕ → Prop) (N τ : ℕ → ℝ) (κ : ℝ), 0 < κ →
            (∀ n, (A n ∧ N (n+1) = N n + 1) ∨ (¬ A n ∧ N (n+1) = N n)) →
            (∀ n, 0 ≤ N n) →
            Tendsto (fun n : ℕ => τ n / Real.log n) atTop (𝓝 κ) →
            (∀ᶠ n in atTop, A n → N n < τ n) →
            (∀ᶠ n : ℕ in atTop, N n < τ n → √(Real.log n) ≤ n - N n → A n) →
            Tendsto (fun n : ℕ => N n / Real.log n) atTop (𝓝 κ) := by
          intro A N τ κ hκ hstep hN0 hτ hup hlow
          have hlogtop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
            Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
          have hlogn : Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0) := by
            have := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
            exact this
          -- upper bound
          have hupper : ∀ U, κ < U → ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, N n ≤ C + U * Real.log n := by
            intro U hU
            have hU0 : 0 < U := hκ.trans hU
            have h1 : ∀ᶠ n : ℕ in atTop, τ n ≤ U * Real.log n := by
              filter_upwards [hτ.eventually_lt_const hU, hlogtop.eventually_gt_atTop 0] with n hn hl
              rw [div_lt_iff₀ hl] at hn
              exact hn.le
            obtain ⟨n0, hn0⟩ := eventually_atTop.1 ((h1.and hup).and (eventually_ge_atTop 1))
            refine ⟨N n0 + 1, eventually_atTop.2 ⟨n0, fun n hn => ?_⟩⟩
            induction n, hn using Nat.le_induction with
            | base =>
              have : 0 ≤ Real.log n0 := Real.log_natCast_nonneg n0
              nlinarith
            | succ n hn ih =>
              obtain ⟨⟨a1, a2⟩, a3⟩ := hn0 n hn
              have hl : Real.log n ≤ Real.log ((n+1 : ℕ):ℝ) := by
                apply Real.log_le_log
                · exact_mod_cast a3
                · push_cast; linarith
              have hl' := mul_le_mul_of_nonneg_left hl hU0.le
              rcases hstep n with ⟨hA, h⟩ | ⟨hA, h⟩
              · have := a2 hA
                have := hN0 n0
                rw [h]; linarith
              · rw [h]; linarith
          have hbig : ∀ᶠ n : ℕ in atTop, √(Real.log n) ≤ n - N n := by
            obtain ⟨C, hC⟩ := hupper (κ+1) (by linarith)
            have h2 : ∀ᶠ n : ℕ in atTop, Real.log n / n < 1 / (2 * (κ + 2)) :=
              hlogn.eventually_lt_const (by positivity)
            filter_upwards [hC, h2, hlogtop.eventually_ge_atTop 1, eventually_ge_atTop 1,
              (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * C)] with n a1 a2 a3 a4 a5
            have hnpos : (0:ℝ) < n := by exact_mod_cast a4
            have hsq : √(Real.log n) ≤ Real.log n := by
              rw [Real.sqrt_le_left (by linarith)]
              nlinarith
            rw [div_lt_div_iff₀ hnpos (by positivity)] at a2
            nlinarith
          have hlower : ∀ V, 0 < V → V < κ → ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, V * Real.log n - C ≤ N n := by
            intro V hV0 hV
            have h1 : ∀ᶠ n : ℕ in atTop, V * Real.log n ≤ τ n := by
              filter_upwards [hτ.eventually_const_lt hV, hlogtop.eventually_gt_atTop 0] with n hn hl
              rw [lt_div_iff₀ hl] at hn
              exact hn.le
            obtain ⟨n0, hn0⟩ := eventually_atTop.1 (((h1.and hlow).and hbig).and
              ((eventually_ge_atTop 1).and
                ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop V)))
            refine ⟨V * Real.log n0 + 1, eventually_atTop.2 ⟨n0, fun n hn => ?_⟩⟩
            induction n, hn using Nat.le_induction with
            | base => linarith [hN0 n0]
            | succ n hn ih =>
              obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4, a5⟩ := hn0 n hn
              have hnpos : (0:ℝ) < n := by exact_mod_cast a4
              have hl : Real.log ((n+1 : ℕ):ℝ) - Real.log n ≤ 1 / n := by
                rw [← Real.log_div (by positivity) (by positivity)]
                have := Real.log_le_sub_one_of_pos (x := ((n+1:ℕ):ℝ)/n) (by positivity)
                refine this.trans (le_of_eq ?_)
                push_cast
                field_simp
                ring
              have hl' : V * (Real.log ((n+1 : ℕ):ℝ) - Real.log n) ≤ 1 := by
                refine (mul_le_mul_of_nonneg_left hl hV0.le).trans ?_
                rw [mul_one_div, div_le_one hnpos]
                exact a5
              rcases hstep n with ⟨hA, h⟩ | ⟨hA, h⟩
              · rw [h]; linarith
              · have h3 : τ n ≤ N n := by
                  by_contra hcon
                  exact hA (a2 (not_le.1 hcon) a3)
                have h0 : 0 ≤ V * Real.log n0 := mul_nonneg hV0.le (Real.log_natCast_nonneg n0)
                rw [h]; linarith
          rw [Metric.tendsto_atTop']
          intro ε hε
          obtain ⟨C1, hC1⟩ := hupper (κ + ε/2) (by linarith)
          obtain ⟨V, hV0, hV, hVε⟩ : ∃ V, 0 < V ∧ V < κ ∧ κ - ε/2 ≤ V := by
            refine ⟨max (κ - ε/2) (κ/2), ?_, ?_, le_max_left _ _⟩
            · exact lt_max_of_lt_right (by linarith)
            · exact max_lt (by linarith) (by linarith)
          obtain ⟨C2, hC2⟩ := hlower V hV0 hV
          have hfin : ∀ᶠ n : ℕ in atTop, dist (N n / Real.log n) κ < ε := by
            filter_upwards [hC1, hC2, hlogtop.eventually_gt_atTop 0,
              hlogtop.eventually_gt_atTop (2 * C1 / ε), hlogtop.eventually_gt_atTop (2 * C2 / ε)]
              with n a1 a2 a3 a4 a5
            rw [div_lt_iff₀ hε] at a4 a5
            rw [Real.dist_eq, abs_lt]
            constructor
            · rw [lt_sub_iff_add_lt, lt_div_iff₀ a3]
              nlinarith
            · rw [sub_lt_iff_lt_add, div_lt_iff₀ a3]
              nlinarith
          obtain ⟨n0, h⟩ := eventually_atTop.1 hfin
          exact ⟨n0, fun n hn => h n hn.le⟩
        have hD : ∃ f : (n : ℕ) → BanditHistory 2 n → Fin 2, (∀ n, Measurable (f n)) ∧
            ∀ (x : RewardTable 2) (a : ℕ → Fin 2), (∀ n, a n = f n (realizedHistory x a n)) →
              ∃ (N : Fin 2 → ℕ → ℕ) (E : Fin 2 → ℕ → ℝ) (A : Fin 2 → ℕ → Prop),
                (∀ i n, N i n = armPullCount i (realizedHistory x a n)) ∧
                (∀ i n, 4 ≤ n → E i n = (rewardSum x i (N i n) - √(N i n : ℝ) * x i 0) /
                  ((N i n : ℝ) - √(N i n : ℝ))) ∧
                (∀ i n, (A i n ∧ N i (n+1) = N i n + 1) ∨ (¬ A i n ∧ N i (n+1) = N i n)) ∧
                (∀ n, N 0 n + N 1 n = n) ∧ (∀ i n, 4 ≤ n → 2 ≤ N i n) ∧ (∀ n, A 0 n ↔ ¬ A 1 n) ∧
                (∀ n, 4 ≤ n → (A 0 n ↔ ((N 0 n : ℝ) < √(Real.log n) ∨ (¬ ((N 1 n : ℝ) < √(Real.log n)) ∧
                  ((E 0 n < E 1 n ∧ (N 0 n : ℝ) < 2 * Real.log n / (E 0 n - E 1 n) ^ 2) ∨
                   (¬ (E 0 n < E 1 n) ∧ ¬ (N 1 n : ℝ) < 2 * Real.log n / (E 0 n - E 1 n) ^ 2)))))) := by
          classical
          -- statistics on histories
          let W : (n : ℕ) → Fin 2 → BanditHistory 2 n → ℝ := fun n i h =>
            ∑ t : Fin n, if (h t).1 = i then (h t).2 else 0
          let F : (n : ℕ) → Fin 2 → BanditHistory 2 n → ℝ := fun n i h =>
            if hn : i.val < n then (h ⟨i.val, hn⟩).2 else 0
          let E : (n : ℕ) → Fin 2 → BanditHistory 2 n → ℝ := fun n i h =>
            (W n i h - √(armPullCount i h : ℝ) * F n i h) /
              ((armPullCount i h : ℝ) - √(armPullCount i h : ℝ))
          let S : (n : ℕ) → Set (BanditHistory 2 n) := fun n => {h |
            (armPullCount 0 h : ℝ) < √(Real.log n) ∨ (¬ ((armPullCount 1 h : ℝ) < √(Real.log n)) ∧
                  ((E n 0 h < E n 1 h ∧ (armPullCount 0 h : ℝ) < 2 * Real.log n / (E n 0 h - E n 1 h) ^ 2) ∨
                   (¬ (E n 0 h < E n 1 h) ∧
                    ¬ (armPullCount 1 h : ℝ) < 2 * Real.log n / (E n 0 h - E n 1 h) ^ 2)))}
          have hW : ∀ n i, Measurable (W n i) := by
            intro n i
            refine Finset.measurable_sum _ fun t _ => ?_
            refine Measurable.ite ?_ (measurable_snd.comp (measurable_pi_apply t)) measurable_const
            exact (measurable_fst.comp (measurable_pi_apply t)) (measurableSet_singleton i)
          have hF : ∀ n i, Measurable (F n i) := by
            intro n i
            by_cases hn : i.val < n
            · simp only [F, hn, dif_pos]
              exact measurable_snd.comp (measurable_pi_apply _)
            · simp only [F, hn, dif_neg, not_false_eq_true]
              exact measurable_const
          have hN : ∀ n i, Measurable (fun h : BanditHistory 2 n => (armPullCount i h : ℝ)) := by
            intro n i
            exact (measurable_from_top (f := fun k : ℕ => (k:ℝ))).comp (measurable_count i)
          have hE : ∀ n i, Measurable (E n i) := by
            intro n i
            exact ((hW n i).sub ((hN n i).sqrt.mul (hF n i))).div ((hN n i).sub (hN n i).sqrt)
          have hS : ∀ n, MeasurableSet (S n) := by
            intro n
            have hD : Measurable (fun h => 2 * Real.log n / (E n 0 h - E n 1 h) ^ 2) :=
              (((hE n 0).sub (hE n 1)).pow_const 2).const_div _
            have s1 := measurableSet_lt (hN n 0) (measurable_const (a := √(Real.log n)))
            have s2 := measurableSet_lt (hN n 1) (measurable_const (a := √(Real.log n)))
            have s3 := measurableSet_lt (hE n 0) (hE n 1)
            have s4 := measurableSet_lt (hN n 0) hD
            have s5 := measurableSet_lt (hN n 1) hD
            exact s1.union (s2.compl.inter ((s3.inter s4).union (s3.compl.inter s5.compl)))
          let f : (n : ℕ) → BanditHistory 2 n → Fin 2 := fun n h =>
            if n < 4 then (if n % 2 = 0 then 0 else 1) else if h ∈ S n then 0 else 1
          refine ⟨f, ?_, ?_⟩
          · intro n
            by_cases hn : n < 4
            · simp only [f, hn, if_true]
              exact measurable_const
            · simp only [f, hn, if_false]
              exact Measurable.ite (hS n) measurable_const measurable_const
          intro x a ha
          let N : Fin 2 → ℕ → ℕ := fun i n => ((Finset.range n).filter (fun s => a s = i)).card
          have hNs : ∀ i n, N i (n+1) = N i n + if a n = i then 1 else 0 := by
            intro i n
            simp only [N, Finset.range_add_one, Finset.filter_insert]
            split_ifs with h
            · rw [Finset.card_insert_of_notMem (by simp)]
            · simp
          have hNc : ∀ i n, N i n = armPullCount i (realizedHistory x a n) := by
            intro i n
            have h1 : armPullCount i (realizedHistory x a n)
                = ∑ t : Fin n, if a t = i then 1 else 0 := by
              simp only [armPullCount, realizedHistory, Finset.sum_boole, Nat.cast_id]
              congr 1
              ext t
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact Set.mem_toFinset
            rw [h1, Fin.sum_univ_eq_sum_range (fun t => if a t = i then 1 else 0) n]
            simp [N]
          have hWr : ∀ i n, W n i (realizedHistory x a n) = rewardSum x i (N i n) := by
            intro i n
            have h1 : W n i (realizedHistory x a n) = ∑ t ∈ Finset.range n,
                if a t = i then x (a t) (N (a t) t) else 0 := by
              rw [← Fin.sum_univ_eq_sum_range (fun t => if a t = i then x (a t) (N (a t) t) else 0) n]
              rfl
            rw [h1]
            clear h1
            induction n with
            | zero => simp [N, rewardSum]
            | succ n ih =>
              rw [Finset.sum_range_succ, ih, hNs]
              split_ifs with h
              · subst h
                simp [rewardSum, Finset.sum_range_succ]
              · simp
          have hf4 : ∀ n, n < 4 → a n = if n % 2 = 0 then 0 else 1 := by
            intro n hn
            rw [ha n]
            simp only [f, hn, if_true]
          have a0 : a 0 = 0 := by rw [hf4 0 (by norm_num)]; rfl
          have a1 : a 1 = 1 := by rw [hf4 1 (by norm_num)]; rfl
          have a2 : a 2 = 0 := by rw [hf4 2 (by norm_num)]; rfl
          have a3 : a 3 = 1 := by rw [hf4 3 (by norm_num)]; rfl
          have hN00 : ∀ i, N i 0 = 0 := by intro i; simp [N]
          have hFr : ∀ i n, 4 ≤ n → F n i (realizedHistory x a n) = x i 0 := by
            intro i n hn
            have hi : i.val < n := by omega
            simp only [F, hi, dif_pos, realizedHistory]
            have hai : a i.val = i := by fin_cases i <;> simp [a0, a1]
            rw [hai]
            have hz : N i i.val = 0 := by
              fin_cases i
              · exact hN00 _
              · show N 1 1 = 0
                rw [hNs, hN00, a0]; simp
            exact congrArg (x i) hz
          have hN2 : ∀ i n, 4 ≤ n → 2 ≤ N i n := by
            intro i n hn
            induction n, hn using Nat.le_induction with
            | base =>
              simp only [hNs, hN00, a0, a1, a2, a3]
              fin_cases i <;> simp
            | succ n hn ih => rw [hNs]; omega
          refine ⟨N, fun i n => E n i (realizedHistory x a n), fun i n => a n = i, hNc, ?_, ?_, ?_, hN2, ?_, ?_⟩
          · intro i n hn
            simp only [E]
            rw [hWr, hFr i n hn, ← hNc]
          · intro i n
            rw [hNs]
            by_cases h : a n = i
            · left; simp [h]
            · right; simp [h]
          · intro n
            induction n with
            | zero => simp [hN00]
            | succ n ih =>
              rw [hNs, hNs]
              have : a n = 0 ∨ a n = 1 := by omega
              rcases this with h | h <;> simp [h] <;> omega
          · intro n
            show a n = 0 ↔ ¬ a n = 1
            omega
          · intro n hn
            have h1 : a n = if realizedHistory x a n ∈ S n then 0 else 1 := by
              conv_lhs => rw [ha n]
              simp only [f, not_lt.2 hn, if_false]
            have h2 : a n = 0 ↔ realizedHistory x a n ∈ S n := by
              rw [h1]; split_ifs with h <;> simp [h]
            show a n = 0 ↔ _
            rw [h2]
            simp only [S, Set.mem_ofPred_eq, hNc]
        have hE : ∀ (ν : RestedEnvironment 2) (π : BanditPolicy 2)
            (f : (n : ℕ) → BanditHistory 2 n → Fin 2) (hf : ∀ n, Measurable (f n)),
            (∀ n, π.select n = Kernel.deterministic (f n) (hf n)) →
            ∃ (a : RewardTable 2 → ℕ → Fin 2),
              (∀ x n, a x n = f n (realizedHistory x (a x) n)) ∧
              ∀ T, processMeasure ν π T = ν.law.map (fun x => realizedHistory x (a x) T) ∧
                Measurable (fun x => realizedHistory x (a x) T) := by
          intro ν π f hf hπ
          let H : RewardTable 2 → (n : ℕ) → BanditHistory 2 n := fun x n =>
            Nat.rec (motive := fun n => BanditHistory 2 n) (fun t => t.elim0)
              (fun n h => (reveal ((x, h), f n h)).2) n
          have hHs : ∀ x n, H x (n+1) = (reveal ((x, H x n), f n (H x n))).2 := fun x n => rfl
          let a : RewardTable 2 → ℕ → Fin 2 := fun x n => f n (H x n)
          have hHr : ∀ x n, H x n = realizedHistory x (a x) n := by
            intro x n
            induction n with
            | zero => funext t; exact t.elim0
            | succ n ih =>
              rw [hHs]
              funext t
              refine Fin.lastCases ?_ (fun t => ?_) t
              · simp only [reveal, Fin.snoc_last]
                have hc : armPullCount (f n (H x n)) (H x n)
                    = ((Finset.range n).filter (fun s => a x s = a x n)).card := by
                  rw [show f n (H x n) = a x n from rfl, ih]
                  rw [Finset.card_filter,
                    ← Fin.sum_univ_eq_sum_range (fun s => if a x s = a x n then 1 else 0) n]
                  simp only [armPullCount, realizedHistory, Finset.sum_boole, Nat.cast_id]
                  congr 1
                  ext t
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  exact Set.mem_toFinset
                rw [hc]
                rfl
              · simp only [reveal, Fin.snoc_castSucc]
                rw [ih]
                rfl
          have hHm : ∀ n, Measurable (fun x => H x n) := by
            intro n
            induction n with
            | zero => exact measurable_pi_lambda _ fun t => t.elim0
            | succ n ih =>
              simp_rw [hHs]
              exact measurable_snd.comp (measurable_reveal.comp
                ((measurable_id.prodMk ih).prodMk ((hf n).comp ih)))
          have hj : ∀ n, processJointMeasure ν π n = ν.law.map (fun x => (x, H x n)) := by
            intro n
            induction n with
            | zero => rfl
            | succ n ih =>
              rw [processJointMeasure, hπ n]
              have hk : ((Kernel.deterministic (f n) (hf n)).comap
                  (Prod.snd : RewardTable 2 × BanditHistory 2 n → BanditHistory 2 n) measurable_snd :
                  Kernel (RewardTable 2 × BanditHistory 2 n) (Fin 2))
                  = Kernel.deterministic (fun p : RewardTable 2 × BanditHistory 2 n => f n p.2)
                    ((hf n).comp measurable_snd) := by
                ext p s hs
                simp [Kernel.comap_apply, Kernel.deterministic_apply]
              rw [hk, Measure.compProd_deterministic, ih]
              have m1 : Measurable (fun x => (x, H x n)) := measurable_id.prodMk (hHm n)
              have m2 : Measurable (fun p : RewardTable 2 × BanditHistory 2 n => (p, f n p.2)) :=
                measurable_id.prodMk ((hf n).comp measurable_snd)
              rw [Measure.map_map m2 m1, Measure.map_map measurable_reveal (m2.comp m1)]
              rfl
          refine ⟨a, ?_, ?_⟩
          · intro x n
            rw [← hHr]
          · intro T
            simp_rw [← hHr]
            refine ⟨?_, hHm T⟩
            unfold processMeasure
            rw [hj]
            exact Measure.map_map (g := Prod.snd) (f := fun x => (x, H x T)) measurable_snd (measurable_id.prodMk (hHm T))
        have hF :
          ∃ ν : RestedEnvironment 2,
              IndependentArms ν ∧
              AssumptionOne ν ∧ AssumptionTwo ν ∧
              FitsFamily (gaussianReal 0 1) ν ∧
              (∀ (i : Fin 2) (θ : ℝ), limitingCGF ν i θ =
                (((if i = 0 then 1 else 0 : ℝ) * θ + θ ^ 2 / 2 : ℝ) : EReal)) ∧
              processMean ν 0 = 1 ∧ processMean ν 1 = 0 ∧
              processTailExponent (gaussianReal 0 1) ν 1 = 1 ∧
            (∃ A : Set (RewardTable 2), MeasurableSet A ∧ (∀ᵐ x ∂ν.law, x ∈ A) ∧
              ∀ x ∈ A, ∃ z : Fin 2 → ℝ, ∀ i (n : ℕ),
                rewardSum x i n = n * (if i = 0 then 1 else 0 : ℝ) + √(n:ℝ) * z i) := by
          obtain ⟨ν, hind, hcgf, hsupp⟩ := hB
          obtain ⟨hA1, hA2⟩ := hA
          have htend : ∀ (i : Fin 2) (θ : ℝ), Tendsto (fun n => scaledCGF ν i n θ) atTop
              (𝓝 (((if i = 0 then 1 else 0 : ℝ) * θ + θ ^ 2 / 2 : ℝ) : EReal)) := by
            intro i θ
            refine tendsto_const_nhds.congr' ?_
            filter_upwards [eventually_ge_atTop 1] with n hn
            exact (hcgf i n θ hn).symm
          have hlim : ∀ (i : Fin 2) (θ : ℝ), limitingCGF ν i θ =
                (((if i = 0 then 1 else 0 : ℝ) * θ + θ ^ 2 / 2 : ℝ) : EReal) := by
            intro i θ
            have hex : ∃ L : EReal, Tendsto (fun n => scaledCGF ν i n θ) atTop (𝓝 L) := ⟨_, htend i θ⟩
            unfold limitingCGF
            rw [dif_pos hex]
            exact tendsto_nhds_unique hex.choose_spec (htend i θ)
          have hTheta : ∀ i, processTheta ν i = Set.univ := by
            intro i
            unfold processTheta
            have : {θ | limitingCGF ν i θ < ⊤} = Set.univ := by
              refine Set.eq_univ_of_forall fun θ => ?_
              show limitingCGF ν i θ < ⊤
              rw [hlim]
              exact EReal.coe_lt_top _
            rw [this, interior_univ]
          have hreal : ∀ i, realCGF ν i = fun θ => (if i = 0 then 1 else 0 : ℝ) * θ + θ ^ 2 / 2 := by
            intro i
            funext θ
            unfold realCGF
            rw [hlim, EReal.toReal_coe]
          have hderiv : ∀ i θ, HasDerivAt (realCGF ν i) ((if i = 0 then 1 else 0 : ℝ) + θ) θ := by
            intro i θ
            rw [hreal]
            have h1 := ((hasDerivAt_id θ).const_mul (if i = 0 then 1 else 0 : ℝ)).add
              (((hasDerivAt_id θ).pow 2).div_const 2)
            refine (h1.congr_deriv ?_)
            simp
          have hmean : ∀ i, processMean ν i = (if i = 0 then 1 else 0 : ℝ) := by
            intro i
            unfold processMean
            rw [(hderiv i 0).deriv, add_zero]
          have hrate : ∀ i z, processRate ν i z =
              ENNReal.ofReal ((z - (if i = 0 then 1 else 0 : ℝ)) ^ 2 / 2) := by
            intro i z
            unfold processRate
            have hs : (⨆ θ : ℝ, ((θ * z : ℝ) : EReal) - limitingCGF ν i θ)
                = (((z - (if i = 0 then 1 else 0 : ℝ)) ^ 2 / 2 : ℝ) : EReal) := by
              have hterm0 : ∀ θ : ℝ, ((θ * z : ℝ) : EReal) - limitingCGF ν i θ =
                  ((θ * z - ((if i = 0 then 1 else 0 : ℝ) * θ + θ ^ 2 / 2) : ℝ) : EReal) := by
                intro θ
                rw [hlim, EReal.coe_sub]
              simp_rw [hterm0]
              apply le_antisymm
              · refine iSup_le fun θ => ?_
                rw [EReal.coe_le_coe_iff]
                nlinarith [sq_nonneg (θ - (z - (if i = 0 then 1 else 0 : ℝ)))]
              · refine le_trans (le_of_eq ?_) (le_iSup _ (z - (if i = 0 then 1 else 0 : ℝ)))
                congr 1
                ring
            rw [hs, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
          have hms : ∀ i, processMeanSet ν i = Set.univ := by
            intro i
            unfold processMeanSet
            have : {z | processRate ν i z < ⊤} = Set.univ := by
              refine Set.eq_univ_of_forall fun z => ?_
              show processRate ν i z < ⊤
              rw [hrate]
              exact ENNReal.ofReal_lt_top
            rw [this, interior_univ]
          refine ⟨ν, hind, ⟨?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩, hlim, ?_, ?_, ?_, hsupp⟩
          · intro i θ
            rw [hlim]; exact htend i θ
          · intro i
            rw [hTheta]; trivial
          · intro i
            exact ⟨fun θ _ => (hderiv i θ).differentiableAt.differentiableWithinAt, Or.inl (hTheta i)⟩
          · rw [hA1]; exact Set.ordConnected_univ
          · refine Eventually.of_forall fun x i s => ?_
            rw [hA1]; trivial
          · intro i
            rw [hA1]; exact Set.subset_univ _
          · rw [hmean]; simp
          · rw [hmean]; simp
          · unfold processTailExponent
            have hfil : (Finset.univ.filter (fun j : Fin 2 => processMean ν 1 < processMean ν j)) = {0} := by
              ext j
              simp only [hmean, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
              fin_cases j <;> simp
            rw [hfil, Finset.sum_singleton, hms, Set.univ_inter]
            have hm1 : processMean ν 1 = 0 := by rw [hmean]; simp
            rw [hm1]
            have hterm : ∀ z : ℝ, z < 0 → processRate ν 0 z / dP (gaussianReal 0 1) z 0
                = ENNReal.ofReal ((1 - 1 / z) ^ 2) := by
              intro z hz
              rw [hrate, hA2, ← ENNReal.ofReal_div_of_pos (by nlinarith [sq_pos_of_neg hz])]
              congr 1
              have hz0 : z ≠ 0 := hz.ne
              simp only [if_true]
              field_simp
              try ring
            apply le_antisymm
            · refine ENNReal.le_of_forall_pos_le_add ?_
              intro ε hε _
              have hε' : (0:ℝ) < ε := hε
              have hz : -(1 + 3 / (ε:ℝ)) < 0 := by
                have : 0 < 3 / (ε:ℝ) := by positivity
                linarith
              refine (iInf₂_le (-(1 + 3 / (ε:ℝ))) hz).trans ?_
              rw [hterm _ hz]
              have : (1:ℝ≥0∞) + (ε:ℝ≥0∞) = ENNReal.ofReal (1 + ε) := by
                rw [ENNReal.ofReal_add (by norm_num) hε'.le]; simp
              rw [this]
              apply ENNReal.ofReal_le_ofReal
              have e1 : 1 - 1 / (-(1 + 3 / (ε:ℝ))) = 1 + ε / (ε + 3) := by
                field_simp
                try ring
              rw [e1]
              have e2 : (ε:ℝ) / (ε + 3) * (ε + 3) = ε := by field_simp
              have e3 : 0 < (ε:ℝ) / (ε + 3) := by positivity
              have e4 : (ε:ℝ) / (ε + 3) < 1 := by rw [div_lt_one (by positivity)]; linarith
              nlinarith
            · refine le_iInf₂ fun z hz => ?_
              have hz' : z < 0 := hz
              rw [hterm z hz', ← ENNReal.ofReal_one]
              apply ENNReal.ofReal_le_ofReal
              have : 1 / z < 0 := one_div_neg.2 hz'
              nlinarith
        have hG : ∀ (hC : ∀ (A : ℕ → Prop) (N τ : ℕ → ℝ) (κ : ℝ), 0 < κ →
            (∀ n, (A n ∧ N (n+1) = N n + 1) ∨ (¬ A n ∧ N (n+1) = N n)) →
            (∀ n, 0 ≤ N n) →
            Tendsto (fun n : ℕ => τ n / Real.log n) atTop (𝓝 κ) →
            (∀ᶠ n in atTop, A n → N n < τ n) →
            (∀ᶠ n : ℕ in atTop, N n < τ n → √(Real.log n) ≤ n - N n → A n) →
            Tendsto (fun n : ℕ => N n / Real.log n) atTop (𝓝 κ))
            (x : RewardTable 2) (c : Fin 2 → ℝ) (N : Fin 2 → ℕ → ℕ) (E : Fin 2 → ℕ → ℝ) (A : Fin 2 → ℕ → Prop),
            (∀ i n, 4 ≤ n → E i n = (rewardSum x i (N i n) - √(N i n : ℝ) * x i 0) /
                  ((N i n : ℝ) - √(N i n : ℝ))) →
            (∀ i n, (A i n ∧ N i (n+1) = N i n + 1) ∨ (¬ A i n ∧ N i (n+1) = N i n)) →
            (∀ n, N 0 n + N 1 n = n) → (∀ n, A 0 n ↔ ¬ A 1 n) →
                (∀ n, 4 ≤ n → (A 0 n ↔ ((N 0 n : ℝ) < √(Real.log n) ∨ (¬ ((N 1 n : ℝ) < √(Real.log n)) ∧
                  ((E 0 n < E 1 n ∧ (N 0 n : ℝ) < 2 * Real.log n / (E 0 n - E 1 n) ^ 2) ∨
                   (¬ (E 0 n < E 1 n) ∧ ¬ (N 1 n : ℝ) < 2 * Real.log n / (E 0 n - E 1 n) ^ 2)))))) →
            c 0 ≠ c 1 →
            (∀ i, Tendsto (fun n : ℕ => rewardSum x i n / (n : ℝ)) atTop (𝓝 (c i))) →
            ∀ i b : Fin 2, i ≠ b → c i < c b →
              Tendsto (fun n : ℕ => (N i n : ℝ) / Real.log n) atTop (𝓝 (2 / (c i - c b) ^ 2)) := by
          intro hC x c N E A hE hstep hadd hAA hrule hc hlim
          have hlogtop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
            Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
          have hlogn : Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0) :=
            (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
          have hsqtop : Tendsto (fun n : ℕ => √(Real.log n)) atTop atTop :=
            Real.tendsto_sqrt_atTop.comp hlogtop
          have haddR : ∀ n, (N 0 n : ℝ) + N 1 n = n := by intro n; exact_mod_cast hadd n
          have hsqle : ∀ᶠ n : ℕ in atTop, 2 * √(Real.log n) ≤ n := by
            filter_upwards [hlogn.eventually_lt_const (show (0:ℝ) < 1/2 by norm_num),
              hlogtop.eventually_ge_atTop 1, eventually_ge_atTop 1] with n a1 a2 a3
            have hnpos : (0:ℝ) < n := by exact_mod_cast a3
            have hsq : √(Real.log n) ≤ Real.log n := by
              rw [Real.sqrt_le_left (by linarith)]
              nlinarith
            rw [div_lt_iff₀ hnpos] at a1
            linarith
          have hforce : ∀ i, ∀ᶠ n : ℕ in atTop, (N i n : ℝ) < √(Real.log n) → A i n := by
            intro i
            filter_upwards [hsqle, eventually_ge_atTop 4] with n h1 h2 h3
            have h4 := haddR n
            fin_cases i
            · exact (hrule n h2).2 (Or.inl h3)
            · by_contra hcon
              have h3' : (N 1 n : ℝ) < √(Real.log n) := h3
              rcases (hrule n h2).1 ((hAA n).2 hcon) with h | ⟨h, -⟩
              · linarith
              · exact h h3'
          have hmono : ∀ i, Monotone (N i) := by
            intro i
            refine monotone_nat_of_le_succ fun n => ?_
            rcases hstep i n with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
          have hNtop : ∀ i, Tendsto (N i) atTop atTop := by
            intro i
            refine tendsto_atTop_atTop_of_monotone (hmono i) fun M => ?_
            by_contra hcon
            push Not at hcon
            obtain ⟨n0, hn0⟩ := eventually_atTop.1 ((hforce i).and (hsqtop.eventually_gt_atTop (M:ℝ)))
            have hA : ∀ n ≥ n0, A i n := by
              intro n hn
              obtain ⟨h1, h2⟩ := hn0 n hn
              refine h1 (lt_trans ?_ h2)
              exact_mod_cast hcon n
            have hgrow : ∀ k, k ≤ N i (n0 + k) := by
              intro k
              induction k with
              | zero => simp
              | succ k ih =>
                rcases hstep i (n0 + k) with ⟨-, h⟩ | ⟨h, -⟩
                · rw [← add_assoc, h]; omega
                · exact absurd (hA _ (by omega)) h
            have := hgrow M
            have := hcon (n0 + M)
            omega
          have hestlim : ∀ i, Tendsto (fun k : ℕ => (rewardSum x i k - √(k:ℝ) * x i 0) / ((k:ℝ) - √(k:ℝ)))
              atTop (𝓝 (c i)) := by
            intro i
            have hinv : Tendsto (fun k : ℕ => (√(k:ℝ))⁻¹) atTop (𝓝 0) :=
              (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
            have h1 : Tendsto (fun k : ℕ => (rewardSum x i k / (k:ℝ) - (√(k:ℝ))⁻¹ * x i 0) / (1 - (√(k:ℝ))⁻¹))
                atTop (𝓝 ((c i - 0 * x i 0) / (1 - 0))) :=
              ((hlim i).sub (hinv.mul_const _)).div (tendsto_const_nhds.sub hinv) (by norm_num)
            simp only [zero_mul, sub_zero, div_one] at h1
            refine h1.congr' ?_
            filter_upwards [eventually_ge_atTop 2] with k hk
            have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
            have hs : 0 < √(k:ℝ) := Real.sqrt_pos.2 hkpos
            have hk1 : 1 < √(k:ℝ) := by
              rw [Real.lt_sqrt (by norm_num)]
              have : (2:ℝ) ≤ k := by exact_mod_cast hk
              linarith
            obtain ⟨s, hsd⟩ : ∃ s, s = √(k:ℝ) := ⟨_, rfl⟩
            have hks : (k:ℝ) = s ^ 2 := by rw [hsd, Real.sq_sqrt hkpos.le]
            rw [← hsd] at hs hk1 ⊢
            rw [hks]
            have e1 : s ^ 2 - s ≠ 0 := by nlinarith
            have e2 : 1 - s⁻¹ ≠ 0 := by
              have : s⁻¹ < 1 := inv_lt_one_of_one_lt₀ hk1
              linarith
            rw [div_eq_div_iff e2 e1]
            field_simp
          have hElim : ∀ i, Tendsto (E i) atTop (𝓝 (c i)) := by
            intro i
            refine ((hestlim i).comp (hNtop i)).congr' ?_
            filter_upwards [eventually_ge_atTop 4] with n hn
            exact (hE i n hn).symm
          -- generic conclusion
          have key : ∀ i b : Fin 2, i ≠ b → c i < c b →
              (∀ n, (N i n : ℝ) + N b n = n) →
              (∀ᶠ n : ℕ in atTop, A i n → (N i n : ℝ) < max (√(Real.log n)) (2 * Real.log n / (E 0 n - E 1 n) ^ 2)) →
              (∀ᶠ n : ℕ in atTop, (N i n : ℝ) < max (√(Real.log n)) (2 * Real.log n / (E 0 n - E 1 n) ^ 2) →
                ¬ ((N b n : ℝ) < √(Real.log n)) → A i n) →
              (c 0 - c 1) ^ 2 = (c i - c b) ^ 2 →
              Tendsto (fun n : ℕ => (N i n : ℝ) / Real.log n) atTop (𝓝 (2 / (c i - c b) ^ 2)) := by
            intro i b hib hlt hsum h1 h2 hsq
            have hgap : 0 < (c i - c b) ^ 2 := by
              have : c i - c b ≠ 0 := by linarith [hlt] |> fun h : c i - c b < 0 => h.ne
              positivity
            refine hC (A i) (fun n => (N i n : ℝ))
              (fun n => max (√(Real.log n)) (2 * Real.log n / (E 0 n - E 1 n) ^ 2)) (2 / (c i - c b) ^ 2)
              (by positivity) ?_ (fun n => Nat.cast_nonneg _) ?_ h1 ?_
            · intro n
              rcases hstep i n with ⟨h, h'⟩ | ⟨h, h'⟩
              · left; exact ⟨h, by rw [h']; push_cast; rfl⟩
              · right; exact ⟨h, by rw [h']⟩
            · have hD : Tendsto (fun n => 2 / (E 0 n - E 1 n) ^ 2) atTop (𝓝 (2 / (c i - c b) ^ 2)) := by
                rw [← hsq] at hgap ⊢
                exact tendsto_const_nhds.div (((hElim 0).sub (hElim 1)).pow 2) hgap.ne'
              have hinv : Tendsto (fun n : ℕ => (√(Real.log n))⁻¹) atTop (𝓝 0) := hsqtop.inv_tendsto_atTop
              have hmax := hinv.max hD
              rw [max_eq_right (by positivity)] at hmax
              refine hmax.congr' ?_
              filter_upwards [hlogtop.eventually_gt_atTop 0] with n hn
              rw [← max_div_div_right hn.le]
              congr 1
              · rw [eq_div_iff hn.ne']
                have hs : 0 < √(Real.log n) := Real.sqrt_pos.2 hn
                rw [inv_mul_eq_iff_eq_mul₀ hs.ne', Real.mul_self_sqrt hn.le]
              · field_simp
            · filter_upwards [h2] with n h2 h3 h4
              refine h2 h3 (not_lt.2 ?_)
              have := hsum n
              linarith
          intro i b hib hlt
          have hib' : (i = 0 ∧ b = 1) ∨ (i = 1 ∧ b = 0) := by omega
          rcases hib' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · have hE01 : ∀ᶠ n in atTop, E 0 n < E 1 n := (hElim 0).eventually_lt (hElim 1) hlt
            refine key 0 1 hib hlt haddR ?_ ?_ rfl
            · filter_upwards [hE01, eventually_ge_atTop 4] with n h1 h2 h3
              rcases (hrule n h2).1 h3 with h | ⟨-, ⟨-, h⟩ | ⟨h, -⟩⟩
              · exact lt_max_of_lt_left h
              · exact lt_max_of_lt_right h
              · exact absurd h1 h
            · filter_upwards [hE01, eventually_ge_atTop 4] with n h1 h2 h3 h4
              refine (hrule n h2).2 ?_
              rcases lt_max_iff.1 h3 with h | h
              · exact Or.inl h
              · exact Or.inr ⟨h4, Or.inl ⟨h1, h⟩⟩
          · have hE01 : ∀ᶠ n in atTop, E 1 n < E 0 n := (hElim 1).eventually_lt (hElim 0) hlt
            refine key 1 0 hib hlt (fun n => by rw [add_comm]; exact haddR n) ?_ ?_ (by ring)
            · filter_upwards [hE01, eventually_ge_atTop 4] with n h1 h2 h3
              by_contra hcon
              rw [lt_max_iff, not_or] at hcon
              have := (hrule n h2).2 (Or.inr ⟨hcon.1, Or.inr ⟨not_lt.2 h1.le, hcon.2⟩⟩)
              exact (hAA n).1 this h3
            · filter_upwards [hE01, eventually_ge_atTop 4] with n h1 h2 h3 h4
              by_contra hcon
              rcases (hrule n h2).1 ((hAA n).2 hcon) with h | ⟨h, ⟨h', -⟩ | ⟨-, h'⟩⟩
              · exact h4 h
              · exact absurd h' (not_lt.2 h1.le)
              · rcases lt_max_iff.1 h3 with h5 | h5
                · exact h h5
                · exact h' h5
        have hH : ∀ (z : Fin 2 → ℝ) (x : RewardTable 2) (N : Fin 2 → ℕ → ℕ) (E : Fin 2 → ℕ → ℝ) (A : Fin 2 → ℕ → Prop),
            (∀ i (n : ℕ), rewardSum x i n = n * (if i = 0 then 1 else 0 : ℝ) + √(n:ℝ) * z i) →
            (∀ i n, 4 ≤ n → E i n = (rewardSum x i (N i n) - √(N i n : ℝ) * x i 0) /
                  ((N i n : ℝ) - √(N i n : ℝ))) →
            (∀ i n, (A i n ∧ N i (n+1) = N i n + 1) ∨ (¬ A i n ∧ N i (n+1) = N i n)) →
            (∀ n, N 0 n + N 1 n = n) → (∀ i n, 4 ≤ n → 2 ≤ N i n) → (∀ n, A 0 n ↔ ¬ A 1 n) →
                (∀ n, 4 ≤ n → (A 0 n ↔ ((N 0 n : ℝ) < √(Real.log n) ∨ (¬ ((N 1 n : ℝ) < √(Real.log n)) ∧
                  ((E 0 n < E 1 n ∧ (N 0 n : ℝ) < 2 * Real.log n / (E 0 n - E 1 n) ^ 2) ∨
                   (¬ (E 0 n < E 1 n) ∧ ¬ (N 1 n : ℝ) < 2 * Real.log n / (E 0 n - E 1 n) ^ 2)))))) →
            ∀ n, 4 ≤ n → (N 1 n : ℝ) ≤ 5 + 2 * Real.log n := by
          intro z x N E A hx hE hstep hadd hN2 hAA hrule
          have hE' : ∀ i n, 4 ≤ n → E i n = (if i = 0 then 1 else 0 : ℝ) := by
            intro i n hn
            have h2 : (2:ℝ) ≤ N i n := by exact_mod_cast hN2 i n hn
            have hx0 : x i 0 = (if i = 0 then 1 else 0 : ℝ) + z i := by
              have := hx i 1
              simpa [rewardSum] using this
            rw [hE i n hn, hx, hx0]
            have hk1 : 1 < √(N i n : ℝ) := by
              rw [Real.lt_sqrt (by norm_num)]
              linarith
            obtain ⟨s, hsd⟩ : ∃ s, s = √(N i n : ℝ) := ⟨_, rfl⟩
            have hks : (N i n : ℝ) = s ^ 2 := by rw [hsd, Real.sq_sqrt (by linarith)]
            rw [← hsd] at hk1 ⊢
            rw [hks]
            have e1 : s ^ 2 - s ≠ 0 := by nlinarith
            rw [div_eq_iff e1]
            ring
          intro n hn
          induction n, hn using Nat.le_induction with
          | base =>
            have h1 : N 1 4 ≤ 4 := by have := hadd 4; omega
            have h2 : (N 1 4 : ℝ) ≤ 4 := by exact_mod_cast h1
            have := Real.log_natCast_nonneg 4
            linarith
          | succ n hn ih =>
            have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
            have hl : Real.log n ≤ Real.log ((n+1 : ℕ):ℝ) := by
              apply Real.log_le_log hnpos
              push_cast; linarith
            rcases hstep 1 n with ⟨hA, h⟩ | ⟨hA, h⟩
            · have hcon : ¬ A 0 n := fun h0 => (hAA n).1 h0 hA
              rw [hrule n hn] at hcon
              rw [hE' 0 n hn, hE' 1 n hn] at hcon
              have h3 : (N 1 n : ℝ) < √(Real.log n) ∨ (N 1 n : ℝ) < 2 * Real.log n := by
                by_contra hc
                rw [not_or] at hc
                apply hcon
                right
                refine ⟨hc.1, Or.inr ⟨by norm_num, ?_⟩⟩
                norm_num
                exact not_lt.1 hc.2
              have hl0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
              have hsq : √(Real.log n) ≤ Real.log n + 1 := by
                rw [Real.sqrt_le_left (by linarith)]
                nlinarith
              rw [h]
              push_cast at hl ⊢
              rcases h3 with h3 | h3 <;> linarith
            · rw [h]; linarith
        have hI : ∀ (q : ℕ → ℝ → ℝ≥0∞),
            (∀ n : ℕ, 4 ≤ n → ∀ x : ℝ, 5 + 2 * Real.log n ≤ x → q n x = 0) →
            (∀ γ : ℝ, 0 < γ → γ < 1 →
                ∀ᶠ T : ℕ in atTop, ∀ x ∈ tailWindow γ T, q T x = 0) ∧
              ¬ UniformTailLower q 1 := by
          intro q hq
          have hlogtop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
            Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
          have h1 : (∀ γ : ℝ, 0 < γ → γ < 1 →
                ∀ᶠ T : ℕ in atTop, ∀ x ∈ tailWindow γ T, q T x = 0) := by
            intro γ hγ _
            have h2 : Tendsto (fun n : ℕ => (Real.log n) ^ γ) atTop atTop :=
              (tendsto_rpow_atTop hγ).comp hlogtop
            filter_upwards [h2.eventually_ge_atTop 7, hlogtop.eventually_ge_atTop 1,
              eventually_ge_atTop 4] with T a1 a2 a3 x hx
            refine hq T a3 x (le_trans ?_ hx.1)
            rw [Real.rpow_add (by linarith), Real.rpow_one]
            nlinarith
          refine ⟨h1, fun hU => ?_⟩
          have hb : (1:ℝ≥0∞) < ENNReal.ofReal 2 := by
            rw [← ENNReal.ofReal_one]
            exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
          have h2 := hU (1/2) (by norm_num) (by norm_num) 2 hb
          have hlit : Tendsto (fun n : ℕ => (Real.log n) ^ (3/2 : ℝ) / (n:ℝ)) atTop (𝓝 0) := by
            have := (isLittleO_log_rpow_atTop (r := 2/3) (by norm_num)).tendsto_div_nhds_zero
            have h3 : Tendsto (fun x : ℝ => (Real.log x / x ^ (2/3 : ℝ)) ^ (3/2 : ℝ)) atTop (𝓝 0) := by
              have h4 := this.rpow_const (p := 3/2) (Or.inr (by norm_num))
              rwa [Real.zero_rpow (by norm_num)] at h4
            refine (h3.comp tendsto_natCast_atTop_atTop).congr' ?_
            filter_upwards [eventually_ge_atTop 1] with n hn
            have hnpos : (0:ℝ) < n := by exact_mod_cast hn
            simp only [Function.comp]
            rw [Real.div_rpow (Real.log_natCast_nonneg n) (by positivity), ← Real.rpow_mul hnpos.le]
            norm_num
          have h3 := hlit.eventually_lt_const (show (0:ℝ) < 1/2 by norm_num)
          have h4 := h1 (1/2) (by norm_num) (by norm_num)
          obtain ⟨T, ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := ((((h2.and h3).and h4).and
            (eventually_ge_atTop 4)).and (hlogtop.eventually_ge_atTop 1)).exists
          have hTpos : (0:ℝ) < T := by exact_mod_cast (by omega : 0 < T)
          have hmem : (Real.log T) ^ (1 + 1/2 : ℝ) ∈ tailWindow (1/2) T := by
            refine ⟨le_rfl, ?_⟩
            rw [div_lt_iff₀ hTpos] at a2
            have e : (1 + 1/2 : ℝ) = 3/2 := by norm_num
            rw [e]
            linarith
          have h5 := a1 _ hmem
          rw [a3 _ hmem] at h5
          have h6 : 0 < ((Real.log T) ^ (1 + 1/2 : ℝ)) ^ (-2 : ℝ) := by positivity
          rw [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h5
          linarith
        obtain ⟨ν, h1, h2, h3, h4, h5, h6, h7, h8, S, hSm, hSae, hS⟩ := hF
        obtain ⟨f, hfm, hf⟩ := hD
        let π : BanditPolicy 2 := ⟨fun n => Kernel.deterministic (f n) (hfm n), fun n => inferInstance⟩
        have hconv : IsGaussianPathwiseConvergent π := by
          intro x a c hpath hc hlim b hb i hib
          have ha : ∀ n, a n = f n (realizedHistory x a n) := by
            intro n
            by_contra hne
            apply hpath n
            show Kernel.deterministic (f n) (hfm n) (realizedHistory x a n) {a n} = 0
            rw [Kernel.deterministic_apply, Measure.dirac_apply' _ (measurableSet_singleton _)]
            exact Set.indicator_of_notMem (fun h => hne (Set.mem_singleton_iff.1 h).symm) _
          obtain ⟨N, E, A, g1, g2, g3, g4, g5, g6, g7⟩ := hf x a ha
          have hlt : c i < c b := lt_of_le_of_ne (hb i) (hc.ne hib)
          have hkey := hG hC x c N E A g2 g3 g4 g6 g7 (hc.ne (by decide)) hlim i b hib hlt
          have hpos : 0 < (c i - c b) ^ 2 / 2 := by
            have : c i - c b ≠ 0 := sub_ne_zero.2 hlt.ne
            positivity
          rw [hA.2, ← ENNReal.ofReal_inv_of_pos hpos, inv_div]
          simp_rw [← g1]
          exact (ENNReal.continuous_ofReal.tendsto _).comp hkey
        obtain ⟨a, ha, hpm⟩ := hE ν π f hfm (fun n => rfl)
        have hq : ∀ n : ℕ, 4 ≤ n → ∀ x : ℝ, 5 + 2 * Real.log n ≤ x → processTail ν π 1 n x = 0 := by
          intro n hn x hx
          unfold processTail
          obtain ⟨e1, e2⟩ := hpm n
          have hcm : Measurable (fun h : BanditHistory 2 n => (armPullCount 1 h : ℝ)) :=
            (measurable_from_top (f := fun k : ℕ => (k:ℝ))).comp (measurable_count 1)
          rw [e1, Measure.map_apply e2 (measurableSet_lt measurable_const hcm)]
          refine measure_mono_null ?_ (mem_ae_iff.1 hSae)
          intro y hy hyS
          obtain ⟨z, hz⟩ := hS y hyS
          obtain ⟨N, E, A, g1, g2, g3, g4, g5, g6, g7⟩ := hf y (a y) (ha y)
          have hb := hH z y N E A hz g2 g3 g4 g5 g6 g7 n hn
          have hy' : x < (armPullCount 1 (realizedHistory y (a y) n) : ℝ) := hy
          rw [← g1] at hy'
          linarith
        obtain ⟨t1, t2⟩ := hI (processTail ν π 1) hq
        refine ⟨ν, π, h1, h2, h3, h4, hconv, h5, h6, h7, h8, t1, ?_⟩
        rw [h8]
        exact t2
