-- Prove2me | solution 1 for ForwardRM.Cutoffs.Supplement.cutoff_last_drop_le
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:14:40.886439+00:00
-- url     : https://prove2.me/submissions/cff5186f-b1b6-4d6b-9af8-419f7a2c2e3a

import Mathlib
import Definitions.Def_ForwardRM_Cutoffs_Model
import Definitions.Def_ForwardRM_Cutoffs_ValueFunction
import Definitions.Def_ForwardRM_Cutoffs_Cutoff
import Definitions.Def_ForwardRM_Cutoffs_Supplement_ContinuousModel

open ForwardRM
open ForwardRM.Cutoffs
open ForwardRM.Cutoffs.Supplement

/-- Lemma 6 (Board–Skrzypacz, p. 38). If the arrival rate is Lipschitz on `[0, T]` and
`inf_{[v̲, v̄]} m′ > 0`, there are constants `α > 0` and `h₀ > 0` such that, for every
discretization with `n ≥ 2` periods of length `h = T/n ≤ h₀` and every number of units `k ≥ 2`,
the cutoff falls by at most `αh` in the last period: `x^k_{T−h} − x^k_T ≤ αh`. -/
theorem solution (C : ContinuousModel) (hlip : C.LipschitzRate)
    (hm : C.MarginalRevenueSlopeBounded) :
    ∃ α : ℝ, 0 < α ∧ ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ (n : ℕ) (hn : 1 ≤ n), 2 ≤ n → C.step n ≤ h₀ →
        ∀ k : ℕ, 2 ≤ k →
          (C.discretize n hn).cutoff (n - 1) k - (C.discretize n hn).cutoff n k ≤ α * C.step n := by
            classical
            -- cohort expectation of zero
            have hzero : ∀ (M : ForwardRM.Cutoffs.Model) (s : ℕ), M.cohortExp s (fun _ => 0) = 0 := by
              intro M s
              simp [ForwardRM.Cutoffs.Model.cohortExp, ForwardRM.Cutoffs.Model.cohortLIntegral]
            -- one-period value
            have hval1 : ∀ (M : ForwardRM.Cutoffs.Model) (k : ℕ) (S : Multiset ℝ),
                M.valueAux 1 k S = (Finset.range (min k (Multiset.card S) + 1)).sup'
                  Finset.nonempty_range_add_one (fun j => M.sumTop j S) := by
              intro M k S
              rw [ForwardRM.Cutoffs.Model.valueAux]
              have h0 : ∀ j : ℕ, M.sumTop j S + M.δ * M.cohortExp (M.T + 1 - 0)
                  (fun C => M.valueAux 0 (k - j) (ForwardRM.Cutoffs.dropTop j S + C)) = M.sumTop j S := by
                intro j
                have : (fun C => M.valueAux 0 (k - j) (ForwardRM.Cutoffs.dropTop j S + C)) = fun _ => 0 := by
                  funext C
                  rw [ForwardRM.Cutoffs.Model.valueAux]
                rw [this, hzero]
                ring
              simp only [h0]
            have hvalge : ∀ (M : ForwardRM.Cutoffs.Model) (k : ℕ) (S : Multiset ℝ) (j : ℕ),
                j ≤ k → j ≤ Multiset.card S → M.sumTop j S ≤ M.valueAux 1 k S := by
              intro M k S j h1 h2
              rw [hval1]
              exact Finset.le_sup' (fun j => M.sumTop j S)
                (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_min h1 h2)))
            have hvalle : ∀ (M : ForwardRM.Cutoffs.Model) (k : ℕ) (S : Multiset ℝ) (a : ℝ),
                (∀ j, j ≤ k → j ≤ Multiset.card S → M.sumTop j S ≤ a) → M.valueAux 1 k S ≤ a := by
              intro M k S a h
              rw [hval1]
              apply Finset.sup'_le
              intro j hj
              have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              exact h j (this.trans (min_le_left _ _)) (this.trans (min_le_right _ _))
            have hsum0 : ∀ (M : ForwardRM.Cutoffs.Model) (S : Multiset ℝ), M.sumTop 0 S = 0 := by
              intro M S
              simp [ForwardRM.Cutoffs.Model.sumTop]
            have hvalnn : ∀ (M : ForwardRM.Cutoffs.Model) (k : ℕ) (S : Multiset ℝ),
                0 ≤ M.valueAux 1 k S := by
              intro M k S
              have := hvalge M k S 0 (Nat.zero_le _) (Nat.zero_le _)
              rwa [hsum0] at this
            have hmemsort : ∀ (S : Multiset ℝ) (v : ℝ), v ∈ ForwardRM.Cutoffs.sortDesc S → v ∈ S := by
              intro S v hv
              simpa [ForwardRM.Cutoffs.sortDesc] using hv
            have hlen : ∀ (S : Multiset ℝ), (ForwardRM.Cutoffs.sortDesc S).length = Multiset.card S := by
              intro S
              simp [ForwardRM.Cutoffs.sortDesc]
            have hsumle : ∀ (M : ForwardRM.Cutoffs.Model) (j : ℕ) (S : Multiset ℝ) (B : ℝ) (c : ℕ),
                0 ≤ B → (∀ v ∈ S, M.m v ≤ B) → min j (Multiset.card S) ≤ c → M.sumTop j S ≤ c * B := by
              intro M j S B c hB hS hc
              unfold ForwardRM.Cutoffs.Model.sumTop
              have h1 := List.sum_le_card_nsmul
                (((ForwardRM.Cutoffs.sortDesc S).take j).map M.m) B (by
                  intro x hx
                  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
                  exact hS v (hmemsort S v (List.mem_of_mem_take hv)))
              rw [List.length_map, List.length_take, hlen, nsmul_eq_mul] at h1
              refine h1.trans ?_
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hB
            have hsumall : ∀ (M : ForwardRM.Cutoffs.Model) (S : Multiset ℝ),
                M.sumTop (Multiset.card S) S = (S.map M.m).sum := by
              intro M S
              unfold ForwardRM.Cutoffs.Model.sumTop
              rw [List.take_of_length_le (le_of_eq (hlen S))]
              have : ((ForwardRM.Cutoffs.sortDesc S : List ℝ) : Multiset ℝ) = S := by
                simp [ForwardRM.Cutoffs.sortDesc]
              conv_rhs => rw [← this]
              simp
            -- pointwise bound
            have hpt : ∀ (M : ForwardRM.Cutoffs.Model) (B : ℝ) (k : ℕ) (y : ℝ) (S : Multiset ℝ),
                0 ≤ B → 2 ≤ k → 0 ≤ M.m y → M.m y ≤ B → (∀ v ∈ S, M.m v ≤ B) →
                M.valueAux 1 k (y ::ₘ S) ≤ M.m y +
                  2 * B * ((Multiset.card S : ℝ) * ((Multiset.card S : ℝ) - 1)) + M.valueAux 1 (k - 1) S := by
              intro M B k y S hB hk hy hyB hS
              apply hvalle
              intro j hjk hjS
              rw [Multiset.card_cons] at hjS
              have hW := hvalnn M (k - 1) S
              rcases Nat.lt_or_ge (Multiset.card S) 2 with hlt | hge
              · rcases Nat.lt_or_ge (Multiset.card S) 1 with h0 | h1
                · have hS0 : S = 0 := by
                    apply Multiset.card_eq_zero.mp; omega
                  subst hS0
                  have h := hsumle M j (y ::ₘ 0) (M.m y) 1 hy (by simp) (by simp)
                  simp only [Multiset.card_zero, Nat.cast_zero]
                  push_cast at h
                  nlinarith
                · have hc1 : Multiset.card S = 1 := by omega
                  obtain ⟨v, rfl⟩ := Multiset.card_eq_one.mp hc1
                  have hv : M.m v ≤ M.valueAux 1 (k - 1) {v} := by
                    have h1 := hvalge M (k - 1) {v} 1 (by omega) (by simp)
                    have h2 := hsumall M {v}
                    simp at h2
                    linarith
                  simp only [Multiset.card_singleton, Nat.cast_one]
                  have hj2 : j ≤ 2 := by simpa using hjS
                  interval_cases j
                  · rw [hsum0]; linarith
                  · have h := hsumle M 1 (y ::ₘ {v}) (M.m y + M.valueAux 1 (k-1) {v}) 1 (by linarith)
                      (by
                        intro w hw
                        simp only [Multiset.mem_cons, Multiset.mem_singleton] at hw
                        rcases hw with rfl | rfl <;> linarith) (by simp)
                    push_cast at h
                    linarith
                  · have h := hsumall M (y ::ₘ {v})
                    simp at h
                    linarith
              · have h := hsumle M j (y ::ₘ S) B (Multiset.card S + 1) hB (by
                    intro w hw
                    rcases Multiset.mem_cons.mp hw with rfl | hw
                    · exact hyB
                    · exact hS w hw) (by simp)
                have hN : (2 : ℝ) ≤ (Multiset.card S : ℝ) := by exact_mod_cast hge
                push_cast at h
                have : ((Multiset.card S : ℝ) + 1) * B ≤
                    2 * B * ((Multiset.card S : ℝ) * ((Multiset.card S : ℝ) - 1)) := by
                  have : ((Multiset.card S : ℝ) + 1) ≤
                    2 * ((Multiset.card S : ℝ) * ((Multiset.card S : ℝ) - 1)) := by nlinarith
                  nlinarith
                linarith
            -- values lie in the support almost surely
            have hae : ∀ (M : ForwardRM.Cutoffs.Model) (N : ℕ),
                ∀ᵐ x : Fin N → ℝ ∂(MeasureTheory.Measure.pi fun _ : Fin N => M.law),
                  ∀ v ∈ ForwardRM.Cutoffs.cohort x, v ∈ Set.Icc M.vlo M.vhi := by
              intro M N
              have h1 : ∀ᵐ v ∂M.law, v ∈ Set.Icc M.vlo M.vhi := by
                rw [MeasureTheory.ae_iff]
                have hs : {a | ¬a ∈ Set.Icc M.vlo M.vhi} = (Set.Icc M.vlo M.vhi)ᶜ := rfl
                rw [hs, ForwardRM.Cutoffs.Model.law,
                  MeasureTheory.withDensity_apply _ measurableSet_Icc.compl]
                rw [MeasureTheory.setLIntegral_congr_fun (g := fun _ => 0) measurableSet_Icc.compl]
                · simp
                · intro v hv
                  simp [M.f_eq_zero v hv]
              have h2 : ∀ i : Fin N, ∀ᵐ x : Fin N → ℝ ∂(MeasureTheory.Measure.pi fun _ : Fin N => M.law),
                  x i ∈ Set.Icc M.vlo M.vhi := by
                intro i
                exact (MeasureTheory.Measure.quasiMeasurePreserving_eval (fun _ : Fin N => M.law) i).ae h1
              filter_upwards [MeasureTheory.ae_all_iff.mpr h2] with x hx v hv
              simp only [ForwardRM.Cutoffs.cohort, Multiset.mem_coe, List.mem_ofFn] at hv
              obtain ⟨i, rfl⟩ := hv
              exact hx i
            have hcard : ∀ (N : ℕ) (x : Fin N → ℝ), Multiset.card (ForwardRM.Cutoffs.cohort x) = N := by
              intro N x
              simp [ForwardRM.Cutoffs.cohort]
            have hmB : ∀ (M : ForwardRM.Cutoffs.Model) (v : ℝ), v ∈ Set.Icc M.vlo M.vhi →
                M.m v ≤ M.m M.vhi := by
              intro M v hv
              exact M.m_strictMonoOn.monotoneOn hv (Set.right_mem_Icc.mpr M.vlo_lt_vhi.le) hv.2
            have hBpos : ∀ (M : ForwardRM.Cutoffs.Model), 0 < M.m M.vhi := fun M => M.m_vhi_pos
            -- finiteness
            have hfin : ∀ (M : ForwardRM.Cutoffs.Model) (s k : ℕ),
                M.cohortLIntegral s (fun C => M.valueAux 1 k C) ≠ ⊤ := by
              intro M s k
              have : M.cohortLIntegral s (fun C => M.valueAux 1 k C) ≤ ENNReal.ofReal (k * M.m M.vhi) := by
                unfold ForwardRM.Cutoffs.Model.cohortLIntegral
                calc _ ≤ ∑' N : ℕ, (M.arrivals s N) * ENNReal.ofReal (k * M.m M.vhi) := by
                      apply ENNReal.tsum_le_tsum
                      intro N
                      gcongr
                      calc _ ≤ ∫⁻ x : Fin N → ℝ, ENNReal.ofReal (k * M.m M.vhi)
                            ∂(MeasureTheory.Measure.pi fun _ : Fin N => M.law) := by
                            apply MeasureTheory.lintegral_mono_ae
                            filter_upwards [hae M N] with x hx
                            apply ENNReal.ofReal_le_ofReal
                            apply hvalle
                            intro j hj _
                            exact hsumle M j _ _ k (hBpos M).le (fun v hv => hmB M v (hx v hv))
                              ((min_le_left _ _).trans hj)
                        _ = _ := by simp
                  _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
              exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this
            -- integrated bound
            have hint : ∀ (M : ForwardRM.Cutoffs.Model) (s k : ℕ) (y Q : ℝ), 2 ≤ k →
                y ∈ Set.Icc M.vlo M.vhi → 0 ≤ M.m y → 0 ≤ Q →
                (∑' N : ℕ, (M.arrivals s N) * ENNReal.ofReal ((N : ℝ) * ((N : ℝ) - 1)) ≤ ENNReal.ofReal Q) →
                M.cohortExp s (fun C => M.valueAux 1 k (y ::ₘ C)) ≤
                  M.m y + 2 * M.m M.vhi * Q + M.cohortExp s (fun C => M.valueAux 1 (k - 1) C) := by
              intro M s k y Q hk hy hmy hQ hQs
              have hB := (hBpos M).le
              have hNN : ∀ N : ℕ, (0 : ℝ) ≤ (N : ℝ) * ((N : ℝ) - 1) := by
                intro N
                rcases Nat.eq_zero_or_pos N with rfl | h
                · simp
                · have : (1 : ℝ) ≤ N := by exact_mod_cast h
                  nlinarith
              have hL : M.cohortLIntegral s (fun C => M.valueAux 1 k (y ::ₘ C)) ≤
                  ENNReal.ofReal (M.m y + 2 * M.m M.vhi * Q) +
                    M.cohortLIntegral s (fun C => M.valueAux 1 (k - 1) C) := by
                unfold ForwardRM.Cutoffs.Model.cohortLIntegral
                calc _ ≤ ∑' N : ℕ, ((M.arrivals s N) * ENNReal.ofReal (M.m y) +
                        ENNReal.ofReal (2 * M.m M.vhi) *
                          ((M.arrivals s N) * ENNReal.ofReal ((N : ℝ) * ((N : ℝ) - 1))) +
                        (M.arrivals s N) * ∫⁻ x : Fin N → ℝ,
                          ENNReal.ofReal (M.valueAux 1 (k - 1) (ForwardRM.Cutoffs.cohort x))
                            ∂(MeasureTheory.Measure.pi fun _ : Fin N => M.law)) := by
                      apply ENNReal.tsum_le_tsum
                      intro N
                      have hstep : (∫⁻ x : Fin N → ℝ,
                          ENNReal.ofReal (M.valueAux 1 k (y ::ₘ ForwardRM.Cutoffs.cohort x))
                            ∂(MeasureTheory.Measure.pi fun _ : Fin N => M.law)) ≤
                          (ENNReal.ofReal (M.m y) + ENNReal.ofReal (2 * M.m M.vhi) *
                            ENNReal.ofReal ((N : ℝ) * ((N : ℝ) - 1))) + ∫⁻ x : Fin N → ℝ,
                          ENNReal.ofReal (M.valueAux 1 (k - 1) (ForwardRM.Cutoffs.cohort x))
                            ∂(MeasureTheory.Measure.pi fun _ : Fin N => M.law) := by
                        have hconst : (ENNReal.ofReal (M.m y) + ENNReal.ofReal (2 * M.m M.vhi) *
                            ENNReal.ofReal ((N : ℝ) * ((N : ℝ) - 1))) = ∫⁻ x : Fin N → ℝ,
                            (ENNReal.ofReal (M.m y) + ENNReal.ofReal (2 * M.m M.vhi) *
                            ENNReal.ofReal ((N : ℝ) * ((N : ℝ) - 1)))
                            ∂(MeasureTheory.Measure.pi fun _ : Fin N => M.law) := by simp
                        rw [hconst, ← MeasureTheory.lintegral_add_left measurable_const]
                        apply MeasureTheory.lintegral_mono_ae
                        filter_upwards [hae M N] with x hx
                        rw [← ENNReal.ofReal_mul (by positivity),
                          ← ENNReal.ofReal_add hmy (mul_nonneg (by positivity) (hNN N)),
                          ← ENNReal.ofReal_add (add_nonneg hmy (mul_nonneg (by positivity) (hNN N)))
                            (hvalnn M _ _)]
                        apply ENNReal.ofReal_le_ofReal
                        have := hpt M (M.m M.vhi) k y (ForwardRM.Cutoffs.cohort x) hB hk hmy (hmB M y hy)
                          (fun v hv => hmB M v (hx v hv))
                        rw [hcard] at this
                        exact this
                      calc _ ≤ (M.arrivals s N) * _ := mul_le_mul_right hstep _
                        _ = _ := by ring
                  _ = ENNReal.ofReal (M.m y) + ENNReal.ofReal (2 * M.m M.vhi) *
                        (∑' N : ℕ, (M.arrivals s N) * ENNReal.ofReal ((N : ℝ) * ((N : ℝ) - 1))) +
                        ∑' N : ℕ, (M.arrivals s N) * ∫⁻ x : Fin N → ℝ,
                          ENNReal.ofReal (M.valueAux 1 (k - 1) (ForwardRM.Cutoffs.cohort x))
                            ∂(MeasureTheory.Measure.pi fun _ : Fin N => M.law) := by
                      rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
                        PMF.tsum_coe, one_mul]
                  _ ≤ _ := by
                      rw [ENNReal.ofReal_add hmy (by positivity),
                        ENNReal.ofReal_mul (p := 2 * M.m M.vhi) (q := Q) (by positivity)]
                      gcongr
              have hF := hfin M s (k - 1)
              have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hF⟩) hL
              rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hF, ENNReal.toReal_ofReal (by positivity)] at this
              exact this
            -- Poisson second factorial moment
            have hpois : ∀ l : NNReal, ∑' N : ℕ, (ProbabilityTheory.poissonPMF l N) *
                ENNReal.ofReal ((N : ℝ) * ((N : ℝ) - 1)) ≤ ENNReal.ofReal ((l : ℝ) ^ 2) := by
              intro l
              rw [tsum_eq_zero_add' ENNReal.summable, tsum_eq_zero_add' ENNReal.summable]
              simp only [Nat.cast_zero, zero_mul, ENNReal.ofReal_zero, mul_zero, zero_add, Nat.cast_one,
                sub_self]
              have hterm : ∀ N : ℕ, (ProbabilityTheory.poissonPMF l (N + 1 + 1)) *
                  ENNReal.ofReal (((N + 1 + 1 : ℕ) : ℝ) * (((N + 1 + 1 : ℕ) : ℝ) - 1)) =
                  ENNReal.ofReal ((l : ℝ) ^ 2) * ProbabilityTheory.poissonPMF l N := by
                intro N
                change ENNReal.ofReal (ProbabilityTheory.poissonPMFReal l (N + 1 + 1)) * _ =
                  _ * ENNReal.ofReal (ProbabilityTheory.poissonPMFReal l N)
                rw [← ENNReal.ofReal_mul ProbabilityTheory.poissonPMFReal_nonneg,
                  ← ENNReal.ofReal_mul (by positivity)]
                congr 1
                unfold ProbabilityTheory.poissonPMFReal
                rw [Nat.factorial_succ, Nat.factorial_succ]
                push_cast
                field_simp
                ring
              simp only [hterm]
              rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
            -- constants
            obtain ⟨L, hL⟩ := hlip
            obtain ⟨c, hc, hslope⟩ := hm
            obtain ⟨l0, hl0⟩ : ∃ l0 : ℝ, ∀ s ∈ Set.Icc 0 C.T, ‖C.lam s‖ ≤ l0 :=
              isCompact_Icc.exists_bound_of_continuousOn hL.continuousOn
            have hl0nn : 0 ≤ l0 := (norm_nonneg _).trans (hl0 0 (Set.left_mem_Icc.mpr C.T_pos.le))
            have hcont : ContinuousOn C.m (Set.Icc C.vlo C.vhi) := C.m_contDiffOn.continuousOn
            obtain ⟨x0, hx0, hmx0⟩ : ∃ x0 ∈ Set.Icc C.vlo C.vhi, C.m x0 = 0 := by
              have := intermediate_value_Icc C.vlo_lt_vhi.le hcont
              obtain ⟨x, hx, h⟩ := this (show (0 : ℝ) ∈ Set.Icc (C.m C.vlo) (C.m C.vhi) from
                ⟨C.m_vlo_neg.le, C.m_vhi_pos.le⟩)
              exact ⟨x, hx, h⟩
            have hB : 0 < C.m C.vhi := C.m_vhi_pos
            have hx0lt : x0 < C.vhi := by
              rcases lt_or_eq_of_le hx0.2 with h | h
              · exact h
              · rw [h] at hmx0; linarith
            have hr := C.r_pos
            set α : ℝ := 4 * C.m C.vhi * l0 ^ 2 / (C.r * c) + 1 with hα
            have hαpos : 0 < α := by positivity
            have hαeq : C.r * c * α = 4 * C.m C.vhi * l0 ^ 2 + C.r * c := by
              rw [hα]; field_simp
            refine ⟨α, hαpos, min (1 / C.r) ((C.vhi - x0) / α),
              lt_min (by positivity) (div_pos (by linarith) hαpos), ?_⟩
            intro n hn hn2 hstep k hk
            have hh : 0 < C.step n := C.step_pos hn
            have hrh : C.r * C.step n ≤ 1 := by
              have := hstep.trans (min_le_left _ _)
              rw [le_div_iff₀ hr] at this
              linarith
            have hαh : α * C.step n ≤ C.vhi - x0 := by
              have := hstep.trans (min_le_right _ _)
              rw [le_div_iff₀ hαpos] at this
              linarith
            set D := C.discretize n hn with hD
            -- last-period cutoff
            have hlast : x0 ≤ D.cutoff n k := by
              unfold ForwardRM.Cutoffs.Model.cutoff
              have hdelta : ∀ y, D.deltaPi n k y 0 = C.m y := by
                intro y
                have hpi : ∀ j S, D.piTilde (n + 1) j S = 0 := by
                  intro j S
                  unfold ForwardRM.Cutoffs.Model.piTilde
                  have : (fun A => D.piVal (n + 1) j (S + A)) = fun _ => 0 := by
                    funext A
                    unfold ForwardRM.Cutoffs.Model.piVal
                    have : D.T + 1 - (n + 1) = 0 := by
                      change n + 1 - (n + 1) = 0
                      omega
                    rw [this, ForwardRM.Cutoffs.Model.valueAux]
                  rw [this, hzero]
                unfold ForwardRM.Cutoffs.Model.deltaPi ForwardRM.Cutoffs.Model.sellOneToday
                  ForwardRM.Cutoffs.Model.sellZeroToday
                rw [hpi, hpi]
                simp only [mul_zero, add_zero, sub_zero]
                rfl
              apply le_csInf
              · refine ⟨C.vhi, Set.right_mem_Icc.mpr C.vlo_lt_vhi.le, ?_⟩
                rw [hdelta]; exact hB.le
              · rintro y ⟨hy, hy0⟩
                rw [hdelta] at hy0
                by_contra hlt
                have := C.m_strictMonoOn hy hx0 (not_le.mp hlt)
                change C.m y < C.m x0 at this
                linarith
            have hpen : D.cutoff (n - 1) k ≤ x0 + α * C.step n := by
              unfold ForwardRM.Cutoffs.Model.cutoff
              have hymem : x0 + α * C.step n ∈ Set.Icc C.vlo C.vhi :=
                ⟨by have := hx0.1; nlinarith, by linarith⟩
              apply csInf_le ⟨C.vlo, fun y hy => hy.1.1⟩
              refine ⟨hymem, ?_⟩
              set y := x0 + α * C.step n with hy
              have hmy : c * (α * C.step n) ≤ C.m y := by
                have := hslope x0 hx0 y hymem (by rw [hy]; nlinarith)
                rw [hmx0, hy] at this
                rw [hy]
                linarith
              have hmy0 : 0 ≤ C.m y := le_trans (by positivity) hmy
              have hnn : n - 1 + 1 = n := by omega
              have hT : D.T + 1 - n = 1 := by
                change n + 1 - n = 1
                omega
              unfold ForwardRM.Cutoffs.Model.deltaPi ForwardRM.Cutoffs.Model.sellOneToday
                  ForwardRM.Cutoffs.Model.sellZeroToday ForwardRM.Cutoffs.Model.piTilde
                  ForwardRM.Cutoffs.Model.piVal
              rw [hnn, hT]
              simp only [zero_add, Multiset.cons_add]
              -- arrival mass
              have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
              have hnh : (n : ℝ) * C.step n = C.T := by
                unfold ContinuousModel.step
                field_simp
              have hmass : C.arrivalMass n n ≤ l0 * C.step n := by
                unfold ContinuousModel.arrivalMass
                refine (le_abs_self _).trans ?_
                rw [← Real.norm_eq_abs]
                have hab : ((n : ℝ) - 1) * C.step n ≤ (n : ℝ) * C.step n := by nlinarith
                refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := l0) ?_).trans ?_
                · intro s hs
                  rw [Set.uIoc_of_le hab] at hs
                  apply hl0
                  refine ⟨?_, by rw [← hnh]; exact hs.2⟩
                  have : 0 ≤ ((n : ℝ) - 1) * C.step n := mul_nonneg (by linarith) hh.le
                  linarith [hs.1]
                · apply le_of_eq
                  rw [show (n : ℝ) * C.step n - ((n : ℝ) - 1) * C.step n = C.step n by ring,
                    abs_of_pos hh]
              have hQ : ∑' N : ℕ, (D.arrivals n N) * ENNReal.ofReal ((N : ℝ) * ((N : ℝ) - 1)) ≤
                  ENNReal.ofReal ((l0 * C.step n) ^ 2) := by
                refine (hpois (C.arrivalMass n n).toNNReal).trans ?_
                apply ENNReal.ofReal_le_ofReal
                have : (((C.arrivalMass n n).toNNReal : NNReal) : ℝ) ≤ l0 * C.step n := by
                  rw [Real.coe_toNNReal']
                  exact max_le hmass (by positivity)
                gcongr
              have hmain := hint D n k y ((l0 * C.step n) ^ 2) hk hymem hmy0 (by positivity) hQ
              change _ ≤ C.m y + 2 * C.m C.vhi * (l0 * C.step n) ^ 2 + _ at hmain
              change 0 ≤ C.m y + _ - _
              set V1 := D.cohortExp n (fun A => D.valueAux 1 (k - 1) A)
              set V0 := D.cohortExp n (fun A => D.valueAux 1 k (y ::ₘ A))
              have hδpos := D.δ_pos
              have hδlt := D.δ_lt_one
              have hδ : C.r * C.step n / 2 ≤ 1 - D.δ := by
                change _ ≤ 1 - Real.exp (-(C.r * C.step n))
                have hx : 0 < C.r * C.step n := by positivity
                have h1 := Real.add_one_le_exp (C.r * C.step n)
                have h2 : Real.exp (-(C.r * C.step n)) * Real.exp (C.r * C.step n) = 1 := by
                  rw [← Real.exp_add]; simp
                have h3 := Real.exp_pos (-(C.r * C.step n))
                nlinarith
              have h1 : D.δ * V0 ≤ D.δ * (C.m y + 2 * C.m C.vhi * (l0 * C.step n) ^ 2 + V1) :=
                mul_le_mul_of_nonneg_left hmain hδpos.le
              have h2 : C.r * C.step n / 2 * (c * (α * C.step n)) ≤ (1 - D.δ) * C.m y :=
                mul_le_mul hδ hmy (by positivity) (by linarith)
              have h3 : C.r * C.step n / 2 * (c * (α * C.step n)) =
                  2 * C.m C.vhi * (l0 * C.step n) ^ 2 + C.r * c * (C.step n) ^ 2 / 2 := by
                have : C.r * C.step n / 2 * (c * (α * C.step n)) =
                  (C.r * c * α) * (C.step n) ^ 2 / 2 := by ring
                rw [this, hαeq]; ring
              have h4 : 0 ≤ C.r * c * (C.step n) ^ 2 / 2 := by positivity
              have h5 : 0 ≤ 2 * C.m C.vhi * (l0 * C.step n) ^ 2 := by positivity
              have h6 : D.δ * (2 * C.m C.vhi * (l0 * C.step n) ^ 2) ≤
                  2 * C.m C.vhi * (l0 * C.step n) ^ 2 := mul_le_of_le_one_left h5 hδlt.le
              linarith
            linarith
