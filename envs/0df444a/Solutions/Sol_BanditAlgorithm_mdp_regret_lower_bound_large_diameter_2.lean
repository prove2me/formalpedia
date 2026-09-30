-- Prove2me | solution 2 for BanditAlgorithm.mdp_regret_lower_bound_large_diameter
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T10:04:02.236791+00:00
-- url     : https://prove2.me/submissions/6bd316ee-9855-4cd6-85e9-7bdea086c67c

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Theorems.Thm_BanditAlgorithm_mdp_travel_time_le_of_lyapunov_drift
import Theorems.Thm_BanditAlgorithm_mdp_optimal_gain_ge_of_reverse_bellman_ineq

open MeasureTheory ProbabilityTheory

section P2MBandit

open BanditAlgorithm

variable {S : ℕ}

/-- Digit-shift navigation: from state `s`, action `a` moves to `(A * s + a) mod S`. -/
def p2m_nxt {A : ℕ} (hS : 0 < S) (s : Fin S) (a : Fin A) : Fin S :=
  ⟨(A * s + a) % S, Nat.mod_lt _ hS⟩

/-- `p2m_Reach hS tgt k s`: the target `tgt` can be reached from `s` in exactly `k` steps. -/
def p2m_Reach (A : ℕ) (hS : 0 < S) (tgt : Fin S) : ℕ → Fin S → Prop
  | 0, s => s = tgt
  | k + 1, s => ∃ a : Fin A, p2m_Reach A hS tgt k (p2m_nxt hS s a)

lemma p2m_reach_pow {A : ℕ} (hS : 0 < S) (hA : 0 < A) :
    ∀ (k : ℕ) (s : Fin S) (m : ℕ), m < A ^ k →
      p2m_Reach A hS ⟨(A ^ k * s + m) % S, Nat.mod_lt _ hS⟩ k s := by
  intro k
  induction k with
  | zero =>
    intro s m hm
    have hm0 : m = 0 := by simpa using hm
    subst hm0
    show (s : Fin S) = ⟨(A ^ 0 * s + 0) % S, Nat.mod_lt _ hS⟩
    ext
    simp [Nat.mod_eq_of_lt s.isLt]
  | succ k ih =>
    intro s m hm
    have hApos : 0 < A ^ k := pow_pos hA k
    have ha : m / A ^ k < A := by
      rw [Nat.div_lt_iff_lt_mul hApos]
      rw [pow_succ'] at hm
      exact hm
    have hq : m % A ^ k < A ^ k := Nat.mod_lt _ hApos
    refine ⟨⟨m / A ^ k, ha⟩, ?_⟩
    have key := ih (p2m_nxt hS s ⟨m / A ^ k, ha⟩) (m % A ^ k) hq
    have h1 : A ^ k * (A * (s : ℕ) + m / A ^ k) + m % A ^ k = A ^ (k + 1) * s + m := by
      calc A ^ k * (A * (s : ℕ) + m / A ^ k) + m % A ^ k
          = A ^ (k + 1) * s + (A ^ k * (m / A ^ k) + m % A ^ k) := by ring
        _ = A ^ (k + 1) * s + m := by rw [Nat.div_add_mod]
    have hT : (⟨(A ^ k * (p2m_nxt hS s ⟨m / A ^ k, ha⟩ : ℕ) + m % A ^ k) % S, Nat.mod_lt _ hS⟩ : Fin S)
        = ⟨(A ^ (k + 1) * s + m) % S, Nat.mod_lt _ hS⟩ := by
      ext
      simp only [p2m_nxt]
      have h2 : A ^ k * ((A * (s : ℕ) + m / A ^ k) % S) + m % A ^ k
          ≡ A ^ k * (A * (s : ℕ) + m / A ^ k) + m % A ^ k [MOD S] :=
        ((Nat.mod_modEq _ S).mul_left _).add_right _
      unfold Nat.ModEq at h2
      rw [h2, h1]
    rw [hT] at key
    exact key

lemma p2m_reach_log {A : ℕ} (hS : 0 < S) (hA : 1 < A) (tgt s : Fin S) :
    p2m_Reach A hS tgt (Nat.log A S + 1) s := by
  have hlt : S < A ^ (Nat.log A S + 1) := Nat.lt_pow_succ_log_self hA S
  set k := Nat.log A S + 1 with hk
  set x := A ^ k * (s : ℕ) with hx
  have hm : (tgt + (S - x % S)) % S < A ^ k := lt_of_lt_of_le (Nat.mod_lt _ hS) hlt.le
  have key := p2m_reach_pow hS (by omega) k s _ hm
  have hT : (⟨(x + (tgt + (S - x % S)) % S) % S, Nat.mod_lt _ hS⟩ : Fin S) = tgt := by
    ext
    simp only
    have hxr : x % S < S := Nat.mod_lt _ hS
    have h3 : x + (tgt + (S - x % S)) % S ≡ x % S + (tgt + (S - x % S)) [MOD S] :=
      (Nat.mod_modEq x S).symm.add (Nat.mod_modEq _ S)
    have h4 : x % S + (tgt + (S - x % S)) = tgt + S := by omega
    unfold Nat.ModEq at h3
    rw [h3, h4, Nat.add_mod_right, Nat.mod_eq_of_lt tgt.isLt]
  rw [hT] at key
  exact key

lemma p2m_exists_reach {A : ℕ} (hS : 0 < S) (hA : 1 < A) (tgt s : Fin S) :
    ∃ k, p2m_Reach A hS tgt k s := ⟨_, p2m_reach_log hS hA tgt s⟩

open Classical in
/-- BFS distance from `s` to `tgt` in the navigation graph. -/
noncomputable def p2m_dgo {A : ℕ} (hS : 0 < S) (hA : 1 < A) (tgt s : Fin S) : ℕ :=
  Nat.find (p2m_exists_reach hS hA tgt s)

lemma p2m_dgo_spec {A : ℕ} (hS : 0 < S) (hA : 1 < A) (tgt s : Fin S) :
    p2m_Reach A hS tgt (p2m_dgo hS hA tgt s) s := by
  classical
  exact Nat.find_spec (p2m_exists_reach hS hA tgt s)

lemma p2m_dgo_le {A : ℕ} (hS : 0 < S) (hA : 1 < A) (tgt s : Fin S) {k : ℕ} (h : p2m_Reach A hS tgt k s) :
    p2m_dgo hS hA tgt s ≤ k := by
  classical
  exact Nat.find_min' (p2m_exists_reach hS hA tgt s) h

lemma p2m_dgo_le_log {A : ℕ} (hS : 0 < S) (hA : 1 < A) (tgt s : Fin S) :
    p2m_dgo hS hA tgt s ≤ Nat.log A S + 1 :=
  p2m_dgo_le hS hA tgt s (p2m_reach_log hS hA tgt s)

lemma p2m_exists_step {A : ℕ} (hS : 0 < S) (hA : 1 < A) (tgt s : Fin S) (hne : s ≠ tgt) :
    ∃ a : Fin A, p2m_dgo hS hA tgt (p2m_nxt hS s a) + 1 ≤ p2m_dgo hS hA tgt s := by
  have hspec := p2m_dgo_spec hS hA tgt s
  obtain ⟨j, hj⟩ : ∃ j, p2m_dgo hS hA tgt s = j + 1 := by
    rcases Nat.eq_zero_or_pos (p2m_dgo hS hA tgt s) with h0 | hpos
    · exfalso
      rw [h0] at hspec
      exact hne hspec
    · exact ⟨p2m_dgo hS hA tgt s - 1, by omega⟩
  rw [hj] at hspec
  obtain ⟨a, ha⟩ := hspec
  refine ⟨a, ?_⟩
  have := p2m_dgo_le hS hA tgt (p2m_nxt hS s a) ha
  omega

/-- The memoryless navigation policy towards `tgt`. -/
noncomputable def p2m_pol {A : ℕ} (hS : 0 < S) (hA : 1 < A) (tgt : Fin S) (s : Fin S) : Fin A :=
  if h : s = tgt then ⟨0, by omega⟩ else Classical.choose (p2m_exists_step hS hA tgt s h)

lemma p2m_pol_spec {A : ℕ} (hS : 0 < S) (hA : 1 < A) (tgt s : Fin S) (hne : s ≠ tgt) :
    p2m_dgo hS hA tgt (p2m_nxt hS s (p2m_pol hS hA tgt s)) + 1 ≤ p2m_dgo hS hA tgt s := by
  unfold p2m_pol
  rw [dif_neg hne]
  exact Classical.choose_spec (p2m_exists_step hS hA tgt s hne)

/-- The MDP: deterministic digit-shift transitions, reward `1` exactly for action `astar`. -/
noncomputable def p2m_mdp {A : ℕ} (hS : 0 < S) (astar : Fin A) : FiniteMDP S A where
  P s a s' := if s' = p2m_nxt hS s a then 1 else 0
  P_sum_one s a := by simp [Finset.sum_ite_eq']
  r s a := if a = astar then 1 else 0
  r_mem_Icc s a := by split_ifs <;> norm_num

lemma p2m_coe_P {A : ℕ} (hS : 0 < S) (astar : Fin A) (s : Fin S) (a : Fin A) (s' : Fin S) :
    (((p2m_mdp hS astar).P s a s' : NNReal) : ℝ) = if s' = p2m_nxt hS s a then 1 else 0 := by
  simp only [p2m_mdp]
  split_ifs <;> simp

lemma p2m_sumP_eq {A : ℕ} (hS : 0 < S) (astar : Fin A) (s : Fin S) (a : Fin A) (V : Fin S → ℝ) :
    ∑ s', (((p2m_mdp hS astar).P s a s' : NNReal) : ℝ) * V s' = V (p2m_nxt hS s a) := by
  simp [p2m_coe_P, ite_mul, Finset.sum_ite_eq']

lemma p2m_diam_le {A : ℕ} (hS : 0 < S) (hA : 1 < A) (astar : Fin A) (D : ℝ)
    (hD : ((Nat.log A S + 1 : ℕ) : ℝ) ≤ D) :
    mdpDiameterENN (p2m_mdp hS astar) ≤ ENNReal.ofReal D := by
  unfold mdpDiameterENN
  refine iSup_le fun src => iSup_le fun tgt => iSup_le fun _ => ?_
  refine iInf_le_of_le (p2m_pol hS hA tgt) ?_
  refine le_trans (mdp_travel_time_le_of_lyapunov_drift (p2m_mdp hS astar) (p2m_pol hS hA tgt) src tgt
    (fun s => (p2m_dgo hS hA tgt s : ℝ)) (fun s => Nat.cast_nonneg _) ?_) ?_
  · intro s hne
    rw [p2m_sumP_eq]
    have := p2m_pol_spec hS hA tgt s hne
    exact_mod_cast this
  · apply ENNReal.ofReal_le_ofReal
    calc ((p2m_dgo hS hA tgt src : ℕ) : ℝ) ≤ ((Nat.log A S + 1 : ℕ) : ℝ) := by
          exact_mod_cast p2m_dgo_le_log hS hA tgt src
      _ ≤ D := hD

lemma p2m_optimalGain_ge_one {A : ℕ} (hS : 0 < S) (astar : Fin A) :
    (1 : ℝ) ≤ mdpOptimalGain (p2m_mdp hS astar) := by
  refine mdp_optimal_gain_ge_of_reverse_bellman_ineq hS (p2m_mdp hS astar) (fun _ => astar) 1
    (fun _ => 0) 0 0 (fun _ => by simp) ?_
  intro s
  simp [p2m_mdp]

lemma p2m_mdpStepKernel_congr {A : ℕ} {M M' : FiniteMDP S A} (h : M.P = M'.P)
    (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) (n : ℕ) :
    mdpStepKernel M μ0 π n = mdpStepKernel M' μ0 π n := by
  obtain ⟨P, hP, r, hr⟩ := M
  obtain ⟨P', hP', r', hr'⟩ := M'
  simp only at h
  subst h
  cases n <;> rfl

lemma p2m_mdpMeasure_congr {A : ℕ} {M M' : FiniteMDP S A} (h : M.P = M'.P)
    (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) :
    ∀ n, mdpMeasure M μ0 π n = mdpMeasure M' μ0 π n
  | 0 => rfl
  | n + 1 => by
    show ((mdpMeasure M μ0 π n).compProd (mdpStepKernel M μ0 π n)).map
        (fun p ↦ Fin.snoc (α := fun _ ↦ Fin S × Fin A) p.1 p.2)
      = ((mdpMeasure M' μ0 π n).compProd (mdpStepKernel M' μ0 π n)).map
        (fun p ↦ Fin.snoc (α := fun _ ↦ Fin S × Fin A) p.1 p.2)
    rw [p2m_mdpMeasure_congr h μ0 π n, p2m_mdpStepKernel_congr h μ0 π n]

lemma p2m_log_bound (S A : ℕ) (D : ℝ) (hS3 : 3 ≤ S) (hA2 : 2 ≤ A)
    (hD : 20 * (1 + Real.log S / Real.log A) ≤ D) :
    ((Nat.log A S + 1 : ℕ) : ℝ) ≤ D := by
  have hA1 : (1 : ℝ) < A := by exact_mod_cast (show 1 < A by omega)
  have hlogA : 0 < Real.log A := Real.log_pos hA1
  have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast (show 1 ≤ S by omega)
  have hlogS : 0 ≤ Real.log S := Real.log_nonneg hS1
  have hpow : A ^ Nat.log A S ≤ S := Nat.pow_log_le_self A (by omega)
  have hpowR : ((A : ℝ) ^ Nat.log A S) ≤ (S : ℝ) := by exact_mod_cast hpow
  have hApos : (0 : ℝ) < (A : ℝ) ^ Nat.log A S := pow_pos (by linarith) _
  have hlog : (Nat.log A S : ℝ) * Real.log A ≤ Real.log S := by
    have := Real.log_le_log hApos hpowR
    rwa [Real.log_pow] at this
  have hL : (Nat.log A S : ℝ) ≤ Real.log S / Real.log A := by
    rw [le_div_iff₀ hlogA]
    exact hlog
  have hD0 : 20 ≤ D := by
    have : (0 : ℝ) ≤ Real.log S / Real.log A := div_nonneg hlogS hlogA.le
    linarith
  push_cast
  nlinarith

end P2MBandit

open BanditAlgorithm in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ S A n : ℕ, ∀ D : ℝ, 3 ≤ S → 2 ≤ A →
        20 * (1 + Real.log S / Real.log A) ≤ D → D * S * A ≤ n →
        ∀ π : MDPPolicy S A,
          ∃ M : FiniteMDP S A, ∃ μ0 : MDPStateDistribution S,
            mdpDiameterENN M ≤ ENNReal.ofReal D ∧
            C * Real.sqrt (D * S * A * n) ≤
              ∫ h, mdpRegret M n h ∂(mdpMeasure M μ0 π n) := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro S A n D hS3 hA2 hD hn π
  have hS : 0 < S := by omega
  have hA : 1 < A := by omega
  have hA0 : 0 < A := by omega
  let μ0 : MDPStateDistribution S := mdpStateDirac ⟨0, hS⟩
  let a0 : Fin A := ⟨0, hA0⟩
  -- the trajectory law does not depend on the reward function
  let ν : Measure (MDPTrajectory S A n) := mdpMeasure (p2m_mdp hS a0) μ0 π n
  have hν : IsProbabilityMeasure ν := mdpMeasure.instIsProbabilityMeasure _ _ _ _
  have hνM : ∀ a : Fin A, mdpMeasure (p2m_mdp hS a) μ0 π n = ν := fun a =>
    p2m_mdpMeasure_congr (M := p2m_mdp hS a) (M' := p2m_mdp hS a0) rfl μ0 π n
  -- expected number of plays of each action
  let cnt : Fin A → ℝ := fun a =>
    ∫ h, (∑ t, if (h t).2 = a then (1 : ℝ) else 0) ∂ν
  have hint : ∀ (f : MDPTrajectory S A n → ℝ), Integrable f ν := fun f =>
    Integrable.of_finite
  have hsum : ∑ a, cnt a = n := by
    simp only [cnt]
    rw [← integral_finsetSum _ (fun a _ => hint _)]
    have : ∀ h : MDPTrajectory S A n,
        (∑ a : Fin A, ∑ t : Fin n, if (h t).2 = a then (1 : ℝ) else 0) = n := by
      intro h
      rw [Finset.sum_comm]
      simp [Finset.sum_ite_eq]
    simp_rw [this]
    simp
  have hex : ∃ a : Fin A, cnt a ≤ n / A := by
    by_contra hcon
    have hcon' : ∀ a : Fin A, (n / A : ℝ) < cnt a := fun a => lt_of_not_ge (fun h => hcon ⟨a, h⟩)
    have hlt : ∑ a : Fin A, (n / A : ℝ) < ∑ a, cnt a :=
      Finset.sum_lt_sum_of_nonempty ⟨a0, Finset.mem_univ _⟩ (fun a _ => hcon' a)
    rw [hsum] at hlt
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
    have hAne : (A : ℝ) ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ hAne] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨astar, hastar⟩ := hex
  refine ⟨p2m_mdp hS astar, μ0, p2m_diam_le hS hA astar D (p2m_log_bound S A D hS3 hA2 hD), ?_⟩
  rw [hνM astar]
  have hreg : ∫ h, mdpRegret (p2m_mdp hS astar) n h ∂ν
      = n * mdpOptimalGain (p2m_mdp hS astar) - cnt astar := by
    simp only [mdpRegret, mdpTrajectoryReward]
    rw [integral_sub (hint _) (hint _)]
    simp only [integral_const, probReal_univ, one_smul]
    congr 1
  rw [hreg]
  have hρ := p2m_optimalGain_ge_one hS astar
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hA2R : (2 : ℝ) ≤ A := by exact_mod_cast hA2
  have hcnt : cnt astar ≤ n / 2 := by
    refine le_trans hastar ?_
    exact div_le_div_of_nonneg_left hn0 (by norm_num) hA2R
  have hsqrt : Real.sqrt (D * S * A * n) ≤ n := by
    have : D * S * A * n ≤ n * n := mul_le_mul_of_nonneg_right hn hn0
    calc Real.sqrt (D * S * A * n) ≤ Real.sqrt (n * n) := Real.sqrt_le_sqrt this
      _ = n := Real.sqrt_mul_self hn0
  nlinarith
