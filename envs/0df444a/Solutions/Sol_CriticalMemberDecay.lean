-- Prove2me | solution 1 for CriticalMemberDecay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:32:52.089072+00:00
-- url     : https://prove2.me/submissions/125e3d10-1468-40e4-98de-adb63f8a0d51

import Definitions.Def_PHigherOrder_CompactJetFamilyPHarm
import Definitions.Def_PHigherOrder_Rigidity
import Definitions.Def_PHigherOrder_TaylorVanishingDecay
import Definitions.Def_PHigherOrder_IMRegularityInput
import Definitions.Def_PHigherOrder_CriticalMemberDecay
import Theorems.Thm_CompactJetFamilyPHarm
import Theorems.Thm_PHarmRestrict
import Theorems.Thm_Rigidity
import Theorems.Thm_TaylorVanishingDecay


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hL : LewisRigidityInput p) (F : FirstOrderEstimateInput p) (hIM : IMRegularityInput p)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p)
    (z : BoundedContinuousFunction XHalf (ℝ × Plane)) (hz : z ∈ CompactJetFamily p)
    (hcrit : ∀ x : XHalf, (x : Plane) = 0 → (z x).2 = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 4 ∧
      ∀ x : XHalf, ‖(x : Plane)‖ ≤ ρ → |(z x).1| < (1 / 2) * ρ ^ ((k : ℝ) + β) := by
  -- The origin, as a point of `XHalf` and of the open half-ball.
  have hx0mem : (0 : Plane) ∈ Metric.closedBall (0 : Plane) (1 / 2) := by
    rw [Metric.mem_closedBall, dist_self]; norm_num
  have h0inball : (0 : Plane) ∈ Metric.ball (0 : Plane) (1 / 2) := by
    rw [Metric.mem_ball, dist_self]; norm_num
  have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  -- Step 1: the auxiliary exponent `β'`, strictly between `β` and `min 1 (SOpt p - k)`.
  -- The decay is obtained at `k + β'`, and `β' > β` is what makes the final bound strict.
  obtain ⟨μ, hμdef⟩ : ∃ m : ℝ, m = min 1 (SOpt p - (k : ℝ)) := ⟨_, rfl⟩
  have hμ1 : μ ≤ 1 := by rw [hμdef]; exact min_le_left _ _
  have hμs : μ ≤ SOpt p - (k : ℝ) := by rw [hμdef]; exact min_le_right _ _
  have hβμ : β < μ := by
    rw [hμdef]
    exact lt_min hβ1 (by linarith)
  obtain ⟨β', hβ'def⟩ : ∃ b : ℝ, b = (β + μ) / 2 := ⟨_, rfl⟩
  have hββ' : β < β' := by rw [hβ'def]; linarith
  have hβ'μ : β' < μ := by rw [hβ'def]; linarith
  have hβ'0 : 0 < β' := lt_trans hβ0 hββ'
  have hβ'1 : β' < 1 := by linarith
  have hksp : (k : ℝ) + β' < SOpt p := by linarith
  have hdiff : 0 < β' - β := by linarith
  -- Step 2: the `p`-harmonic representative of `z`, and the two vanishing facts at the origin.
  obtain ⟨hzero, hbd, h, G, hph, hagree1, hagree2, hEq⟩ :=
    CompactJetFamilyPHarm p hp hp2 F z hz
  have hh0 : h (0 : Plane) = 0 := by
    have e1 : h (0 : Plane) = (z (⟨0, hx0mem⟩ : XHalf)).1 := hagree1 ⟨0, hx0mem⟩
    rw [e1, hzero ⟨0, hx0mem⟩ rfl]
  have hDh0 : gradient h (0 : Plane) = 0 := by
    have e1 : G (0 : Plane) = (z (⟨0, hx0mem⟩ : XHalf)).2 := hagree2 ⟨0, hx0mem⟩
    have e2 : G (0 : Plane) = gradient h (0 : Plane) := hEq h0inball
    rw [← e2, e1, hcrit ⟨0, hx0mem⟩ rfl]
  -- Step 3: replace the weak gradient `G` by the classical one, pointwise on the half-ball.
  have hclass : IsPHarm p (Metric.ball (0 : Plane) (1 / 2)) h (gradient h) :=
    (PHarmRestrict p hp hp2 (Metric.ball 0 (1 / 2)) h G hph).2 h (gradient h)
      (fun _ _ => rfl) hEq
  -- Step 4: qualitative Iwaniec-Manfredi regularity at the origin, at the exponent `β'`.
  obtain ⟨r, hr0, C, hC0, hrsub, hCk, hhol⟩ :=
    hIM.reg (Metric.ball 0 (1 / 2)) h (gradient h) hclass k β' hβ'0 hβ'1 hksp 0 h0inball
  -- Step 5: diagonal vanishing through order `k`.  Orders `2 ≤ j ≤ k` come from Rigidity;
  -- `j = 0` is `h 0 = 0` and `j = 1` is the critical point.
  have hphr : IsPHarm p (Metric.ball (0 : Plane) r) h (gradient h) :=
    (PHarmRestrict p hp hp2 (Metric.ball 0 (1 / 2)) h (gradient h) hclass).1
      (Metric.ball 0 r) Metric.isOpen_ball hrsub
  have h0r : (0 : Plane) ∈ Metric.ball (0 : Plane) r := Metric.mem_ball_self hr0
  have hrig := Rigidity p hp hp2 hL F (Metric.ball 0 r) h 0 h0r k hk hCk hphr hDh0
  have hvan : ∀ j ≤ k, ∀ w : Plane, iteratedFDeriv ℝ j h 0 (fun _ => w) = 0 := by
    intro j hj w
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · interval_cases j
      · rw [iteratedFDeriv_zero_apply]
        exact hh0
      · rw [iteratedFDeriv_one_apply, ← toDual_gradient, hDh0, map_zero]
        exact zero_apply w
    · exact hrig j hj2 hj w
  -- Step 6: the decay estimate, at the exponent `k + β'`.
  have hdecay := TaylorVanishingDecay h 0 r hr0 k (by omega) β' hβ'0 C hC0.le hCk hvan hhol
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = C / (Nat.factorial k : ℝ) := ⟨_, rfl⟩
  have hfac : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hA0 : 0 < A := by rw [hAdef]; exact div_pos hC0 hfac
  have hAne : A ≠ 0 := ne_of_gt hA0
  -- Step 7: choosing `ρ`.  The margin `β' - β > 0` is cashed here:  `ρ ^ (β' - β)` can be
  -- made as small as needed, which is what buys the paper's factor of `1/2`.
  obtain ⟨s₀, hs₀def⟩ : ∃ s : ℝ, s = (1 / (4 * A)) ^ (1 / (β' - β)) := ⟨_, rfl⟩
  have hbase : (0 : ℝ) < 1 / (4 * A) := div_pos one_pos (by linarith)
  have hs₀pos : 0 < s₀ := by rw [hs₀def]; exact Real.rpow_pos_of_pos hbase _
  have hs₀pow : s₀ ^ (β' - β) = 1 / (4 * A) := by
    rw [hs₀def, ← Real.rpow_mul hbase.le, one_div_mul_cancel (ne_of_gt hdiff), Real.rpow_one]
  have hs₀bd : A * s₀ ^ (β' - β) < 1 / 2 := by
    rw [hs₀pow]
    have : A * (1 / (4 * A)) = 1 / 4 := by field_simp
    rw [this]
    norm_num
  obtain ⟨ρ, hρdef⟩ : ∃ t : ℝ, t = min s₀ (min (r / 2) (1 / 8)) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by
    rw [hρdef]
    exact lt_min hs₀pos (lt_min (by linarith) (by norm_num))
  have hρs : ρ ≤ s₀ := by rw [hρdef]; exact min_le_left _ _
  have hρr : ρ ≤ r / 2 := by
    rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ8 : ρ ≤ 1 / 8 := by
    rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨ρ, hρ0, by linarith, ?_⟩
  intro x hx
  have hxb : (x : Plane) ∈ Metric.ball (0 : Plane) r := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hd := hdecay (x : Plane) hxb
  rw [sub_zero, ← hAdef] at hd
  calc |(z x).1| = |h (x : Plane)| := by rw [hagree1 x]
    _ ≤ A * ‖(x : Plane)‖ ^ ((k : ℝ) + β') := hd
    _ ≤ A * ρ ^ ((k : ℝ) + β') :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) hx (by linarith)) hA0.le
    _ = A * (ρ ^ (β' - β) * ρ ^ ((k : ℝ) + β)) := by
        rw [show (k : ℝ) + β' = (β' - β) + ((k : ℝ) + β) by ring, Real.rpow_add hρ0]
    _ ≤ A * (s₀ ^ (β' - β) * ρ ^ ((k : ℝ) + β)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hρ0.le hρs hdiff.le)
            (Real.rpow_nonneg hρ0.le _)) hA0.le
    _ = A * s₀ ^ (β' - β) * ρ ^ ((k : ℝ) + β) := by ring
    _ < 1 / 2 * ρ ^ ((k : ℝ) + β) :=
        mul_lt_mul_of_pos_right hs₀bd (Real.rpow_pos_of_pos hρ0 _)
