-- Prove2me | solution 1 for CarbonFBSDE.MultiPeriod.theorem_2_3
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:31:05.831091+00:00
-- url     : https://prove2.me/submissions/6ac5cc8b-4a06-48a0-8e36-d52213dec384

import Mathlib
import Definitions.Def_CarbonFBSDE_MultiPeriod_Model

open MeasureTheory ProbabilityTheory Filter Set EthierKurtz
open scoped NNReal ENNReal Topology
open CarbonFBSDE.MultiPeriod

namespace CarbonT23Disproof

/-- the counterexample caps: `Λ₁ ≡ 0`, `Λ₂(x) = 0` for `x < 0` and `-1/2` for `x ≥ 0`. -/
noncomputable def Lam (k : ℕ) (x : ℝ) : ℝ :=
  if k = 2 then (if x < 0 then 0 else -1/2) else 0

lemma lam_theta (k : ℕ) : InTheta (Lam k) ∧ CapUnbounded (Lam k) := by
  by_cases hk : k = 2
  · subst hk
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro x y hxy
      simp only [Lam, if_true]
      split_ifs with h1 h2 h2
      · linarith
      · exact absurd (lt_of_le_of_lt hxy h1) h2
      · linarith
      · linarith
    · have : (fun x => Lam 2 x - x) =ᶠ[atTop] fun x => -1/2 - x := by
        filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
        simp [Lam, not_lt.2 hx]
      refine Tendsto.congr' this.symm ?_
      exact tendsto_atBot_add_const_left _ _ tendsto_neg_atTop_atBot
    · have : (fun x => Lam 2 x - x) =ᶠ[atBot] fun x => -x := by
        filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
        simp [Lam, hx]
      exact Tendsto.congr' this.symm tendsto_neg_atBot_atTop
  · have hL : Lam k = fun _ => 0 := by funext x; simp [Lam, hk]
    rw [hL]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro x y hxy; simp only; linarith
    · simpa using tendsto_neg_atTop_atBot
    · unfold CapUnbounded; simpa using tendsto_neg_atBot_atTop

lemma lim_eq {f : ℝ≥0 → ℝ} {a : ℝ≥0} (ha : 0 < a) {c ℓ : ℝ}
    (hf : ∀ t, t < a → f t = c) (h : Tendsto f (𝓝[<] a) (𝓝 ℓ)) : ℓ = c := by
  have : NeBot (𝓝[<] a) := nhdsLT_neBot_of_exists_lt ⟨0, ha⟩
  have h2 : Tendsto f (𝓝[<] a) (𝓝 c) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hf t ht).symm
  exact tendsto_nhds_unique h h2

end CarbonT23Disproof

open CarbonT23Disproof in
theorem solution : ¬ (∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (B : Basis d Ω)
    (hB : B.Valid) (c : Coeffs d) (L l1 l2 : ℝ) (hA : Assumption1 c L l1 l2) (r : ℝ)
    (hr : 0 ≤ r) (q : ℕ) (hq : 1 ≤ q) (Tg : ℕ → ℝ≥0) (hT0 : Tg 0 = 0)
    (hTg : ∀ k < q, Tg k < Tg (k + 1)) (Λ : ℕ → ℝ → ℝ)
    (hΛ : ∀ k, 1 ≤ k → k ≤ q → InTheta (Λ k))
    (hΛu : ∀ k, 1 ≤ k → k ≤ q → CapUnbounded (Λ k)),
    (∀ k0, 1 ≤ k0 → k0 ≤ q → ∀ t0 ∈ Ico (Tg (k0 - 1)) (Tg k0), ∀ (p : SDEState d) (e ee : ℝ),
      (∃ P E Y Z, IsMultiSol B c r q Tg Λ k0 t0 p e ee P E Y Z) ∧
      (∀ P E Y Z P' E' Y' Z', IsMultiSol B c r q Tg Λ k0 t0 p e ee P E Y Z →
        IsMultiSol B c r q Tg Λ k0 t0 p e ee P' E' Y' Z' →
        SolAgree B (Icc t0 (Tg q)) (Icc t0 (Tg q)) t0 (Tg q) P E Y Z P' E' Y' Z')) ∧
    (∀ k0, 1 ≤ k0 → k0 ≤ q → ∀ t0 ∈ Ico (Tg (k0 - 1)) (Tg k0), ∀ (p : SDEState d) (e ee : ℝ)
      P E Y Z, IsMultiSol B c r q Tg Λ k0 t0 p e ee P E Y Z → ∀ k, k0 ≤ k → k ≤ q →
        ∀ᵐ ω ∂B.Pr, ContinuousOn (fun t => Y t ω) (Ico (max t0 (Tg (k - 1))) (Tg k))) ∧
    (∃ v : ℝ≥0 → SDEState d → ℝ → ℝ → ℝ, IsDecField B c r q Tg Λ v) ∧
    (∀ v v' : ℝ≥0 → SDEState d → ℝ → ℝ → ℝ, IsDecField B c r q Tg Λ v →
      IsDecField B c r q Tg Λ v' → ∀ t ≤ Tg q, ∀ p e ee, v t p e ee = v' t p e ee)) := by
  intro H
  -- the deterministic basis on `Ω = Unit`, `d = 0`
  let F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Unit) :=
    ⟨fun _ => inferInstance, fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  let B : Basis 0 Unit := ⟨Measure.dirac (), fun _ _ => 0, F⟩
  have hB : B.Valid := by
    refine ⟨inferInstance, ⟨fun s _ => MeasurableSet.of_discrete⟩, ⟨fun _ => measurable_const,
      fun _ => continuous_const, fun i => i.elim0, iIndepFun.of_subsingleton⟩, fun t => ?_⟩
    ext s
    rcases Set.eq_empty_or_nonempty s with hs | hs
    · subst hs; simp
    · have : s = univ := by
        obtain ⟨x, hx⟩ := hs
        exact Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
      subst this; simp
  let c : Coeffs 0 := ⟨fun _ => 0, fun _ => 0, fun _ y => -y⟩
  have hA : Assumption1 c 1 1 1 := by
    refine ⟨le_rfl, one_pos, one_pos, by norm_num, le_rfl, le_rfl, ?_, ?_, ?_, ?_⟩
    · intro p p'; simp [c]
    · intro p p' y y'
      simp only [c]
      have : |-y - -y'| = |y - y'| := by rw [← abs_neg]; ring_nf
      rw [this]; nlinarith [norm_nonneg (p - p')]
    · intro p x y hxy; simp only [c]; linarith
    · intro p y y'
      simp only [c]
      rw [sq_abs]; constructor <;> nlinarith
  let Tg : ℕ → ℝ≥0 := fun k => (k : ℝ≥0)
  have hTg : ∀ k < 2, Tg k < Tg (k + 1) := by
    intro k _; simp [Tg]
  have H1 := (@H 0 Unit _ B hB c 1 1 1 hA 0 le_rfl 2 (by norm_num) Tg (by simp [Tg]) hTg Lam
    (fun k _ _ => (lam_theta k).1) (fun k _ _ => (lam_theta k).2)).1
  clear H
  obtain ⟨P, E, Y, Z, hS⟩ := (H1 1 le_rfl (by norm_num) 0 (by simp [Tg]) 0 (1/4) (1/4)).1
  obtain ⟨-, -, -, -, -, -, hSE, ⟨JY, -, hPr⟩, hY2, hComp⟩ := hS
  have hpt : ∀ {Q : Unit → Prop}, (∀ᵐ ω ∂B.Pr, Q ω) → Q () := by
    intro Q h
    have h' : ∀ᶠ ω in pure (), Q ω := by
      have : B.Pr = Measure.dirac () := rfl
      rw [this, ae_dirac_eq] at h; exact h
    exact Filter.eventually_pure.1 h'
  have hE := hpt hSE
  have hYT : Y 2 () = 0 := by simpa [Tg] using hpt hY2
  have hC := hpt hComp
  have hP1 := hpt (hPr 1 le_rfl (by norm_num))
  have hP2 := hpt (hPr 2 (by norm_num) le_rfl)
  simp only [Tg, Nat.cast_one, Nat.sub_self, Nat.cast_zero, max_self] at hP1
  simp only [Tg] at hP2
  norm_num at hP2
  -- Y is constant on each period
  have hYa : ∀ t : ℝ≥0, t < 1 → Y t () = Y 0 () := by
    intro t ht
    have := (hP1 0 t le_rfl (by simp) ht).2
    simpa using this
  have hYb : ∀ t : ℝ≥0, 1 ≤ t → t < 2 → Y t () = Y 1 () := by
    intro t h1 h2
    have := (hP2 1 t le_rfl h1 h2).2
    simpa using this
  -- the emissions at `T₁ = 1` and `T₂ = 2`
  have hE1 := hE 1 ⟨by simp, by norm_num⟩
  have hE2 := hE 2 ⟨by simp, by norm_num⟩
  simp only [c, NNReal.coe_zero] at hE1 hE2
  have hne : ∀ a : ℝ, ∀ᵐ x : ℝ ∂volume, x ≠ a := fun a => by
    simpa using (Set.countable_singleton a).ae_notMem volume
  have I1 : ∫ s in (0:ℝ)..(1:ℝ≥0), -Y s.toNNReal () = -Y 0 () := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => -Y 0 ())]
    · simp
    · filter_upwards [hne 1] with x hx hxI
      simp only [NNReal.coe_one] at hxI
      rw [Set.uIoc_of_le zero_le_one] at hxI
      have : x.toNNReal < 1 := by
        rw [Real.toNNReal_lt_one]; exact lt_of_le_of_ne hxI.2 hx
      rw [hYa _ this]
  have I2 : ∫ s in (1:ℝ)..2, -Y s.toNNReal () = -Y 1 () := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => -Y 1 ())]
    · simp; ring
    · filter_upwards [hne 2] with x hx hxI
      rw [Set.uIoc_of_le (by norm_num)] at hxI
      have h1 : (1:ℝ≥0) ≤ x.toNNReal := by
        rw [Real.one_le_toNNReal]; exact hxI.1.le
      have h2 : x.toNNReal < 2 := by
        have : x < 2 := lt_of_le_of_ne hxI.2 hx
        rw [Real.toNNReal_lt_iff_lt_coe (by linarith [hxI.1])]; simpa using this
      rw [hYb _ h1 h2]
  have hsub := intervalIntegral.integral_interval_sub_left hE2.1 hE1.1
  have e1 : E 1 () = 1/4 - Y 0 () := by
    rw [hE1.2, I1]; ring
  have e2 : E 2 () = E 1 () - Y 1 () := by
    have h := hsub
    have hc : ((2:ℝ≥0):ℝ) = 2 := by norm_num
    simp only [NNReal.coe_one, hc] at h hE1 hE2
    rw [I2] at h
    linarith [hE1.2, hE2.2]
  -- compliance at T₁ and T₂
  have hC1 := hC 1 le_rfl (by norm_num)
  have hC2 := hC 2 (by norm_num) le_rfl
  simp only [capArg, Tg, Lam] at hC1 hC2
  norm_num at hC1 hC2
  have L1 : ∀ ℓ, Tendsto (fun t => Y t ()) (𝓝[<] 1) (𝓝 ℓ) → ℓ = Y 0 () :=
    fun ℓ h => lim_eq one_pos hYa h
  have L2 : ∀ ℓ, Tendsto (fun t => Y t ()) (𝓝[<] 2) (𝓝 ℓ) → ℓ = Y 1 () := by
    intro ℓ h
    have : NeBot (𝓝[<] (2:ℝ≥0)) := nhdsLT_neBot_of_exists_lt ⟨0, by norm_num⟩
    refine tendsto_nhds_unique h ?_
    refine tendsto_const_nhds.congr' ?_
    have : Ioo (1:ℝ≥0) 2 ∈ 𝓝[<] (2:ℝ≥0) := Ioo_mem_nhdsLT (by norm_num)
    filter_upwards [this] with t ht
    exact (hYb t ht.1.le ht.2).symm
  obtain ⟨c1a, c1b, c1c⟩ := hC1
  obtain ⟨c2a, c2b, c2c⟩ := hC2
  rw [hYT] at c2a c2c
  set y1 := Y 0 ()
  set y2 := Y 1 ()
  set x := E 1 ()
  rcases lt_trichotomy x 0 with hx | hx | hx
  · -- x < 0: y1 = y2, Λ₂ = 0
    have hy : y1 = y2 := (L1 _ (c1a hx)).symm
    simp only [hx, if_true] at c2a c2b c2c
    have : E 2 () < 0 := by rw [e2]; linarith
    have := L2 _ (c2a this)
    linarith
  · simp only [hx, lt_irrefl, if_false] at c2a c2b c2c
    obtain ⟨ℓ, hℓ, hl1, hl2⟩ := c1c hx
    have hℓ' := L1 _ hℓ
    rcases lt_trichotomy (E 2 ()) (-1/2) with h2 | h2 | h2
    · have := L2 _ (c2a (by linarith)); rw [e2] at h2; linarith
    · obtain ⟨m, hm, -, -⟩ := c2c (by linarith)
      have := L2 _ hm; rw [e2] at h2; linarith
    · have := L2 _ (c2b (by linarith)); rw [e2] at h2; linarith
  · have := L1 _ (c1b hx)
    linarith
