-- Prove2me | solution 1 for FiniteEnergyPlane.exists_exitTime_of_leavesRadiateFrom
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-26T21:39:12.127858+00:00
-- url     : https://prove2.me/submissions/b3f80f8b-c031-405c-8751-b8d15b552edf

import Definitions.Def_FiniteEnergyPlane_SpanningDisk
import Mathlib



/-! Child E of P c5a21fab: `exists_exitTime_of_leavesRadiateFrom`. -/

namespace FiniteEnergyPlane

open Metric Filter Topology Set
open scoped ContDiff

theorem olpe_liou_add (x v w : V 1) : liouville x (v + w) = liouville x v + liouville x w := by
  simp only [liouville, omega0, dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring

theorem olpe_liou_smul (x v : V 1) (a : ℝ) : liouville x (a • v) = a * liouville x v := by
  simp only [liouville, omega0, dot, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

theorem olpe_liou_rot (e : ℂ → V 1) (z : ℂ) :
    liouville (e z) (fderiv ℝ e z (Complex.I * z)) =
      z.re * (charField e z).re + z.im * (charField e z).im := by
  have hw : Complex.I * z = (-z.im) • (1 : ℂ) + z.re • Complex.I := by
    apply Complex.ext <;> simp
  rw [hw, map_add, map_smul, map_smul, olpe_liou_add, olpe_liou_smul, olpe_liou_smul]
  simp only [charField, ds, dt]
  ring

/-- Along a function whose derivative is positive at each of its zeros, a zero is never followed by
a nonpositive value. -/
theorem olpe_eventually_of_deriv_pos {N : ℝ → ℝ} {a d : ℝ} (h : HasDerivAt N d a) (hd : 0 < d) :
    (∀ᶠ s in 𝓝[>] a, N a < N s) ∧ ∀ᶠ s in 𝓝[<] a, N s < N a := by
  have ht := hasDerivAt_iff_tendsto_slope.1 h
  have hev : ∀ᶠ s in 𝓝[≠] a, 0 < slope N a s := ht.eventually (lt_mem_nhds hd)
  constructor
  · have := nhdsWithin_mono a (fun s (hs : a < s) => ne_of_gt hs) hev
    filter_upwards [this, self_mem_nhdsWithin] with s hs hlt
    rw [slope_def_field] at hs
    have : 0 < s - a := sub_pos.2 hlt
    have := (div_pos_iff_of_pos_right this).1 hs
    linarith
  · have := nhdsWithin_mono a (fun s (hs : s < a) => ne_of_lt hs) hev
    filter_upwards [this, self_mem_nhdsWithin] with s hs hlt
    rw [slope_def_field] at hs
    have h1 : s - a < 0 := sub_neg.2 hlt
    have := (div_pos_iff.1 hs)
    rcases this with ⟨h2, h3⟩ | ⟨h2, _⟩
    · linarith
    · linarith

theorem olpe_pos_after {N N' : ℝ → ℝ} (hN : ∀ s, HasDerivAt N (N' s) s)
    (hpos : ∀ s, N s = 0 → 0 < N' s) {b : ℝ} (hb : N b = 0) : ∀ s, b < s → 0 < N s := by
  have hNc : Continuous N := continuous_iff_continuousAt.2 fun s => (hN s).continuousAt
  intro s₂ hs₂
  by_contra hcon
  push_neg at hcon
  obtain ⟨c, hc, hcpos⟩ : ∃ c, b < c ∧ ∀ s ∈ Ioo b c, 0 < N s := by
    have h := (olpe_eventually_of_deriv_pos (hN b) (hpos b hb)).1
    rw [hb] at h
    obtain ⟨c, hc, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 h
    exact ⟨c, hc, fun s hs => hsub hs⟩
  set m := (b + c) / 2 with hm
  have hmI : m ∈ Ioo b c := ⟨by linarith, by linarith⟩
  have hNm : 0 < N m := hcpos m hmI
  have hms₂ : m < s₂ := by
    by_contra h; push_neg at h
    by_cases hsc : s₂ < c
    · exact absurd (hcpos s₂ ⟨hs₂, hsc⟩) (not_lt.2 hcon)
    · push_neg at hsc; linarith [hmI.2]
  set Z : Set ℝ := {s ∈ Icc m s₂ | N s ≤ 0} with hZ
  have hZc : IsClosed Z := isClosed_Icc.inter (isClosed_le hNc continuous_const)
  have hZne : Z.Nonempty := ⟨s₂, ⟨hms₂.le, le_rfl⟩, hcon⟩
  have hZb : BddBelow Z := ⟨m, fun s hs => hs.1.1⟩
  set s₃ := sInf Z with hs₃
  have hs₃Z : s₃ ∈ Z := hZc.csInf_mem hZne hZb
  have hms₃ : m < s₃ := by
    rcases eq_or_lt_of_le hs₃Z.1.1 with h | h
    · exact absurd hs₃Z.2 (by rw [← h]; exact not_le.2 hNm)
    · exact h
  have hbefore : ∀ s ∈ Ico m s₃, 0 < N s := by
    intro s hs
    by_contra h; push_neg at h
    have : s ∈ Z := ⟨⟨hs.1, hs.2.le.trans hs₃Z.1.2⟩, h⟩
    exact absurd (csInf_le hZb this) (not_le.2 hs.2)
  have hIoo : Ioo m s₃ ∈ 𝓝[<] s₃ := Ioo_mem_nhdsLT hms₃
  have hN3 : N s₃ = 0 := by
    refine le_antisymm hs₃Z.2 ?_
    by_contra h; push_neg at h
    have hev : ∀ᶠ s in 𝓝[<] s₃, N s < 0 :=
      nhdsWithin_le_nhds ((hNc.tendsto s₃).eventually (gt_mem_nhds h))
    obtain ⟨s, hs1, hs2⟩ := (hev.and hIoo).exists
    exact absurd (hbefore s ⟨hs2.1.le, hs2.2⟩) (not_lt.2 hs1.le)
  have hev := (olpe_eventually_of_deriv_pos (hN s₃) (hpos s₃ hN3)).2
  rw [hN3] at hev
  obtain ⟨s, hs1, hs2⟩ := (hev.and hIoo).exists
  exact absurd (hbefore s ⟨hs2.1.le, hs2.2⟩) (not_lt.2 hs1.le)

theorem olpe_hasDerivAt_normSq {w : ℝ → ℂ} {w' : ℂ} {s : ℝ} (h : HasDerivAt w w' s) :
    HasDerivAt (fun r => Complex.normSq (w r) - 1)
      (2 * ((w s).re * w'.re + (w s).im * w'.im)) s := by
  have hre : HasDerivAt (fun r => (w r).re) w'.re s :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h
  have him : HasDerivAt (fun r => (w r).im) w'.im s :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt s h
  have := ((hre.mul hre).add (him.mul him)).sub_const 1
  refine (this.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun r => by simp [Complex.normSq_apply]

theorem olpe_norm_lt_one_iff (y : ℂ) : ‖y‖ < 1 ↔ Complex.normSq y - 1 < 0 := by
  rw [Complex.normSq_eq_norm_sq, sub_neg]
  constructor
  · intro h; nlinarith [norm_nonneg y]
  · intro h; by_contra h'; push_neg at h'; nlinarith [norm_nonneg y]

theorem olpe_one_lt_norm_iff (y : ℂ) : 1 < ‖y‖ ↔ 0 < Complex.normSq y - 1 := by
  rw [Complex.normSq_eq_norm_sq, sub_pos]
  constructor
  · intro h; nlinarith [norm_nonneg y]
  · intro h; by_contra h'; push_neg at h'; nlinarith [norm_nonneg y]

theorem exists_exitTime_of_leavesRadiateFrom_aux (e : ℂ → V 1) (he : ContDiff ℝ ∞ e) (z₀ : ℂ)
    (hz₀ : z₀ ∈ ball (0 : ℂ) 1) (hV : charField e z₀ = 0) (hL : LeavesRadiateFrom e z₀)
    (hS : ∀ z ∈ sphere (0 : ℂ) 1, 0 < liouville (e z) (fderiv ℝ e z (Complex.I * z)))
    (X : ℂ → ℂ) (hX : ContDiff ℝ ∞ X) (hXK : HasCompactSupport X)
    (hXV : ∀ z ∈ ball (0 : ℂ) 2, X z = charField e z)
    (ψ : ℝ → ℂ → ℂ) (hψ : Continuous (fun p : ℝ × ℂ => ψ p.1 p.2)) (hψ0 : ∀ y, ψ 0 y = y)
    (hψd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t) :
    ∃ b : ℂ → ℝ, ContinuousOn b (closedBall (0 : ℂ) 1 \ {z₀}) ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, z ≠ z₀ → 0 ≤ b z ∧ (∀ s < b z, ψ s z ∈ ball (0 : ℂ) 1) ∧
        ψ (b z) z ∈ sphere (0 : ℂ) 1 ∧ (∀ s, b z < s → ψ s z ∉ closedBall (0 : ℂ) 1) ∧
        Tendsto (fun s => ψ s z) atBot (𝓝 z₀) ∧ ∀ s, ψ s z ≠ z₀ := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXK hX (by simp)
  have hKs : ∀ t : ℝ, LipschitzOnWith K ((fun _ : ℝ => X) t) ((fun _ : ℝ => (univ : Set ℂ)) t) :=
    fun _ => hK.lipschitzOnWith
  have hcb2 : ∀ y ∈ closedBall (0 : ℂ) 1, y ∈ ball (0 : ℂ) 2 := fun y hy =>
    mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hy) (by norm_num))
  -- outward on the circle
  have hout : ∀ y ∈ sphere (0 : ℂ) 1, 0 < y.re * (X y).re + y.im * (X y).im := by
    intro y hy
    rw [hXV y (hcb2 y (sphere_subset_closedBall hy)), ← olpe_liou_rot]
    exact hS y hy
  -- the flow through `z₀` is constant, so no other orbit reaches `z₀`
  have hX0 : X z₀ = 0 := by rw [hXV z₀ (hcb2 z₀ (ball_subset_closedBall hz₀)), hV]
  have hconst : ∀ t : ℝ, HasDerivAt (fun _ : ℝ => z₀) (X z₀) t := fun t => by
    rw [hX0]; exact hasDerivAt_const t z₀
  have hne : ∀ z, z ≠ z₀ → ∀ s, ψ s z ≠ z₀ := by
    intro z hz s hs
    rcases le_total 0 s with h | h
    · have := ODE_solution_unique_of_mem_Icc_left (v := fun _ => X) (s := fun _ => univ) (K := K)
        (fun t _ => hKs t)
        (fun t _ => (hψd t z).continuousAt.continuousWithinAt)
        (fun t _ => (hψd t z).hasDerivWithinAt) (fun _ _ => mem_univ _)
        (fun t _ => (hconst t).continuousAt.continuousWithinAt)
        (fun t _ => (hconst t).hasDerivWithinAt) (fun _ _ => mem_univ _) hs
        (show (0 : ℝ) ∈ Icc 0 s from ⟨le_rfl, h⟩)
      exact hz (by simpa [hψ0] using this)
    · have := ODE_solution_unique_of_mem_Icc_right (v := fun _ => X) (s := fun _ => univ) (K := K)
        (fun t _ => hKs t)
        (fun t _ => (hψd t z).continuousAt.continuousWithinAt)
        (fun t _ => (hψd t z).hasDerivWithinAt) (fun _ _ => mem_univ _)
        (fun t _ => (hconst t).continuousAt.continuousWithinAt)
        (fun t _ => (hconst t).hasDerivWithinAt) (fun _ _ => mem_univ _) hs
        (show (0 : ℝ) ∈ Icc s 0 from ⟨h, le_rfl⟩)
      exact hz (by simpa [hψ0] using this)
  -- each leaf: identification with the flow, and the exit
  have key : ∀ z ∈ closedBall (0 : ℂ) 1, z ≠ z₀ → ∃ β : ℝ, 0 ≤ β ∧
      (∀ s < β, ψ s z ∈ ball (0 : ℂ) 1) ∧ ψ β z ∈ sphere (0 : ℂ) 1 ∧
      (∀ s, β < s → 1 < ‖ψ s z‖) ∧ Tendsto (fun s => ψ s z) atBot (𝓝 z₀) := by
    intro z hz hz0
    obtain ⟨σ, β, hβ, hσ0, hσt, hσd, hσin, hσb⟩ := hL z hz hz0
    have hσcl : ∀ τ ≤ β, σ τ ∈ closedBall (0 : ℂ) 1 := fun τ hτ => by
      rcases lt_or_eq_of_le hτ with h | h
      · exact ball_subset_closedBall (hσin τ h)
      · rw [h]; exact sphere_subset_closedBall hσb
    have hσd' : ∀ τ ≤ β, HasDerivWithinAt σ (X (σ τ)) (Iic β) τ := fun τ hτ => by
      rw [hXV _ (hcb2 _ (hσcl τ hτ))]; exact hσd τ hτ
    have hσc : ∀ τ ≤ β, ContinuousWithinAt σ (Iic β) τ := fun τ hτ =>
      (hσd' τ hτ).continuousWithinAt
    have hid : ∀ τ ≤ β, ψ τ z = σ τ := by
      intro τ hτ
      rcases le_total τ 0 with h | h
      · have := ODE_solution_unique_of_mem_Icc_left (v := fun _ => X) (s := fun _ => univ) (K := K)
          (a := τ) (b := 0) (f := fun s => ψ s z) (g := σ)
          (fun t _ => hKs t)
          (fun t _ => (hψd t z).continuousAt.continuousWithinAt)
          (fun t _ => (hψd t z).hasDerivWithinAt) (fun _ _ => mem_univ _)
          (fun t ht => (hσc t (ht.2.trans hβ)).mono (fun x hx => hx.2.trans hβ))
          (fun t ht => (hσd' t (ht.2.trans hβ)).mono (Iic_subset_Iic.2 (ht.2.trans hβ)))
          (fun _ _ => mem_univ _) (by simp only [hψ0, hσ0])
        exact this ⟨le_rfl, h⟩
      · have := ODE_solution_unique_of_mem_Icc_right (v := fun _ => X) (s := fun _ => univ) (K := K)
          (a := 0) (b := β) (f := fun s => ψ s z) (g := σ)
          (fun t _ => hKs t)
          (fun t _ => (hψd t z).continuousAt.continuousWithinAt)
          (fun t _ => (hψd t z).hasDerivWithinAt) (fun _ _ => mem_univ _)
          (fun t ht => (hσc t ht.2).mono (fun x hx => hx.2))
          (fun t ht => ((hσd' t ht.2.le).hasDerivAt (Iic_mem_nhds ht.2)).hasDerivWithinAt)
          (fun _ _ => mem_univ _) (by simp only [hψ0, hσ0])
        exact this ⟨h, hτ⟩
    refine ⟨β, hβ, fun s hs => (hid s hs.le) ▸ hσin s hs, (hid β le_rfl) ▸ hσb, ?_, ?_⟩
    · intro s hs
      have hN := fun r => olpe_hasDerivAt_normSq (hψd r z)
      have hpos : ∀ r, Complex.normSq (ψ r z) - 1 = 0 →
          0 < 2 * ((ψ r z).re * (X (ψ r z)).re + (ψ r z).im * (X (ψ r z)).im) := by
        intro r hr
        have : ψ r z ∈ sphere (0 : ℂ) 1 := by
          rw [mem_sphere_zero_iff_norm]
          have h1 : ‖ψ r z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; linarith
          nlinarith [norm_nonneg (ψ r z)]
        linarith [hout _ this]
      have hb0 : Complex.normSq (ψ β z) - 1 = 0 := by
        have h1 := (hid β le_rfl) ▸ hσb
        rw [mem_sphere_zero_iff_norm] at h1
        rw [Complex.normSq_eq_norm_sq, h1]; norm_num
      exact (olpe_one_lt_norm_iff _).2 (olpe_pos_after hN hpos hb0 s hs)
    · refine hσt.congr' ?_
      filter_upwards [eventually_le_atBot β] with s hs
      exact (hid s hs).symm
  classical
  set D := closedBall (0 : ℂ) 1 \ {z₀} with hD
  let b : ℂ → ℝ := fun z => if h : z ∈ closedBall (0 : ℂ) 1 ∧ z ≠ z₀ then
    Classical.choose (key z h.1 h.2) else 0
  have hbspec : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ hz0 : z ≠ z₀, 0 ≤ b z ∧
      (∀ s < b z, ψ s z ∈ ball (0 : ℂ) 1) ∧ ψ (b z) z ∈ sphere (0 : ℂ) 1 ∧
      (∀ s, b z < s → 1 < ‖ψ s z‖) ∧ Tendsto (fun s => ψ s z) atBot (𝓝 z₀) := by
    intro z hz hz0
    have h : z ∈ closedBall (0 : ℂ) 1 ∧ z ≠ z₀ := ⟨hz, hz0⟩
    have := Classical.choose_spec (key z hz hz0)
    simp only [b, dif_pos h]
    exact this
  -- threshold characterization
  have hlt : ∀ z ∈ D, ∀ s, ‖ψ s z‖ < 1 → s < b z := by
    intro z hz s hs
    obtain ⟨-, -, hsph, hgt, -⟩ := hbspec z hz.1 hz.2
    by_contra h; push_neg at h
    rcases eq_or_lt_of_le h with h' | h'
    · rw [h', mem_sphere_zero_iff_norm] at hsph; linarith
    · linarith [hgt s h']
  have hgt' : ∀ z ∈ D, ∀ s, 1 < ‖ψ s z‖ → b z < s := by
    intro z hz s hs
    obtain ⟨-, hin, hsph, -, -⟩ := hbspec z hz.1 hz.2
    by_contra h; push_neg at h
    rcases eq_or_lt_of_le h with h' | h'
    · rw [← h', mem_sphere_zero_iff_norm] at hsph; linarith
    · linarith [mem_ball_zero_iff.1 (hin s h')]
  have hψz : ∀ s, Continuous (fun y => ψ s y) := fun s =>
    hψ.comp (continuous_const.prodMk continuous_id)
  refine ⟨b, ?_, ?_⟩
  · intro z hz
    obtain ⟨-, hin, -, hgt, -⟩ := hbspec z hz.1 hz.2
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · set s := (a + b z) / 2
      have hs : ‖ψ s z‖ < 1 := mem_ball_zero_iff.1 (hin s (by simp only [s]; linarith))
      have hev : ∀ᶠ y in 𝓝[D] z, ‖ψ s y‖ < 1 :=
        nhdsWithin_le_nhds (((hψz s).norm.tendsto z).eventually (gt_mem_nhds hs))
      filter_upwards [hev, self_mem_nhdsWithin] with y hy hyD
      have := hlt y hyD s hy
      simp only [s] at this; linarith
    · set s := (a + b z) / 2
      have hs : 1 < ‖ψ s z‖ := hgt s (by simp only [s]; linarith)
      have hev : ∀ᶠ y in 𝓝[D] z, 1 < ‖ψ s y‖ :=
        nhdsWithin_le_nhds (((hψz s).norm.tendsto z).eventually (lt_mem_nhds hs))
      filter_upwards [hev, self_mem_nhdsWithin] with y hy hyD
      have := hgt' y hyD s hy
      simp only [s] at this; linarith
  · intro z hz hz0
    obtain ⟨h0, hin, hsph, hgt, ht⟩ := hbspec z hz hz0
    refine ⟨h0, hin, hsph, fun s hs hcl => ?_, ht, hne z hz0⟩
    linarith [hgt s hs, mem_closedBall_zero_iff.1 hcl]

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff

theorem solution (e : ℂ → V 1) (he : ContDiff ℝ ∞ e) (z₀ : ℂ)
    (hz₀ : z₀ ∈ ball (0 : ℂ) 1) (hV : charField e z₀ = 0) (hL : LeavesRadiateFrom e z₀)
    (hS : ∀ z ∈ sphere (0 : ℂ) 1, 0 < liouville (e z) (fderiv ℝ e z (Complex.I * z)))
    (X : ℂ → ℂ) (hX : ContDiff ℝ ∞ X) (hXK : HasCompactSupport X)
    (hXV : ∀ z ∈ ball (0 : ℂ) 2, X z = charField e z)
    (ψ : ℝ → ℂ → ℂ) (hψ : Continuous (fun p : ℝ × ℂ => ψ p.1 p.2)) (hψ0 : ∀ y, ψ 0 y = y)
    (hψd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t) :
    ∃ b : ℂ → ℝ, ContinuousOn b (closedBall (0 : ℂ) 1 \ {z₀}) ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, z ≠ z₀ → 0 ≤ b z ∧ (∀ s < b z, ψ s z ∈ ball (0 : ℂ) 1) ∧
        ψ (b z) z ∈ sphere (0 : ℂ) 1 ∧ (∀ s, b z < s → ψ s z ∉ closedBall (0 : ℂ) 1) ∧
        Tendsto (fun s => ψ s z) atBot (𝓝 z₀) ∧ ∀ s, ψ s z ≠ z₀ :=
  exists_exitTime_of_leavesRadiateFrom_aux e he z₀ hz₀ hV hL hS X hX hXK hXV ψ hψ hψ0 hψd
