-- Prove2me | solution 1 for DROCalibration.Sensitivity.eq_F_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:17:57.245664+00:00
-- url     : https://prove2.me/submissions/ecab71e2-c513-45b8-8d36-502402495eef

import Mathlib
import Definitions.Def_DROCalibration_Sensitivity_Setting

set_option autoImplicit false
open Filter Topology DROCalibration.Sensitivity

namespace DROHelp

lemma phi_nonneg_all {φ : ℝ → EReal} (hφ : Assumption21 φ) (z : ℝ) : 0 ≤ φ z := by
  rcases lt_or_ge z 0 with h | h
  · rw [hφ.top_of_neg z h]; exact le_top
  · exact hφ.nonneg z h

lemma cd2 {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) (h : ContDiffOn ℝ 2 f s) :
    ContinuousOn (deriv f) s ∧ ContinuousOn (deriv (deriv f)) s ∧
      (∀ x ∈ s, HasDerivAt f (deriv f x) x) ∧
      (∀ x ∈ s, HasDerivAt (deriv f) (deriv (deriv f) x) x) := by
  have h1 : ContDiffOn ℝ (1 + 1 : WithTop ℕ∞) f s := by rwa [one_add_one_eq_two]
  rw [contDiffOn_succ_iff_deriv_of_isOpen hs] at h1
  obtain ⟨hd, -, h2⟩ := h1
  have h2' : ContDiffOn ℝ (0 + 1 : WithTop ℕ∞) (deriv f) s := by rwa [zero_add]
  rw [contDiffOn_succ_iff_deriv_of_isOpen hs] at h2'
  obtain ⟨hd2, -, h3⟩ := h2'
  refine ⟨h2.continuousOn, h3.continuousOn, fun x hx => ?_, fun x hx => ?_⟩
  · exact (hd.differentiableAt (hs.mem_nhds hx)).hasDerivAt
  · exact (hd2.differentiableAt (hs.mem_nhds hx)).hasDerivAt

structure Loc (φ : ℝ → EReal) (r0 : ℝ) : Prop where
  pos : 0 < r0
  le : r0 ≤ 1 / 2
  fin : ∀ z ∈ Set.Ioo (1 - r0) (1 + r0), φ z = ((phiReal φ z : ℝ) : EReal)
  cd : ContDiffOn ℝ 2 (phiReal φ) (Set.Ioo (1 - r0) (1 + r0))
  ppos : ∀ z ∈ Set.Ioo (1 - r0) (1 + r0), 0 < deriv (deriv (phiReal φ)) z

lemma loc {φ : ℝ → EReal} (hφ : Assumption21 φ) : ∃ r0, Loc φ r0 := by
  obtain ⟨ε, hε, hne, hcd⟩ := hφ.smooth
  obtain ⟨-, hc, -, -⟩ := cd2 isOpen_Ioo hcd
  have hpos := hφ.pp_pos
  have hcont : ContinuousAt (deriv (deriv (phiReal φ))) 1 :=
    hc.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))
  have hev : ∀ᶠ z in 𝓝 (1:ℝ), 0 < deriv (deriv (phiReal φ)) z :=
    hcont.tendsto.eventually_const_lt hpos
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hm : 0 < min (min ρ ε) (1 / 2) := by positivity
  have hsub : Set.Ioo (1 - min (min ρ ε) (1 / 2)) (1 + min (min ρ ε) (1 / 2)) ⊆
      Set.Ioo (1 - ε) (1 + ε) := by
    intro z hz
    have := min_le_left (min ρ ε) (1 / 2)
    have := min_le_right ρ ε
    constructor <;> linarith [hz.1, hz.2]
  refine ⟨min (min ρ ε) (1 / 2), ⟨hm, min_le_right _ _, ?_, hcd.mono hsub, ?_⟩⟩
  · intro z hz
    have h := hne z (hsub hz)
    have h0 : (0:EReal) ≤ φ z := phi_nonneg_all hφ z
    have hb : φ z ≠ ⊥ := by
      intro hb; rw [hb] at h0; exact absurd h0 (by simp)
    simp only [phiReal]
    exact (EReal.coe_toReal h hb).symm
  · intro z hz
    apply hball
    rw [Real.dist_eq]
    have := min_le_left (min ρ ε) (1 / 2)
    have := min_le_left ρ ε
    rw [abs_lt]; constructor <;> linarith [hz.1, hz.2]

lemma fin_eq {φ : ℝ → EReal} (hφ : Assumption21 φ) {x : ℝ} (h : φ x ≠ ⊤) :
    φ x = ((phiReal φ x : ℝ) : EReal) := by
  have h0 : (0:EReal) ≤ φ x := phi_nonneg_all hφ x
  have hb : φ x ≠ ⊥ := by
    intro hb; rw [hb] at h0; exact absurd h0 (by simp)
  exact (EReal.coe_toReal h hb).symm

lemma real_convex {φ : ℝ → EReal} (hφ : Assumption21 φ) {w z : ℝ} (hw : φ w ≠ ⊤) (hz : φ z ≠ ⊤)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    φ (θ * w + (1 - θ) * z) ≠ ⊤ ∧
      phiReal φ (θ * w + (1 - θ) * z) ≤ θ * phiReal φ w + (1 - θ) * phiReal φ z := by
  have hc := hφ.convex w z θ h0 h1
  rw [fin_eq hφ hw, fin_eq hφ hz, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hc
  have hne : φ (θ * w + (1 - θ) * z) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hc
  refine ⟨hne, ?_⟩
  rw [fin_eq hφ hne] at hc
  exact_mod_cast hc

lemma tangent {φ : ℝ → EReal} (hφ : Assumption21 φ) {r0 : ℝ} (hl : Loc φ r0) {z : ℝ}
    (hz : z ∈ Set.Ioo (1 - r0) (1 + r0)) {w : ℝ} (hw : φ w ≠ ⊤) :
    phiReal φ z + deriv (phiReal φ) z * (w - z) ≤ phiReal φ w := by
  obtain ⟨-, -, hd, -⟩ := cd2 isOpen_Ioo hl.cd
  have hzt : φ z ≠ ⊤ := by rw [hl.fin z hz]; exact EReal.coe_ne_top _
  have hg : HasDerivAt (fun θ : ℝ => phiReal φ (z + θ * (w - z)))
      (deriv (phiReal φ) z * (w - z)) 0 := by
    have h1 : HasDerivAt (fun θ : ℝ => z + θ * (w - z)) (w - z) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const (w - z)).const_add z
    have h2 : HasDerivAt (phiReal φ) (deriv (phiReal φ) z) (z + 0 * (w - z)) := by
      simpa using hd z hz
    exact h2.comp (0:ℝ) h1
  have ht := hg.tendsto_slope_zero_right
  suffices hs : deriv (phiReal φ) z * (w - z) ≤ phiReal φ w - phiReal φ z by linarith
  refine le_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  have e : z + t * (w - z) = t * w + (1 - t) * z := by ring
  have hh := (real_convex hφ hw hzt ht.1.le ht.2.le).2
  rw [← e] at hh
  simp only [smul_eq_mul, add_zero, zero_mul, zero_add]
  rw [inv_mul_le_iff₀ ht.1]
  nlinarith

lemma strict_cvx {φ : ℝ → EReal} {r0 : ℝ} (hl : Loc φ r0) :
    StrictConvexOn ℝ (Set.Ioo (1 - r0) (1 + r0)) (phiReal φ) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ioo _ _) hl.cd.continuousOn
  intro x hx
  rw [interior_Ioo] at hx
  simpa using hl.ppos x hx

lemma tangent_strict {φ : ℝ → EReal} (hφ : Assumption21 φ) {r0 : ℝ} (hl : Loc φ r0) {z : ℝ}
    (hz : z ∈ Set.Ioo (1 - r0) (1 + r0)) {w : ℝ} (hw : φ w ≠ ⊤) (hne : w ≠ z) :
    phiReal φ z + deriv (phiReal φ) z * (w - z) < phiReal φ w := by
  refine lt_of_le_of_ne (tangent hφ hl hz hw) ?_
  intro heq
  have hzt : φ z ≠ ⊤ := by rw [hl.fin z hz]; exact EReal.coe_ne_top _
  set d := deriv (phiReal φ) z with hd
  have key : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      phiReal φ (z + θ * (w - z)) = phiReal φ z + d * (θ * (w - z)) := by
    intro θ h0 h1
    have e : z + θ * (w - z) = θ * w + (1 - θ) * z := by ring
    obtain ⟨hne', hle⟩ := real_convex hφ hw hzt h0 h1
    rw [← e] at hne' hle
    have h1' := tangent hφ hl hz hne'
    have : z + θ * (w - z) - z = θ * (w - z) := by ring
    rw [this] at h1'
    apply le_antisymm
    · nlinarith
    · exact h1'
  have hρ : 0 < r0 - |z - 1| := by
    have := abs_lt.2 (⟨by linarith [hz.1], by linarith [hz.2]⟩ : -r0 < z - 1 ∧ z - 1 < r0)
    linarith
  set ρ := r0 - |z - 1| with hρdef
  have hdpos : 0 < |w - z| := abs_pos.2 (sub_ne_zero.2 hne)
  set θ0 := min 1 (ρ / (2 * |w - z|)) with hθ0
  have hθ0pos : 0 < θ0 := lt_min one_pos (by positivity)
  have hθ01 : θ0 ≤ 1 := min_le_left _ _
  have hθρ : |θ0 * (w - z)| < ρ := by
    rw [abs_mul, abs_of_pos hθ0pos]
    have h1 : θ0 ≤ ρ / (2 * |w - z|) := min_le_right _ _
    calc θ0 * |w - z| ≤ ρ / (2 * |w - z|) * |w - z| :=
          mul_le_mul_of_nonneg_right h1 hdpos.le
      _ = ρ / 2 := by field_simp
      _ < ρ := by linarith
  have hmem : ∀ θ : ℝ, 0 ≤ θ → θ ≤ θ0 → z + θ * (w - z) ∈ Set.Ioo (1 - r0) (1 + r0) := by
    intro θ h0 h1
    have : |θ * (w - z)| ≤ |θ0 * (w - z)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_pos hθ0pos]
      exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    have h2 := abs_lt.1 (lt_of_le_of_lt this hθρ)
    have h3 := abs_lt.1 (show |z - 1| < r0 by linarith [abs_nonneg (z - 1)])
    have h4 := le_abs_self (z - 1)
    have h5 := neg_abs_le (z - 1)
    constructor <;> linarith [h2.1, h2.2]
  have hu1 := hmem θ0 hθ0pos.le le_rfl
  have hu2 : z + (θ0 / 2) * (w - z) ∈ Set.Ioo (1 - r0) (1 + r0) :=
    hmem _ (by positivity) (by linarith)
  have hne2 : z ≠ z + θ0 * (w - z) := by
    intro h
    have : θ0 * (w - z) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact hθ0pos.ne' h
    · exact hne (by linarith)
  have hs := (strict_cvx hl).2 hz hu1 hne2 (show (0:ℝ) < 1 / 2 by norm_num)
    (show (0:ℝ) < 1 / 2 by norm_num) (by norm_num)
  have e1 : (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • (z + θ0 * (w - z)) = z + (θ0 / 2) * (w - z) := by
    simp only [smul_eq_mul]; ring
  rw [e1, key (θ0 / 2) (by positivity) (by linarith), smul_eq_mul, smul_eq_mul,
    key θ0 hθ0pos.le hθ01] at hs
  nlinarith
lemma inv_exists {φ : ℝ → EReal} (hφ : Assumption21 φ) {r0 : ℝ} (hl : Loc φ r0) :
    ∃ ε > 0, ∃ z : ℝ → ℝ,
      (∀ ζ ∈ Set.Ioo (-ε) ε, z ζ ∈ Set.Ioo (1 - r0 / 2) (1 + r0 / 2) ∧
        deriv (phiReal φ) (z ζ) = ζ ∧
        ∀ y ∈ Set.Ioo (1 - r0 / 2) (1 + r0 / 2), deriv (phiReal φ) y = ζ → y = z ζ) ∧
      (∀ ζ ∈ Set.Ioo (-ε) ε, HasDerivAt z (deriv (deriv (phiReal φ)) (z ζ))⁻¹ ζ) ∧
      z 0 = 1 ∧ ContinuousOn z (Set.Ioo (-ε) ε) ∧ StrictMonoOn z (Set.Ioo (-ε) ε) ∧
      ContDiffOn ℝ 1 z (Set.Ioo (-ε) ε) := by
  obtain ⟨hc1, hc2, hd1, hd2⟩ := cd2 isOpen_Ioo hl.cd
  have hr0 : 0 < r0 / 2 := by have := hl.pos; positivity
  have hIr : Set.Icc (1 - r0 / 2) (1 + r0 / 2) ⊆ Set.Ioo (1 - r0) (1 + r0) := by
    intro x hx; constructor <;> linarith [hx.1, hx.2, hl.pos]
  have hIr' : Set.Ioo (1 - r0 / 2) (1 + r0 / 2) ⊆ Set.Ioo (1 - r0) (1 + r0) :=
    fun x hx => hIr (Set.Ioo_subset_Icc_self hx)
  have hmono : StrictMonoOn (deriv (phiReal φ)) (Set.Ioo (1 - r0) (1 + r0)) :=
    strictMonoOn_of_deriv_pos (convex_Ioo _ _) hc1 (by
      intro x hx; rw [interior_Ioo] at hx; exact hl.ppos x hx)
  have h1mem : (1:ℝ) ∈ Set.Ioo (1 - r0) (1 + r0) :=
    ⟨by linarith [hl.pos], by linarith [hl.pos]⟩
  have hψ1 : deriv (phiReal φ) 1 = 0 := by
    have hmin : IsLocalMin (phiReal φ) 1 := by
      have : Set.Ioo (1 - r0) (1 + r0) ∈ 𝓝 (1:ℝ) :=
        Ioo_mem_nhds (by linarith [hl.pos]) (by linarith [hl.pos])
      filter_upwards [this] with x hx
      have h0 : phiReal φ 1 = 0 := by simp [phiReal, hφ.map_one]
      have hx0 : (0:EReal) ≤ φ x := phi_nonneg_all hφ x
      rw [hl.fin x hx] at hx0
      have : (0:ℝ) ≤ phiReal φ x := by exact_mod_cast hx0
      rw [h0]; exact this
    exact hmin.deriv_eq_zero
  have hlo : (1:ℝ) - r0 / 2 ∈ Set.Ioo (1 - r0) (1 + r0) :=
    ⟨by linarith [hl.pos], by linarith [hl.pos]⟩
  have hhi : (1:ℝ) + r0 / 2 ∈ Set.Ioo (1 - r0) (1 + r0) :=
    ⟨by linarith [hl.pos], by linarith [hl.pos]⟩
  have ha : deriv (phiReal φ) (1 - r0 / 2) < 0 := by
    have := hmono hlo h1mem (by linarith); rwa [hψ1] at this
  have hb : 0 < deriv (phiReal φ) (1 + r0 / 2) := by
    have := hmono h1mem hhi (by linarith); rwa [hψ1] at this
  set ε := min (-deriv (phiReal φ) (1 - r0 / 2)) (deriv (phiReal φ) (1 + r0 / 2)) with hε
  have hεpos : 0 < ε := lt_min (by linarith) hb
  have hεa : ε ≤ -deriv (phiReal φ) (1 - r0 / 2) := min_le_left _ _
  have hεb : ε ≤ deriv (phiReal φ) (1 + r0 / 2) := min_le_right _ _
  have hex : ∀ ζ ∈ Set.Ioo (-ε) ε, ∃ y, y ∈ Set.Ioo (1 - r0 / 2) (1 + r0 / 2) ∧
      deriv (phiReal φ) y = ζ := by
    intro ζ hζ
    have hcont : ContinuousOn (deriv (phiReal φ)) (Set.Icc (1 - r0 / 2) (1 + r0 / 2)) :=
      hc1.mono hIr
    obtain ⟨y, hy, hyζ⟩ := intermediate_value_Icc (by linarith) hcont
      (show ζ ∈ Set.Icc (deriv (phiReal φ) (1 - r0 / 2)) (deriv (phiReal φ) (1 + r0 / 2)) from
        ⟨by linarith [hζ.1], by linarith [hζ.2]⟩)
    refine ⟨y, ⟨lt_of_le_of_ne hy.1 ?_, lt_of_le_of_ne hy.2 ?_⟩, hyζ⟩
    · rintro rfl; linarith [hζ.1]
    · rintro rfl; linarith [hζ.2]
  have hinj : ∀ y ∈ Set.Ioo (1 - r0 / 2) (1 + r0 / 2), ∀ y' ∈ Set.Ioo (1 - r0 / 2) (1 + r0 / 2),
      deriv (phiReal φ) y = deriv (phiReal φ) y' → y = y' :=
    fun y hy y' hy' h => (hmono.injOn) (hIr' hy) (hIr' hy') h
  choose! z hz1 hz2 using hex
  have huniq : ∀ ζ ∈ Set.Ioo (-ε) ε, ∀ y ∈ Set.Ioo (1 - r0 / 2) (1 + r0 / 2),
      deriv (phiReal φ) y = ζ → y = z ζ :=
    fun ζ hζ y hy h => hinj y hy _ (hz1 ζ hζ) (by rw [h, hz2 ζ hζ])
  have hz0 : z 0 = 1 := by
    have h0 : (0:ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hεpos⟩
    exact (huniq 0 h0 1 ⟨by linarith, by linarith⟩ hψ1).symm
  have hsm : StrictMonoOn z (Set.Ioo (-ε) ε) := by
    intro a ha b hb hab
    by_contra hcon
    push_neg at hcon
    have := hmono.monotoneOn (hIr' (hz1 b hb)) (hIr' (hz1 a ha)) hcon
    rw [hz2 a ha, hz2 b hb] at this
    linarith
  have hJ : IsOpen (Set.Ioo (-ε) ε) := isOpen_Ioo
  have hcontAt : ∀ ζ ∈ Set.Ioo (-ε) ε, ContinuousAt z ζ := by
    intro ζ hζ
    apply continuousAt_of_monotoneOn_of_image_mem_nhds hsm.monotoneOn (hJ.mem_nhds hζ)
    have hopen : IsOpen (Set.Ioo (1 - r0 / 2) (1 + r0 / 2) ∩
        deriv (phiReal φ) ⁻¹' Set.Ioo (-ε) ε) :=
      (hc1.mono hIr').isOpen_inter_preimage isOpen_Ioo isOpen_Ioo
    refine mem_of_superset (hopen.mem_nhds ⟨(hz1 ζ hζ), by simpa [hz2 ζ hζ] using hζ⟩) ?_
    rintro y ⟨hy1, hy2⟩
    exact ⟨deriv (phiReal φ) y, hy2, (huniq _ hy2 y hy1 rfl).symm⟩
  have hder : ∀ ζ ∈ Set.Ioo (-ε) ε, HasDerivAt z (deriv (deriv (phiReal φ)) (z ζ))⁻¹ ζ := by
    intro ζ hζ
    have hzI := hIr' (hz1 ζ hζ)
    refine HasDerivAt.of_local_left_inverse (hcontAt ζ hζ) (hd2 _ hzI) (hl.ppos _ hzI).ne' ?_
    filter_upwards [hJ.mem_nhds hζ] with y hy using hz2 y hy
  have hcz : ContinuousOn z (Set.Ioo (-ε) ε) := fun ζ hζ => (hcontAt ζ hζ).continuousWithinAt
  refine ⟨ε, hεpos, z, fun ζ hζ => ⟨hz1 ζ hζ, hz2 ζ hζ, huniq ζ hζ⟩, hder, hz0, hcz, hsm, ?_⟩
  have : ContDiffOn ℝ (0 + 1 : WithTop ℕ∞) z (Set.Ioo (-ε) ε) := by
    rw [contDiffOn_succ_iff_deriv_of_isOpen hJ]
    refine ⟨fun ζ hζ => (hder ζ hζ).differentiableAt.differentiableWithinAt, fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · rw [contDiffOn_zero]
      have : ContinuousOn (fun ζ => (deriv (deriv (phiReal φ)) (z ζ))⁻¹) (Set.Ioo (-ε) ε) := by
        apply ContinuousOn.inv₀
        · exact hc2.comp hcz (fun ζ hζ => hIr' (hz1 ζ hζ))
        · intro ζ hζ; exact (hl.ppos _ (hIr' (hz1 ζ hζ))).ne'
      exact this.congr (fun ζ hζ => (hder ζ hζ).deriv)
  simpa using this
end DROHelp

theorem solution (φ : ℝ → EReal) (hφ : Assumption21 φ) :
    ∃ ε > 0, ∃ r > 0, ∃ z : ℝ → ℝ,
      ContDiffOn ℝ 1 z (Set.Ioo (-ε) ε) ∧
      (∀ ζ ∈ Set.Ioo (-ε) ε, z ζ ∈ Set.Ioo (1 - r) (1 + r) ∧ deriv (phiReal φ) (z ζ) = ζ ∧
        ∀ y ∈ Set.Ioo (1 - r) (1 + r), deriv (phiReal φ) y = ζ → y = z ζ) ∧
      (∀ ζ ∈ Set.Ioo (-ε) ε, HasDerivAt z (deriv (deriv (phiReal φ)) (z ζ))⁻¹ ζ) ∧
      z 0 = 1 ∧ HasDerivAt z (phiPP φ)⁻¹ 0 := by
  obtain ⟨r0, hl⟩ := DROHelp.loc hφ
  obtain ⟨ε, hε, z, h1, h2, h3, h4, h5, h6⟩ := DROHelp.inv_exists hφ hl
  have hr := hl.pos
  refine ⟨ε, hε, r0 / 2, by positivity, z, h6, h1, h2, h3, ?_⟩
  have := h2 0 ⟨by linarith, hε⟩
  rw [h3] at this
  exact this
