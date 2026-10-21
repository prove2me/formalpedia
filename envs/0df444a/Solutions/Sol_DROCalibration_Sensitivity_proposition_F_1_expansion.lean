-- Prove2me | solution 1 for DROCalibration.Sensitivity.proposition_F_1_expansion
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:27:15.078988+00:00
-- url     : https://prove2.me/submissions/b3cf5578-684c-4da8-acc5-b8bb147bab25

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
lemma conj_eval {φ : ℝ → EReal} (hφ : Assumption21 φ) {r0 : ℝ} (hl : Loc φ r0) {ζ z : ℝ}
    (hz : z ∈ Set.Ioo (1 - r0) (1 + r0)) (hzd : deriv (phiReal φ) z = ζ) :
    conj φ ζ = ((ζ * z - phiReal φ z : ℝ) : EReal) := by
  unfold conj
  apply le_antisymm
  · apply iSup_le
    intro w
    by_cases hw : φ w = ⊤
    · rw [hw]; simp
    · have := tangent hφ hl hz hw
      rw [fin_eq hφ hw, ← EReal.coe_sub]
      apply EReal.coe_le_coe_iff.2
      rw [hzd] at this
      linarith
  · have := le_iSup (fun w : ℝ => ((ζ * w : ℝ) : EReal) - φ w) z
    rw [hl.fin z hz, ← EReal.coe_sub] at this
    exact this

lemma conjReal_eval {φ : ℝ → EReal} (hφ : Assumption21 φ) {r0 : ℝ} (hl : Loc φ r0) {ζ z : ℝ}
    (hz : z ∈ Set.Ioo (1 - r0) (1 + r0)) (hzd : deriv (phiReal φ) z = ζ) :
    conjReal φ ζ = ζ * z - phiReal φ z := by
  simp only [conjReal]
  rw [conj_eval hφ hl hz hzd]; rfl

lemma conj_hasDeriv {φ : ℝ → EReal} (hφ : Assumption21 φ) {r0 : ℝ} (hl : Loc φ r0) {ε : ℝ}
    {z : ℝ → ℝ}
    (h1 : ∀ ζ ∈ Set.Ioo (-ε) ε, z ζ ∈ Set.Ioo (1 - r0 / 2) (1 + r0 / 2) ∧
        deriv (phiReal φ) (z ζ) = ζ)
    (h2 : ∀ ζ ∈ Set.Ioo (-ε) ε, HasDerivAt z (deriv (deriv (phiReal φ)) (z ζ))⁻¹ ζ) :
    ∀ ζ ∈ Set.Ioo (-ε) ε, HasDerivAt (conjReal φ) (z ζ) ζ := by
  intro ζ hζ
  have hsub : ∀ ζ ∈ Set.Ioo (-ε) ε, z ζ ∈ Set.Ioo (1 - r0) (1 + r0) := fun ζ hζ => by
    have := (h1 ζ hζ).1
    constructor <;> linarith [this.1, this.2, hl.pos]
  obtain ⟨-, -, hd1, -⟩ := cd2 isOpen_Ioo hl.cd
  have hA := ((hasDerivAt_id ζ).mul (h2 ζ hζ)).sub ((hd1 _ (hsub ζ hζ)).comp ζ (h2 ζ hζ))
  have hev : (fun ζ' => id ζ' * z ζ' - (phiReal φ ∘ z) ζ') =ᶠ[𝓝 ζ] conjReal φ := by
    filter_upwards [Ioo_mem_nhds hζ.1 hζ.2] with ζ' hζ'
    rw [conjReal_eval hφ hl (hsub ζ' hζ') (h1 ζ' hζ').2]
    rfl
  refine (hA.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  rw [(h1 ζ hζ).2]
  simp
lemma coe_sum' {n : ℕ} (g : Fin n → ℝ) : (((∑ i, g i : ℝ)) : EReal) = ∑ i, ((g i : ℝ) : EReal) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, EReal.coe_add, ih]

lemma obj_fin {φ : ℝ → EReal} (hφ : Assumption21 φ) {n : ℕ} (p f : Fin n → ℝ) (δ : ℝ)
    (q : Fin n → ℝ) (h : ∀ i, φ (q i / p i) ≠ ⊤) :
    objective φ p f δ q =
      ((∑ i, q i * f i + δ⁻¹ * ∑ i, p i * phiReal φ (q i / p i) : ℝ) : EReal) := by
  unfold objective
  have e : ∀ i, φ (q i / p i) = ((phiReal φ (q i / p i) : ℝ) : EReal) :=
    fun i => fin_eq hφ (h i)
  simp_rw [e]
  rw [EReal.coe_add, EReal.coe_mul, coe_sum' (fun i => p i * phiReal φ (q i / p i))]
  simp_rw [EReal.coe_mul]

lemma obj_top {φ : ℝ → EReal} (hφ : Assumption21 φ) {n : ℕ} (p f : Fin n → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hp : ∀ i, 0 < p i) (q : Fin n → ℝ) (i₀ : Fin n) (h : φ (q i₀ / p i₀) = ⊤) :
    objective φ p f δ q = ⊤ := by
  unfold objective
  have h1 : ((p i₀ : ℝ) : EReal) * φ (q i₀ / p i₀) = ⊤ := by
    rw [h]; exact EReal.coe_mul_top_of_pos (hp i₀)
  have h2 : ∑ i, ((p i : ℝ) : EReal) * φ (q i / p i) = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : EReal) = ((p i₀ : ℝ) : EReal) * φ (q i₀ / p i₀) := h1.symm
      _ ≤ ∑ i, ((p i : ℝ) : EReal) * φ (q i / p i) :=
        Finset.single_le_sum (f := fun i => ((p i : ℝ) : EReal) * φ (q i / p i))
          (fun i _ => EReal.mul_nonneg (EReal.coe_nonneg.2 (hp i).le) (phi_nonneg_all hφ _))
          (Finset.mem_univ i₀)
  rw [h2, EReal.coe_mul_top_of_pos (inv_pos.2 hδ), EReal.coe_add_top]

lemma min_real {φ : ℝ → EReal} (hφ : Assumption21 φ) {r0 : ℝ} (hl : Loc φ r0) {n : ℕ}
    (p f : Fin n → ℝ) (hp : ∀ i, 0 < p i) (δ : ℝ) (hδ : 0 < δ) (q q' : Fin n → ℝ)
    (hqs : q ∈ stdSimplex ℝ (Fin n)) (hq's : q' ∈ stdSimplex ℝ (Fin n)) (c : ℝ)
    (hq : ∀ i, q i / p i ∈ Set.Ioo (1 - r0) (1 + r0) ∧
      deriv (phiReal φ) (q i / p i) = δ * (-f i - c))
    (hall : ∀ i, φ (q' i / p i) ≠ ⊤) :
    ∑ i, q i * f i + δ⁻¹ * ∑ i, p i * phiReal φ (q i / p i) ≤
        ∑ i, q' i * f i + δ⁻¹ * ∑ i, p i * phiReal φ (q' i / p i) ∧
      (q' ≠ q → ∑ i, q i * f i + δ⁻¹ * ∑ i, p i * phiReal φ (q i / p i) <
        ∑ i, q' i * f i + δ⁻¹ * ∑ i, p i * phiReal φ (q' i / p i)) := by
  have hi : ∀ i, p i * phiReal φ (q i / p i) + δ * (-f i - c) * (q' i - q i) ≤
      p i * phiReal φ (q' i / p i) := by
    intro i
    have h := tangent hφ hl (hq i).1 (hall i)
    rw [(hq i).2] at h
    have hpi := hp i
    have e : p i * (δ * (-f i - c) * (q' i / p i - q i / p i)) =
        δ * (-f i - c) * (q' i - q i) := by field_simp
    have := mul_le_mul_of_nonneg_left h hpi.le
    nlinarith
  have hs : ∑ i, δ * (-f i - c) * (q' i - q i) =
      δ * (-(∑ i, q' i * f i) + ∑ i, q i * f i) := by
    have : ∀ i, δ * (-f i - c) * (q' i - q i) =
        δ * (-(q' i * f i) + q i * f i) + δ * (-c) * (q' i - q i) := fun i => by ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib,
      hqs.2, hq's.2, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    ring
  have hsum : ∑ i, p i * phiReal φ (q i / p i) + δ * (-(∑ i, q' i * f i) + ∑ i, q i * f i) ≤
      ∑ i, p i * phiReal φ (q' i / p i) := by
    rw [← hs, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => hi i
  have hδi : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ.ne'
  have hmul := mul_le_mul_of_nonneg_left hsum (inv_pos.2 hδ).le
  rw [mul_add, ← mul_assoc, hδi, one_mul] at hmul
  constructor
  · linarith
  · intro hne
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hne
    have hlt : p i₀ * phiReal φ (q i₀ / p i₀) + δ * (-f i₀ - c) * (q' i₀ - q i₀) <
        p i₀ * phiReal φ (q' i₀ / p i₀) := by
      have hne' : q' i₀ / p i₀ ≠ q i₀ / p i₀ := by
        intro h
        apply hi₀
        have := hp i₀
        field_simp at h
        exact h
      have h := tangent_strict hφ hl (hq i₀).1 (hall i₀) hne'
      rw [(hq i₀).2] at h
      have hpi := hp i₀
      have e : p i₀ * (δ * (-f i₀ - c) * (q' i₀ / p i₀ - q i₀ / p i₀)) =
          δ * (-f i₀ - c) * (q' i₀ - q i₀) := by field_simp
      have := mul_lt_mul_of_pos_left h hpi
      nlinarith
    have hsum' : ∑ i, p i * phiReal φ (q i / p i) +
        δ * (-(∑ i, q' i * f i) + ∑ i, q i * f i) < ∑ i, p i * phiReal φ (q' i / p i) := by
      rw [← hs, ← Finset.sum_add_distrib]
      exact Finset.sum_lt_sum (fun i _ => hi i) ⟨i₀, Finset.mem_univ _, hlt⟩
    have hmul' := mul_lt_mul_of_pos_left hsum' (inv_pos.2 hδ)
    rw [mul_add, ← mul_assoc, hδi, one_mul] at hmul'
    linarith

lemma min_ereal {φ : ℝ → EReal} (hφ : Assumption21 φ) {r0 : ℝ} (hl : Loc φ r0) {n : ℕ}
    (p f : Fin n → ℝ) (hp : ∀ i, 0 < p i) (δ : ℝ) (hδ : 0 < δ) (q : Fin n → ℝ)
    (hqs : q ∈ stdSimplex ℝ (Fin n)) (c : ℝ)
    (hq : ∀ i, q i / p i ∈ Set.Ioo (1 - r0) (1 + r0) ∧
      deriv (phiReal φ) (q i / p i) = δ * (-f i - c)) (q' : Fin n → ℝ)
    (hq's : q' ∈ stdSimplex ℝ (Fin n)) :
    objective φ p f δ q ≤ objective φ p f δ q' ∧
      (q' ≠ q → objective φ p f δ q < objective φ p f δ q') := by
  have hqfin : ∀ i, φ (q i / p i) ≠ ⊤ := fun i => by
    rw [hl.fin _ (hq i).1]; exact EReal.coe_ne_top _
  by_cases hex : ∃ i, φ (q' i / p i) = ⊤
  · obtain ⟨i₀, hi₀⟩ := hex
    rw [obj_top hφ p f δ hδ hp q' i₀ hi₀, obj_fin hφ p f δ q hqfin]
    exact ⟨le_top, fun _ => EReal.coe_lt_top _⟩
  · push_neg at hex
    rw [obj_fin hφ p f δ q hqfin, obj_fin hφ p f δ q' hex]
    obtain ⟨h1, h2⟩ := min_real hφ hl p f hp δ hδ q q' hqs hq's c hq hex
    exact ⟨EReal.coe_le_coe_iff.2 h1, fun h => EReal.coe_lt_coe_iff.2 (h2 h)⟩

lemma worst_eq {φ : ℝ → EReal} (hφ : Assumption21 φ) {r0 : ℝ} (hl : Loc φ r0) {n : ℕ}
    (p f : Fin n → ℝ) (hp : ∀ i, 0 < p i) (δ : ℝ) (hδ : 0 < δ) (q : Fin n → ℝ)
    (hqs : q ∈ stdSimplex ℝ (Fin n)) (c : ℝ)
    (hq : ∀ i, q i / p i ∈ Set.Ioo (1 - r0) (1 + r0) ∧
      deriv (phiReal φ) (q i / p i) = δ * (-f i - c)) :
    worstCaseSet φ p f δ = {q} := by
  ext q'
  simp only [worstCaseSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hq's, hmin⟩
    by_contra hne
    have := (min_ereal hφ hl p f hp δ hδ q hqs c hq q' hq's).2 hne
    exact absurd (hmin q hqs) (not_le.2 this)
  · rintro rfl
    exact ⟨hqs, fun q'' h => (min_ereal hφ hl p f hp δ hδ q' hqs c hq q'' h).1⟩
lemma dual_real {n : ℕ} (p f q : Fin n → ℝ) (hp : ∀ i, 0 < p i) (δ : ℝ) (hδ : 0 < δ)
    (hqs : ∑ i, q i = 1) (φz : Fin n → ℝ) (c' : ℝ) :
    -(δ⁻¹ * ∑ i, p i * (δ * (-f i - c') * (q i / p i) - φz i)) - c' =
      ∑ i, q i * f i + δ⁻¹ * ∑ i, p i * φz i := by
  have e : ∀ i, p i * (δ * (-f i - c') * (q i / p i) - φz i) =
      δ * (-(q i * f i) - c' * q i) - p i * φz i := by
    intro i
    have := (hp i).ne'
    field_simp
  simp_rw [e, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hqs, Finset.sum_neg_distrib]
  field_simp
  ring

lemma dual_max {φ : ℝ → EReal} (hφ : Assumption21 φ) {r0 : ℝ} (hl : Loc φ r0) {n : ℕ}
    (p f : Fin n → ℝ) (hp : ∀ i, 0 < p i) (δ : ℝ) (hδ : 0 < δ) (q : Fin n → ℝ)
    (hqs : q ∈ stdSimplex ℝ (Fin n)) (c : ℝ)
    (hq : ∀ i, q i / p i ∈ Set.Ioo (1 - r0) (1 + r0) ∧
      deriv (phiReal φ) (q i / p i) = δ * (-f i - c)) :
    IsMaxOn (fun c' : ℝ => -(((δ⁻¹ : ℝ) : EReal) *
          ∑ i, ((p i : ℝ) : EReal) * conj φ (δ * (-f i - c'))) - (c' : EReal)) Set.univ c := by
  rw [isMaxOn_iff]
  intro c' _
  set a : ℝ → Fin n → ℝ := fun c'' i => δ * (-f i - c'') * (q i / p i) - phiReal φ (q i / p i)
    with ha
  set J : ℝ := ∑ i, q i * f i + δ⁻¹ * ∑ i, p i * phiReal φ (q i / p i) with hJ
  have hRI : ∀ c'' : ℝ, -(δ⁻¹ * ∑ i, p i * a c'' i) - c'' = J := fun c'' =>
    dual_real p f q hp δ hδ hqs.2 (fun i => phiReal φ (q i / p i)) c''
  -- value at c
  have hB : (-(((δ⁻¹ : ℝ) : EReal) * ∑ i, ((p i : ℝ) : EReal) * conj φ (δ * (-f i - c))) -
      (c : EReal)) = (J : ℝ) := by
    have : ∀ i, conj φ (δ * (-f i - c)) = ((a c i : ℝ) : EReal) := fun i => by
      rw [conj_eval hφ hl (hq i).1 (hq i).2]
    simp_rw [this]
    rw [← hRI c]
    simp_rw [← EReal.coe_mul]
    rw [← coe_sum' (fun i => p i * a c i), ← EReal.coe_mul, ← EReal.coe_neg, ← EReal.coe_sub]
  -- bound at c'
  have hA : ∑ i, ((p i * a c' i : ℝ) : EReal) ≤
      ∑ i, ((p i : ℝ) : EReal) * conj φ (δ * (-f i - c')) := by
    apply Finset.sum_le_sum
    intro i _
    rw [EReal.coe_mul]
    apply mul_le_mul_of_nonneg_left _ (EReal.coe_nonneg.2 (hp i).le)
    have := le_iSup (fun w : ℝ => (((δ * (-f i - c')) * w : ℝ) : EReal) - φ w) (q i / p i)
    rw [hl.fin _ (hq i).1, ← EReal.coe_sub] at this
    exact this
  rw [hB]
  rw [← coe_sum'] at hA
  set T : EReal := ∑ i, ((p i : ℝ) : EReal) * conj φ (δ * (-f i - c')) with hT
  by_cases htop : T = ⊤
  · rw [htop, EReal.coe_mul_top_of_pos (inv_pos.2 hδ)]
    simp
  · have hbot : T ≠ ⊥ := by
      intro h; rw [h] at hA
      exact absurd hA (by simp)
    obtain ⟨t, ht⟩ : ∃ t : ℝ, T = (t : EReal) := ⟨T.toReal, (EReal.coe_toReal htop hbot).symm⟩
    rw [ht] at hA ⊢
    have hle : ∑ i, p i * a c' i ≤ t := EReal.coe_le_coe_iff.1 hA
    rw [← EReal.coe_mul, ← EReal.coe_neg, ← EReal.coe_sub]
    apply EReal.coe_le_coe_iff.2
    rw [← hRI c']
    have := inv_pos.2 hδ
    nlinarith
def Hfun {n : ℕ} (z : ℝ → ℝ) (p f : Fin n → ℝ) (δ c : ℝ) : ℝ :=
  ∑ i, p i * z (δ * (-f i - c))

structure ZData (φ : ℝ → EReal) (r0 ε : ℝ) (z : ℝ → ℝ) : Prop where
  eps : 0 < ε
  spec : ∀ ζ ∈ Set.Ioo (-ε) ε, z ζ ∈ Set.Ioo (1 - r0 / 2) (1 + r0 / 2) ∧
    deriv (phiReal φ) (z ζ) = ζ
  uniq : ∀ ζ ∈ Set.Ioo (-ε) ε, ∀ y ∈ Set.Ioo (1 - r0 / 2) (1 + r0 / 2),
    deriv (phiReal φ) y = ζ → y = z ζ
  hd : ∀ ζ ∈ Set.Ioo (-ε) ε, HasDerivAt z (deriv (deriv (phiReal φ)) (z ζ))⁻¹ ζ
  z0 : z 0 = 1
  cont : ContinuousOn z (Set.Ioo (-ε) ε)
  mono : StrictMonoOn z (Set.Ioo (-ε) ε)

lemma zdata {φ : ℝ → EReal} (hφ : Assumption21 φ) {r0 : ℝ} (hl : Loc φ r0) :
    ∃ ε z, ZData φ r0 ε z := by
  obtain ⟨ε, hε, z, h1, h2, h3, h4, h5, h6⟩ := inv_exists hφ hl
  exact ⟨ε, z, ⟨hε, fun ζ hζ => ⟨(h1 ζ hζ).1, (h1 ζ hζ).2.1⟩, fun ζ hζ => (h1 ζ hζ).2.2, h2, h3, h4, h5⟩⟩

lemma sum_p_mul {n : ℕ} (p f : Fin n → ℝ) (hp1 : ∑ i, p i = 1) (δ c : ℝ) :
    ∑ i, p i * (δ * (-f i - c)) = δ * (-wMean p f - c) := by
  have : ∀ i, p i * (δ * (-f i - c)) = δ * (-(p i * f i)) + (-(δ * c)) * p i := fun i => by ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_neg_distrib, hp1]
  unfold wMean
  ring

lemma Hmain {φ : ℝ → EReal} (hφ : Assumption21 φ) {r0 : ℝ} (hl : Loc φ r0) {ε : ℝ}
    {z : ℝ → ℝ} (ZD : ZData φ r0 ε z) {n : ℕ} (p f : Fin n → ℝ) (hp : ∀ i, 0 < p i)
    (hp1 : ∑ i, p i = 1) :
    ∃ Λ δ1 : ℝ, 0 < Λ ∧ 0 < δ1 ∧
      (∀ δ ∈ Set.Ioo 0 δ1, ∀ c, |c + wMean p f| ≤ 1 → ∀ i,
        |-f i - c| ≤ Λ ∧ δ * (-f i - c) ∈ Set.Ioo (-ε) ε) ∧
      (∀ δ ∈ Set.Ioo 0 δ1, ∀ c c', |c + wMean p f| ≤ 1 → |c' + wMean p f| ≤ 1 → c < c' →
        Hfun z p f δ c' < Hfun z p f δ c) ∧
      (∀ η > 0, ∃ δ2 > 0, δ2 ≤ δ1 ∧ ∀ δ ∈ Set.Ioo 0 δ2, ∀ c, |c + wMean p f| ≤ 1 →
        |Hfun z p f δ c - 1 + (deriv (deriv (phiReal φ)) 1)⁻¹ * δ * (c + wMean p f)| ≤ η * δ * Λ) ∧
      (∀ r' ∈ Set.Ioc (0:ℝ) 1, ∃ δ2 > 0, δ2 ≤ δ1 ∧ ∀ δ ∈ Set.Ioo 0 δ2,
        (∃ c, |c + wMean p f| < r' ∧ Hfun z p f δ c = 1) ∧
        (∀ c, |c + wMean p f| ≤ 1 → Hfun z p f δ c = 1 → |c + wMean p f| < r')) := by
  set E := wMean p f with hE
  set B : ℝ := ∑ j, |f j| with hB
  have hfB : ∀ i, |f i| ≤ B := fun i =>
    Finset.single_le_sum (f := fun j => |f j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  set Λ : ℝ := B + |E| + 1 with hΛ
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hΛ0 : 0 < Λ := by positivity
  have hε := ZD.eps
  set δ1 : ℝ := ε / Λ with hδ1
  have hδ1pos : 0 < δ1 := div_pos hε hΛ0
  have hbd : ∀ c, |c + E| ≤ 1 → ∀ i, |-f i - c| ≤ Λ := by
    intro c hc i
    have h1 := hfB i
    have h2 : |-f i - c| ≤ |f i| + |E| + |c + E| := by
      have : -f i - c = -f i + E - (c + E) := by ring
      rw [this]
      calc |-f i + E - (c + E)| ≤ |-f i + E| + |c + E| := abs_sub _ _
        _ ≤ |f i| + |E| + |c + E| := by
          have := abs_add_le (-f i) E
          rw [abs_neg] at this; linarith
    linarith
  have hmem : ∀ δ ∈ Set.Ioo 0 δ1, ∀ c, |c + E| ≤ 1 → ∀ i,
      |δ * (-f i - c)| ≤ δ * Λ ∧ δ * (-f i - c) ∈ Set.Ioo (-ε) ε := by
    intro δ hδ c hc i
    have h1 : |δ * (-f i - c)| ≤ δ * Λ := by
      rw [abs_mul, abs_of_pos hδ.1]
      exact mul_le_mul_of_nonneg_left (hbd c hc i) hδ.1.le
    have h2 : δ * Λ < ε := by
      have := hδ.2
      rw [hδ1, lt_div_iff₀ hΛ0] at this
      exact this
    have := abs_le.1 h1
    exact ⟨h1, by constructor <;> linarith [this.1, this.2]⟩
  have h0 : (0:ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  have h1mem : (1:ℝ) ∈ Set.Ioo (1 - r0) (1 + r0) :=
    ⟨by linarith [hl.pos], by linarith [hl.pos]⟩
  set κ : ℝ := (deriv (deriv (phiReal φ)) 1)⁻¹ with hκdef
  have hκ : HasDerivAt z κ 0 := by
    have := ZD.hd 0 h0
    rwa [ZD.z0] at this
  have hκpos : 0 < κ := inv_pos.2 (hl.ppos 1 h1mem)
  have Hest : ∀ η > 0, ∃ δ2 > 0, δ2 ≤ δ1 ∧ ∀ δ ∈ Set.Ioo 0 δ2, ∀ c, |c + E| ≤ 1 →
      |Hfun z p f δ c - 1 + κ * δ * (c + E)| ≤ η * δ * Λ := by
    intro η hη
    have hlo := hκ.isLittleO.def hη
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hlo
    refine ⟨min δ1 (ρ / Λ), lt_min hδ1pos (div_pos hρ hΛ0), min_le_left _ _, ?_⟩
    intro δ hδ c hc
    have hδ1' : δ ∈ Set.Ioo 0 δ1 := ⟨hδ.1, lt_of_lt_of_le hδ.2 (min_le_left _ _)⟩
    have hδρ : δ * Λ < ρ := by
      have := lt_of_lt_of_le hδ.2 (min_le_right _ _)
      exact (lt_div_iff₀ hΛ0).1 this
    have key : ∀ i, |z (δ * (-f i - c)) - 1 - κ * (δ * (-f i - c))| ≤ η * (δ * Λ) := by
      intro i
      have hb := (hmem δ hδ1' c hc i).1
      have := hball (show dist (δ * (-f i - c)) 0 < ρ by
        rw [Real.dist_eq, sub_zero]; linarith)
      simp only [Real.norm_eq_abs, smul_eq_mul, sub_zero, ZD.z0] at this
      calc |z (δ * (-f i - c)) - 1 - κ * (δ * (-f i - c))|
          = |z (δ * (-f i - c)) - 1 - δ * (-f i - c) * κ| := by ring_nf
        _ ≤ η * |δ * (-f i - c)| := this
        _ ≤ η * (δ * Λ) := mul_le_mul_of_nonneg_left hb hη.le
    have hid : Hfun z p f δ c - 1 + κ * δ * (c + E) =
        ∑ i, p i * (z (δ * (-f i - c)) - 1 - κ * (δ * (-f i - c))) := by
      have e : ∀ i, p i * (z (δ * (-f i - c)) - 1 - κ * (δ * (-f i - c))) =
          p i * z (δ * (-f i - c)) - p i - κ * (p i * (δ * (-f i - c))) := fun i => by ring
      simp_rw [e, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_p_mul p f hp1, hp1]
      unfold Hfun
      ring
    rw [hid]
    calc |∑ i, p i * (z (δ * (-f i - c)) - 1 - κ * (δ * (-f i - c)))|
        ≤ ∑ i, |p i * (z (δ * (-f i - c)) - 1 - κ * (δ * (-f i - c)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, p i * (η * (δ * Λ)) := by
          apply Finset.sum_le_sum
          intro i _
          rw [abs_mul, abs_of_pos (hp i)]
          exact mul_le_mul_of_nonneg_left (key i) (hp i).le
      _ = η * δ * Λ := by
          rw [← Finset.sum_mul, hp1]; ring
  have hn : n ≠ 0 := by
    rintro rfl; simp at hp1
  let i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  have hanti : ∀ δ ∈ Set.Ioo 0 δ1, ∀ c c', |c + E| ≤ 1 → |c' + E| ≤ 1 → c < c' →
      Hfun z p f δ c' < Hfun z p f δ c := by
    intro δ hδ c c' hc hc' hcc
    unfold Hfun
    have hlt : ∀ i, z (δ * (-f i - c')) < z (δ * (-f i - c)) := fun i =>
      ZD.mono (hmem δ hδ c' hc' i).2 (hmem δ hδ c hc i).2 (by nlinarith [hδ.1])
    exact Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hlt i).le (hp i).le)
      ⟨i₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hlt i₀) (hp i₀)⟩
  have hcontH : ∀ δ ∈ Set.Ioo 0 δ1, ContinuousOn (Hfun z p f δ)
      (Set.Icc (-E - 1) (-E + 1)) := by
    intro δ hδ
    unfold Hfun
    apply continuousOn_finsetSum
    intro i _
    apply ContinuousOn.mul continuousOn_const
    have hc : Continuous fun c : ℝ => δ * (-f i - c) := by fun_prop
    exact ZD.cont.comp hc.continuousOn (fun c hc' =>
      (hmem δ hδ c (abs_le.2 ⟨by linarith [hc'.1], by linarith [hc'.2]⟩) i).2)
  refine ⟨Λ, δ1, hΛ0, hδ1pos, fun δ hδ c hc i => ⟨hbd c hc i, (hmem δ hδ c hc i).2⟩,
    hanti, fun η hη => Hest η hη, ?_⟩
  intro r' hr'
  obtain ⟨δ2, hδ2, hδ2le, hest⟩ := Hest (κ * r' / (2 * Λ)) (by have := hr'.1; positivity)
  refine ⟨δ2, hδ2, hδ2le, fun δ hδ => ?_⟩
  have hδ1' : δ ∈ Set.Ioo 0 δ1 := ⟨hδ.1, lt_of_lt_of_le hδ.2 hδ2le⟩
  have hηΛ : κ * r' / (2 * Λ) * δ * Λ = κ * r' * δ / 2 := by field_simp
  have hmpos : 0 < κ * r' * δ := by have := hr'.1; have := hδ.1; positivity
  have hra : |(-E - r') + E| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hr'.1, hr'.2]
  have hrb : |(-E + r') + E| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hr'.1, hr'.2]
  have hlow : 1 < Hfun z p f δ (-E - r') := by
    have h := abs_le.1 (hest δ hδ (-E - r') hra)
    have e1 : κ * δ * ((-E - r') + E) = -(κ * r' * δ) := by ring
    rw [e1, hηΛ] at h
    linarith [h.1]
  have hhigh : Hfun z p f δ (-E + r') < 1 := by
    have h := abs_le.1 (hest δ hδ (-E + r') hrb)
    have e1 : κ * δ * ((-E + r') + E) = κ * r' * δ := by ring
    rw [e1, hηΛ] at h
    linarith [h.2]
  constructor
  · have hsub : Set.Icc (-E - r') (-E + r') ⊆ Set.Icc (-E - 1) (-E + 1) :=
      Set.Icc_subset_Icc (by linarith [hr'.2]) (by linarith [hr'.2])
    have hIVT := intermediate_value_Icc' (by linarith [hr'.1] : -E - r' ≤ -E + r')
      ((hcontH δ hδ1').mono hsub)
      (show (1:ℝ) ∈ Set.Icc (Hfun z p f δ (-E + r')) (Hfun z p f δ (-E - r')) from
        ⟨hhigh.le, hlow.le⟩)
    obtain ⟨c, hc, hc1⟩ := hIVT
    refine ⟨c, ?_, hc1⟩
    have hne1 : c ≠ -E - r' := by rintro rfl; linarith
    have hne2 : c ≠ -E + r' := by rintro rfl; linarith
    rw [abs_lt]
    constructor
    · have := lt_of_le_of_ne hc.1 (Ne.symm hne1); linarith
    · have := lt_of_le_of_ne hc.2 hne2; linarith
  · intro c hc hc1
    by_contra hcon
    rw [not_lt] at hcon
    rcases le_abs'.1 hcon with h | h
    · -- c + E ≤ -r'
      rcases eq_or_lt_of_le (show c ≤ -E - r' by linarith) with h' | h'
      · rw [h'] at hc1; linarith
      · have := hanti δ hδ1' c (-E - r') hc hra h'
        linarith
    · rcases eq_or_lt_of_le (show -E + r' ≤ c by linarith) with h' | h'
      · rw [← h'] at hc1; linarith
      · have := hanti δ hδ1' (-E + r') c hrb hc h'
        linarith
lemma Hfull {φ : ℝ → EReal} (hφ : Assumption21 φ) {r0 : ℝ} (hl : Loc φ r0) {ε : ℝ}
    {z : ℝ → ℝ} (ZD : ZData φ r0 ε z) {n : ℕ} (p f : Fin n → ℝ) (hp : ∀ i, 0 < p i)
    (hp1 : ∑ i, p i = 1) :
    ∃ Λ δ0 : ℝ, 0 < Λ ∧ 0 < δ0 ∧
      (∀ δ ∈ Set.Ioo 0 δ0, ∀ c, |c + wMean p f| ≤ 1 → ∀ i,
        |-f i - c| ≤ Λ ∧ δ * (-f i - c) ∈ Set.Ioo (-ε) ε) ∧
      (∀ δ ∈ Set.Ioo 0 δ0, ∃ c, |c + wMean p f| < 1 ∧ Hfun z p f δ c = 1) ∧
      (∀ δ ∈ Set.Ioo 0 δ0, ∀ c c', |c + wMean p f| ≤ 1 → |c' + wMean p f| ≤ 1 →
        Hfun z p f δ c = 1 → Hfun z p f δ c' = 1 → c = c') ∧
      (∀ cs : ℝ → ℝ, (∀ δ ∈ Set.Ioo 0 δ0, |cs δ + wMean p f| < 1 ∧ Hfun z p f δ (cs δ) = 1) →
        Tendsto cs (𝓝[>] 0) (𝓝 (-wMean p f))) := by
  obtain ⟨Λ, δ1, hΛ, hδ1, hA, hanti, -, hr⟩ := Hmain hφ hl ZD p f hp hp1
  obtain ⟨δ0, hδ0, hδ0le, hδ0P⟩ := hr 1 ⟨one_pos, le_rfl⟩
  have hmono : ∀ δ ∈ Set.Ioo 0 δ0, δ ∈ Set.Ioo 0 δ1 := fun δ hδ => ⟨hδ.1, lt_of_lt_of_le hδ.2 hδ0le⟩
  refine ⟨Λ, δ0, hΛ, hδ0, fun δ hδ => hA δ (hmono δ hδ), fun δ hδ => ?_, ?_, ?_⟩
  · obtain ⟨c, hc, hc1⟩ := (hδ0P δ hδ).1
    exact ⟨c, hc, hc1⟩
  · intro δ hδ c c' hc hc' h h'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hanti δ (hmono δ hδ) c c' hc hc' hlt; linarith
    · have := hanti δ (hmono δ hδ) c' c hc' hc hlt; linarith
  · intro cs hcs
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro e he
    obtain ⟨δ2, hδ2, hδ2le, hδ2P⟩ := hr (min 1 e) ⟨lt_min one_pos he, min_le_left _ _⟩
    refine ⟨min δ0 δ2, lt_min hδ0 hδ2, fun x hx hxd => ?_⟩
    have hx0 : 0 < x := hx
    have hxd' : x < min δ0 δ2 := by rwa [Real.dist_eq, sub_zero, abs_of_pos hx0] at hxd
    have hxa : x ∈ Set.Ioo 0 δ0 := ⟨hx0, lt_of_lt_of_le hxd' (min_le_left _ _)⟩
    have hxb : x ∈ Set.Ioo 0 δ2 := ⟨hx0, lt_of_lt_of_le hxd' (min_le_right _ _)⟩
    obtain ⟨h1, h2⟩ := hcs x hxa
    have := (hδ2P x hxb).2 (cs x) h1.le h2
    rw [Real.dist_eq]
    have e : cs x - -wMean p f = cs x + wMean p f := by ring
    rw [e]
    exact lt_of_lt_of_le this (min_le_right _ _)
lemma worst_explicit {φ : ℝ → EReal} (hφ : Assumption21 φ) {r0 : ℝ} (hl : Loc φ r0) {ε : ℝ}
    {z : ℝ → ℝ} (ZD : ZData φ r0 ε z) {n : ℕ} (p f : Fin n → ℝ) (hp : ∀ i, 0 < p i)
    (δ : ℝ) (hδ : 0 < δ) (c : ℝ) (hmem : ∀ i, δ * (-f i - c) ∈ Set.Ioo (-ε) ε)
    (hH : Hfun z p f δ c = 1) :
    worstCaseSet φ p f δ = {fun i => p i * z (δ * (-f i - c))} := by
  have hr0 := hl.pos
  have hr1 := hl.le
  set q : Fin n → ℝ := fun i => p i * z (δ * (-f i - c)) with hq
  have hqdiv : ∀ i, q i / p i = z (δ * (-f i - c)) := fun i => by
    simp only [hq]; field_simp [(hp i).ne']
  have hzI : ∀ i, z (δ * (-f i - c)) ∈ Set.Ioo (1 - r0 / 2) (1 + r0 / 2) :=
    fun i => (ZD.spec _ (hmem i)).1
  have hzpos : ∀ i, 0 < z (δ * (-f i - c)) := fun i => by
    have := (hzI i).1; linarith
  have hqs : q ∈ stdSimplex ℝ (Fin n) :=
    ⟨fun i => (mul_pos (hp i) (hzpos i)).le, hH⟩
  have hI0 : ∀ i, q i / p i ∈ Set.Ioo (1 - r0) (1 + r0) ∧
      deriv (phiReal φ) (q i / p i) = δ * (-f i - c) := fun i => by
    rw [hqdiv i]
    exact ⟨⟨by linarith [(hzI i).1], by linarith [(hzI i).2]⟩, (ZD.spec _ (hmem i)).2⟩
  exact worst_eq hφ hl p f hp δ hδ q hqs c hI0

lemma expansion {φ : ℝ → EReal} (hφ : Assumption21 φ) {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) (f : Fin n → ℝ) (Q : ℝ → Fin n → ℝ)
    (hQ : ∀ᶠ δ in 𝓝[>] 0, Q δ ∈ worstCaseSet φ p f δ) (i : Fin n) :
    Tendsto (fun δ => (Q δ i - p i) / δ) (𝓝[>] 0)
      (𝓝 (-(p i * (f i - wMean p f)) / phiPP φ)) := by
  obtain ⟨r0, hl⟩ := loc hφ
  obtain ⟨ε, z, ZD⟩ := zdata hφ hl
  obtain ⟨Λ, δ0, hΛ, hδ0, hA, hB, hC, hD⟩ := Hfull hφ hl ZD p f hp hp1
  choose! cs hcs using hB
  have hcst := hD cs hcs
  have hev : ∀ᶠ δ in 𝓝[>] (0:ℝ), Q δ i = p i * z (δ * (-f i - cs δ)) := by
    filter_upwards [hQ, Ioo_mem_nhdsGT hδ0] with δ hQδ hδ
    obtain ⟨hc, hc1⟩ := hcs δ hδ
    rw [worst_explicit hφ hl ZD p f hp δ hδ.1 (cs δ)
      (fun j => (hA δ hδ (cs δ) hc.le j).2) hc1] at hQδ
    exact congrFun (Set.mem_singleton_iff.1 hQδ) i
  set E := wMean p f with hE
  have h0 : (0:ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith [ZD.eps], ZD.eps⟩
  set κ : ℝ := (deriv (deriv (phiReal φ)) 1)⁻¹ with hκdef
  have hκ : HasDerivAt z κ 0 := by
    have := ZD.hd 0 h0
    rwa [ZD.z0] at this
  set ξ : ℝ → ℝ := fun δ => -f i - cs δ with hξdef
  have hξ : Tendsto ξ (𝓝[>] 0) (𝓝 (-f i + E)) := by
    have := (tendsto_const_nhds (x := -f i)).sub hcst
    simpa [hξdef, sub_neg_eq_add] using this
  have hu : Tendsto (fun δ => δ * ξ δ) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
      tendsto_id
    simpa using h1.mul hξ
  have hlo := hκ.isLittleO.comp_tendsto hu
  have hbo : (fun δ => δ * ξ δ) =O[𝓝[>] 0] (fun δ : ℝ => δ) := by
    apply Asymptotics.IsBigO.of_bound Λ
    filter_upwards [Ioo_mem_nhdsGT hδ0] with δ hδ
    have := (hA δ hδ (cs δ) (hcs δ hδ).1.le i).1
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hδ.1]
    calc δ * |ξ δ| ≤ δ * Λ := mul_le_mul_of_nonneg_left this hδ.1.le
      _ = Λ * δ := by ring
  have hlo2 : (fun δ => z (δ * ξ δ) - 1 - δ * ξ δ * κ) =o[𝓝[>] 0] (fun δ : ℝ => δ) := by
    have hbo' : (fun δ => δ * ξ δ - 0) =O[𝓝[>] 0] (fun δ : ℝ => δ) := by
      simpa using hbo
    have := hlo.trans_isBigO hbo'
    refine this.congr_left (fun δ => ?_)
    simp [Function.comp, ZD.z0]
  have hdiv := hlo2.tendsto_div_nhds_zero
  have hmain := ((hdiv.add (hξ.mul_const κ)).const_mul (p i))
  have hval : -(p i * (f i - E)) / phiPP φ = p i * (0 + (-f i + E) * κ) := by
    unfold phiPP
    simp only [hκdef]
    ring
  rw [hval]
  refine hmain.congr' ?_
  filter_upwards [hev, Ioo_mem_nhdsGT hδ0] with δ hδ hδ'
  rw [hδ]
  have := hδ'.1.ne'
  simp only [hξdef]
  field_simp
  ring
end DROHelp

theorem solution (φ : ℝ → EReal) (hφ : Assumption21 φ) {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) (f : Fin n → ℝ) (Q : ℝ → Fin n → ℝ)
    (hQ : ∀ᶠ δ in 𝓝[>] 0, Q δ ∈ worstCaseSet φ p f δ) (i : Fin n) :
    Tendsto (fun δ => (Q δ i - p i) / δ) (𝓝[>] 0)
      (𝓝 (-(p i * (f i - wMean p f)) / phiPP φ)) :=
  DROHelp.expansion hφ p hp hp1 f Q hQ i
