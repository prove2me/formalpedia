-- Prove2me | solution 1 for ErrBoundCplx.Cplx.theorem_16
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T17:22:33.843549+00:00
-- url     : https://prove2.me/submissions/979b248f-6aaf-4955-83fe-48ac50d34c13

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_ErrBoundCplx_Cplx_DescentSeq
import Definitions.Def_ErrBoundCplx_Cplx_WorstCase

set_option autoImplicit false

open MoreauProx.Characterization NonconvexSplitting.ADMMKL
open Filter Topology

namespace ErrBoundCplxT16Aux

open ErrBoundCplx.Cplx

lemma phi_diffAt {φ : ℝ → ℝ} {rbar : ℝ} (hφ : IsDesingularizer rbar φ) {r : ℝ}
    (hr : r ∈ Set.Ioo 0 rbar) : DifferentiableAt ℝ φ r :=
  ((hφ.2.2.2.2.1.differentiableOn (by norm_num)) r hr).differentiableAt (Ioo_mem_nhds hr.1 hr.2)

lemma phi_strictMono {φ : ℝ → ℝ} {rbar : ℝ} (hφ : IsDesingularizer rbar φ) :
    StrictMonoOn φ (Set.Ico 0 rbar) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico 0 rbar) hφ.1
  intro x hx
  rw [interior_Ico] at hx
  exact hφ.2.2.2.2.2 x hx

lemma concave_tangent {φ : ℝ → ℝ} {rbar : ℝ} (hφ : IsDesingularizer rbar φ)
    {r r' : ℝ} (hr : r ∈ Set.Ioo 0 rbar) (hr' : r' ∈ Set.Ico 0 rbar) :
    φ r' ≤ φ r + deriv φ r * (r' - r) := by
  have hd := phi_diffAt hφ hr
  have hcc := hφ.2.1
  have hrS : r ∈ Set.Ico 0 rbar := ⟨hr.1.le, hr.2⟩
  rcases lt_trichotomy r r' with h | h | h
  · have h1 := hcc.slope_le_deriv hrS hr' h hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at h1
    linarith
  · subst h; simp
  · have h1 := hcc.deriv_le_slope hr' hrS h hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at h1
    have e : deriv φ r * (r' - r) = -(deriv φ r * (r - r')) := by ring
    linarith

section profile

variable {φ ψ : ℝ → ℝ} {rbar r0 : ℝ} {ℓ : NNReal}

lemma phi_mapsTo (hS : ProfileSetting φ ψ rbar r0 ℓ) {s : ℝ} (hs : s ∈ Set.Icc 0 r0) :
    φ s ∈ Set.Icc 0 (φ r0) := by
  obtain ⟨hφ, hr0, hr0b, -, -⟩ := hS
  have hsI : s ∈ Set.Ico 0 rbar := ⟨hs.1, lt_of_le_of_lt hs.2 hr0b⟩
  exact ⟨hφ.2.2.1 s hsI, (phi_strictMono hφ).monotoneOn hsI ⟨hr0.le, hr0b⟩ hs.2⟩

lemma exists_pre (hS : ProfileSetting φ ψ rbar r0 ℓ) {u : ℝ} (hu : u ∈ Set.Icc 0 (φ r0)) :
    ∃ s ∈ Set.Icc 0 r0, φ s = u := by
  obtain ⟨hφ, hr0, hr0b, -, -⟩ := hS
  have hcont : ContinuousOn φ (Set.Icc 0 r0) :=
    hφ.1.mono (fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hr0b⟩)
  have hu' : u ∈ Set.Icc (φ 0) (φ r0) := by rw [hφ.2.2.2.1]; exact hu
  exact intermediate_value_Icc hr0.le hcont hu'

lemma psi_mono (hS : ProfileSetting φ ψ rbar r0 ℓ) {u v : ℝ} (hu : u ∈ Set.Icc 0 (φ r0))
    (hv : v ∈ Set.Icc 0 (φ r0)) (huv : u ≤ v) : ψ u ≤ ψ v := by
  obtain ⟨s, hs, rfl⟩ := exists_pre hS hu
  obtain ⟨t, ht, rfl⟩ := exists_pre hS hv
  rw [hS.2.2.2.1 s hs, hS.2.2.2.1 t ht]
  by_contra h
  push Not at h
  have := (phi_strictMono hS.1) ⟨ht.1, lt_of_le_of_lt ht.2 hS.2.2.1⟩
    ⟨hs.1, lt_of_le_of_lt hs.2 hS.2.2.1⟩ h
  linarith

lemma psiPrime_mul (hS : ProfileSetting φ ψ rbar r0 ℓ) {r : ℝ} (hr : r ∈ Set.Ioc 0 r0) :
    psiPrime ψ (φ r0) (φ r) * deriv φ r = 1 := by
  have hrI : r ∈ Set.Icc 0 r0 := ⟨hr.1.le, hr.2⟩
  have hψ : HasDerivWithinAt ψ (psiPrime ψ (φ r0) (φ r)) (Set.Icc 0 (φ r0)) (φ r) :=
    (hS.2.2.2.2.1 (φ r) (phi_mapsTo hS hrI)).hasDerivWithinAt
  have hφd : HasDerivWithinAt φ (deriv φ r) (Set.Icc 0 r0) r :=
    (phi_diffAt hS.1 ⟨hr.1, lt_of_le_of_lt hr.2 hS.2.2.1⟩).hasDerivAt.hasDerivWithinAt
  have hcomp := hψ.comp r hφd (fun s hs => phi_mapsTo hS hs)
  have hid : HasDerivWithinAt (ψ ∘ φ) 1 (Set.Icc 0 r0) r :=
    (hasDerivWithinAt_id r _).congr (fun y hy => by simp [hS.2.2.2.1 y hy])
      (by simp [hS.2.2.2.1 r hrI])
  exact (uniqueDiffOn_Icc hS.2.1 r hrI).eq_deriv _ hcomp hid

lemma psi_descent (hS : ProfileSetting φ ψ rbar r0 ℓ) {β γ : ℝ} (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (hγ : γ ≤ φ r0) :
    ψ γ ≤ ψ β + psiPrime ψ (φ r0) β * (γ - β) + (ℓ : ℝ) * (γ - β) ^ 2 / 2 := by
  obtain ⟨hdiff, -, hlip, -⟩ := hS.2.2.2.2
  have hsub : Set.Icc β γ ⊆ Set.Icc 0 (φ r0) := fun t ht => ⟨le_trans hβ ht.1, le_trans ht.2 hγ⟩
  have hψc : ContinuousOn ψ (Set.Icc β γ) := hdiff.continuousOn.mono hsub
  let p := psiPrime ψ (φ r0) β
  let g : ℝ → ℝ := fun t => ψ t - ψ β - p * (t - β) - (ℓ : ℝ) * (t - β) ^ 2 / 2
  have hgc : ContinuousOn g (Set.Icc β γ) := by
    have h2 : ContinuousOn (fun t : ℝ => p * (t - β) + (ℓ : ℝ) * (t - β) ^ 2 / 2)
        (Set.Icc β γ) := by fun_prop
    have := (hψc.sub (continuousOn_const : ContinuousOn (fun _ : ℝ => ψ β) (Set.Icc β γ))).sub h2
    refine this.congr (fun t _ => ?_)
    simp only [g, Pi.sub_apply]; ring
  have hderiv : ∀ t ∈ Set.Ioo β γ,
      HasDerivAt g (psiPrime ψ (φ r0) t - p - (ℓ : ℝ) * (t - β)) t := by
    intro t ht
    have htI : t ∈ Set.Ioo 0 (φ r0) := ⟨lt_of_le_of_lt hβ ht.1, lt_of_lt_of_le ht.2 hγ⟩
    have hψt : HasDerivAt ψ (psiPrime ψ (φ r0) t) t :=
      (hdiff t (Set.Ioo_subset_Icc_self htI)).hasDerivWithinAt.hasDerivAt
        (Icc_mem_nhds htI.1 htI.2)
    have h1 : HasDerivAt (fun s : ℝ => s - β) 1 t := (hasDerivAt_id' t).sub_const β
    have h2 : HasDerivAt (fun s : ℝ => (s - β) ^ 2) (2 * (t - β)) t :=
      (h1.pow 2).congr_deriv (by norm_num)
    have := ((hψt.sub_const (ψ β)).sub (h1.const_mul p)).sub ((h2.const_mul (ℓ : ℝ)).div_const 2)
    exact this.congr_deriv (by ring)
  have hanti : AntitoneOn g (Set.Icc β γ) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc β γ) hgc
    · intro t ht
      rw [interior_Icc] at ht
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t ht).deriv]
      have htI : t ∈ Set.Icc 0 (φ r0) := hsub (Set.Ioo_subset_Icc_self ht)
      have hβI : β ∈ Set.Icc 0 (φ r0) := hsub ⟨le_rfl, hβγ⟩
      have hl := hlip.dist_le_mul t htI β hβI
      rw [Real.dist_eq, Real.dist_eq, abs_of_pos (sub_pos.mpr ht.1)] at hl
      have h3 := le_abs_self (psiPrime ψ (φ r0) t - psiPrime ψ (φ r0) β)
      show psiPrime ψ (φ r0) t - psiPrime ψ (φ r0) β - (ℓ : ℝ) * (t - β) ≤ 0
      linarith
  have hm := hanti ⟨le_rfl, hβγ⟩ ⟨hβγ, le_rfl⟩ hβγ
  simp only [g, sub_self, mul_zero, zero_pow two_ne_zero, zero_div] at hm
  show ψ γ ≤ ψ β + p * (γ - β) + (ℓ : ℝ) * (γ - β) ^ 2 / 2
  linarith

end profile

lemma zeta_pos {ℓ a b : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) (hb : 0 < b) : 0 < zeta ℓ a b := by
  unfold zeta
  apply div_pos _ hℓ
  have h1 : (1 : ℝ) < 1 + 2 * ℓ * a * b⁻¹ ^ 2 := by
    have : 0 < 2 * ℓ * a * b⁻¹ ^ 2 := by positivity
    linarith
  have h := Real.sqrt_lt_sqrt (by norm_num) h1
  rw [Real.sqrt_one] at h
  linarith

lemma zeta_id {ℓ a b : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) (hb : 0 < b) :
    zeta ℓ a b + ℓ * zeta ℓ a b ^ 2 / 2 = a / b ^ 2 := by
  unfold zeta
  have hnn : 0 ≤ 1 + 2 * ℓ * a * b⁻¹ ^ 2 := by positivity
  have hs := Real.sq_sqrt hnn
  generalize Real.sqrt (1 + 2 * ℓ * a * b⁻¹ ^ 2) = S at hs ⊢
  have e1 : (S - 1) / ℓ + ℓ * ((S - 1) / ℓ) ^ 2 / 2 = (S ^ 2 - 1) / (2 * ℓ) := by
    field_simp
    ring
  rw [e1, hs]
  field_simp
  ring

/-- The comparison step: one step of the descent sequence stays below the worst-case
proximal step. -/
lemma key_step {φ ψ : ℝ → ℝ} {rbar r0 : ℝ} {ℓ : NNReal} (hS : ProfileSetting φ ψ rbar r0 ℓ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {r R γ δ d : ℝ} (hr : r ∈ Set.Ioc 0 r0) (hd0 : 0 ≤ d) (hrR : r + a * d ^ 2 ≤ R)
    (hKL : 1 ≤ deriv φ r * (b * d))
    (hγ : γ ∈ Set.Icc 0 (φ r0)) (hRγ : R ≤ ψ γ)
    (hδ : δ ∈ Set.Icc 0 (φ r0))
    (hmin : ∀ u ∈ Set.Icc 0 (φ r0),
      ψ δ + (δ - γ) ^ 2 / (2 * zeta ℓ a b) ≤ ψ u + (u - γ) ^ 2 / (2 * zeta ℓ a b)) :
    φ r ≤ δ := by
  by_contra hlt
  push Not at hlt
  have hφ := hS.1
  have hrI : r ∈ Set.Icc 0 r0 := ⟨hr.1.le, hr.2⟩
  have hrO : r ∈ Set.Ioo 0 rbar := ⟨hr.1, lt_of_le_of_lt hr.2 hS.2.2.1⟩
  have hβ := phi_mapsTo hS hrI
  have hq : 0 < deriv φ r := hφ.2.2.2.2.2 r hrO
  have hpq := psiPrime_mul hS hr
  have hψβ : ψ (φ r) = r := hS.2.2.2.1 r hrI
  obtain ⟨r', hr', hr'δ⟩ := exists_pre hS hδ
  have hψδ : ψ δ = r' := by rw [← hr'δ]; exact hS.2.2.2.1 r' hr'
  have htan := concave_tangent hφ hrO ⟨hr'.1, lt_of_le_of_lt hr'.2 hS.2.2.1⟩
  rw [hr'δ] at htan
  have hm := hmin (φ r) hβ
  rw [hψδ, hψβ] at hm
  have hmono : γ ≤ φ r → ψ γ ≤ r := fun h => by
    have := psi_mono hS hγ hβ h; rwa [hψβ] at this
  have hdesc : φ r ≤ γ →
      ψ γ ≤ r + psiPrime ψ (φ r0) (φ r) * (γ - φ r) + (ℓ : ℝ) * (γ - φ r) ^ 2 / 2 :=
    fun h => by have := psi_descent hS hβ.1 h hγ.2; rwa [hψβ] at this
  have hℓ : (0 : ℝ) < ℓ := NNReal.coe_pos.mpr hS.2.2.2.2.2.1
  have hζ := zeta_pos hℓ ha hb
  have hzid := zeta_id hℓ ha hb
  generalize psiPrime ψ (φ r0) (φ r) = p at hpq hdesc
  generalize deriv φ r = q at hq hpq htan hKL
  generalize φ r = β at hlt hβ hm hmono hdesc htan
  generalize zeta ℓ a b = ζ at hζ hzid hm
  generalize ψ γ = Ψ at hRγ hmono hdesc
  have hp : 0 < p := by
    by_contra h
    push Not at h
    nlinarith
  -- p (δ - β) ≤ r' - r
  have h1 : p * (δ - β) ≤ r' - r := by
    have : p * (δ - β) ≤ p * (q * (r' - r)) := mul_le_mul_of_nonneg_left (by linarith) hp.le
    calc p * (δ - β) ≤ p * (q * (r' - r)) := this
      _ = r' - r := by rw [← mul_assoc, hpq, one_mul]
  have hm' : ((δ - γ) ^ 2 - (β - γ) ^ 2) / (2 * ζ) ≤ r - r' := by
    rw [sub_div]; linarith
  rw [div_le_iff₀ (by positivity)] at hm'
  have e : (δ - γ) ^ 2 - (β - γ) ^ 2 = (β - δ) * (2 * (γ - β) + (β - δ)) := by ring
  have h3 : 2 * ζ * (r - r') ≤ 2 * ζ * (p * (β - δ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h4 : (β - δ) * (2 * (γ - β) + (β - δ)) ≤ (β - δ) * (2 * ζ * p) := by
    rw [← e]
    calc (δ - γ) ^ 2 - (β - γ) ^ 2 ≤ 2 * ζ * (r - r') := by linarith
      _ ≤ 2 * ζ * (p * (β - δ)) := h3
      _ = (β - δ) * (2 * ζ * p) := by ring
  have h5 := le_of_mul_le_mul_left h4 (sub_pos.mpr hlt)
  have hs : γ - β < ζ * p := by linarith [sub_pos.mpr hlt]
  have hpd : p ≤ b * d := by
    calc p = p * 1 := (mul_one p).symm
      _ ≤ p * (q * (b * d)) := mul_le_mul_of_nonneg_left hKL hp.le
      _ = (p * q) * (b * d) := by ring
      _ = b * d := by rw [hpq, one_mul]
  have hcp : a / b ^ 2 * p ^ 2 ≤ a * d ^ 2 := by
    have : p ^ 2 ≤ (b * d) ^ 2 := pow_le_pow_left₀ hp.le hpd 2
    calc a / b ^ 2 * p ^ 2 ≤ a / b ^ 2 * (b * d) ^ 2 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = a * d ^ 2 := by field_simp
  have hcpos : 0 < a / b ^ 2 * p ^ 2 := by positivity
  rcases le_or_gt γ β with hγβ | hγβ
  · have := hmono hγβ
    linarith
  · have hd := hdesc hγβ.le
    have hsp : 0 < γ - β := sub_pos.mpr hγβ
    have hgap : 0 < ζ * p - (γ - β) := by linarith
    have key : p * (γ - β) + (ℓ : ℝ) * (γ - β) ^ 2 / 2 < a / b ^ 2 * p ^ 2 := by
      rw [← hzid]
      nlinarith [mul_pos hp hgap, mul_pos (mul_pos hℓ hgap) (add_pos (mul_pos hζ hp) hsp)]
    linarith

end ErrBoundCplxT16Aux

open ErrBoundCplxT16Aux in
open MoreauProx.Characterization NonconvexSplitting.ADMMKL Filter Topology ErrBoundCplx.Cplx in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → EReal) (hf : GammaZero f) (hmin : IsMinZero f)
    (φ ψ : ℝ → ℝ) (rbar r0 : ℝ) (ℓ : NNReal) (hS : ProfileSetting φ ψ rbar r0 ℓ)
    (hKL : KLOnBand f rbar φ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : ℕ → H) (hx : IsSubgradDescentSeq f a b x)
    (hx0 : f (x 0) = (r0 : EReal))
    (α : ℕ → ℝ) (hα : IsWorstCaseProxSeq ψ (φ r0) (zeta ℓ a b) α) :
    ∃ xstar : H, f xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) ∧
      (∀ k, f (x k) ≤ ((ψ (α k) : ℝ) : EReal)) ∧
      ∀ k ≥ 1, ‖x k - xstar‖ ≤ b / a * α k + Real.sqrt (ψ (α (k - 1)) / a) := by
  obtain ⟨-, hH1, hH2⟩ := hx
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ → ℝ, ∀ k, r k = (f (x k)).toReal := ⟨_, fun _ => rfl⟩
  obtain ⟨d, hddef⟩ : ∃ d : ℕ → ℝ, ∀ k, d k = ‖x (k + 1) - x k‖ := ⟨_, fun _ => rfl⟩
  have hd0 : ∀ k, 0 ≤ d k := fun k => by rw [hddef]; exact norm_nonneg _
  -- values of f along the sequence are real numbers in [0, r0]
  have hF : ∀ k, f (x k) = (r k : EReal) ∧ 0 ≤ r k ∧ r k ≤ r0 := by
    intro k
    induction k with
    | zero =>
      rw [hrdef, hx0, EReal.toReal_coe]
      exact ⟨rfl, hS.2.1.le, le_rfl⟩
    | succ k ih =>
      have h1 := hH1 (k + 1) (by omega)
      simp only [Nat.add_sub_cancel] at h1
      have hnn : (0 : EReal) ≤ f (x (k + 1)) := hmin.1 _
      have hle : f (x (k + 1)) ≤ f (x k) :=
        le_trans (le_add_of_nonneg_right (EReal.coe_nonneg.mpr (by positivity))) h1
      have hle' : f (x (k + 1)) ≤ ((r0 : ℝ) : EReal) :=
        le_trans hle (by rw [ih.1]; exact EReal.coe_le_coe_iff.mpr ih.2.2)
      have hne_top : f (x (k + 1)) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hle'
      have hne_bot : f (x (k + 1)) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) hnn
      have hc : f (x (k + 1)) = (r (k + 1) : EReal) := by
        rw [hrdef]; exact (EReal.coe_toReal hne_top hne_bot).symm
      refine ⟨hc, ?_, ?_⟩
      · rw [hc] at hnn; exact EReal.coe_nonneg.mp hnn
      · rw [hc] at hle'; exact EReal.coe_le_coe_iff.mp hle'
  have hr00 : r 0 = r0 := by rw [hrdef, hx0, EReal.toReal_coe]
  -- (H1) in real form
  have F2 : ∀ k, r (k + 1) + a * d k ^ 2 ≤ r k := by
    intro k
    have h1 := hH1 (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h1
    rw [(hF (k + 1)).1, (hF k).1, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    rw [hddef]; exact h1
  -- KL + (H2)
  have F3 : ∀ k, 0 < r (k + 1) → 1 ≤ deriv φ (r (k + 1)) * (b * d k) := by
    intro k h
    obtain ⟨ω, hω, hωn⟩ := hH2 (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hωn
    have hpos' : 0 < f (x (k + 1)) := by rw [(hF _).1]; exact EReal.coe_pos.mpr h
    have hlt : f (x (k + 1)) < (rbar : EReal) := by
      rw [(hF _).1]; exact EReal.coe_lt_coe_iff.mpr (lt_of_le_of_lt (hF _).2.2 hS.2.2.1)
    have := hKL _ hpos' hlt ω hω
    rw [(hF _).1, EReal.toReal_coe] at this
    have hq := hS.1.2.2.2.2.2 (r (k + 1)) ⟨h, lt_of_le_of_lt (hF _).2.2 hS.2.2.1⟩
    calc 1 ≤ deriv φ (r (k + 1)) * ‖ω‖ := this
      _ ≤ deriv φ (r (k + 1)) * (b * d k) :=
          mul_le_mul_of_nonneg_left (by rw [hddef]; exact hωn) hq.le
  have hαI : ∀ k, α k ∈ Set.Icc 0 (φ r0) := by
    intro k
    cases k with
    | zero => rw [hα.1]; exact ⟨(phi_mapsTo hS ⟨hS.2.1.le, le_rfl⟩).1, le_rfl⟩
    | succ k => exact (hα.2 k).1
  have hrI : ∀ k, r k ∈ Set.Icc 0 r0 := fun k => ⟨(hF k).2.1, (hF k).2.2⟩
  -- comparison with the worst-case sequence
  have F4 : ∀ k, φ (r k) ≤ α k := by
    intro k
    induction k with
    | zero => rw [hr00, hα.1]
    | succ k ih =>
      by_cases h : r (k + 1) = 0
      · rw [h, hS.1.2.2.2.1]; exact (hαI _).1
      · have hpos : 0 < r (k + 1) := lt_of_le_of_ne (hF _).2.1 (Ne.symm h)
        have hRγ : r k ≤ ψ (α k) := by
          calc r k = ψ (φ (r k)) := (hS.2.2.2.1 _ (hrI k)).symm
            _ ≤ ψ (α k) := psi_mono hS (phi_mapsTo hS (hrI k)) (hαI k) ih
        exact key_step hS ha hb ⟨hpos, (hF _).2.2⟩ (hd0 k) (F2 k) (F3 k hpos) (hαI k) hRγ
          (hαI (k + 1)) (hα.2 k).2
  have hRψ : ∀ k, r k ≤ ψ (α k) := by
    intro k
    calc r k = ψ (φ (r k)) := (hS.2.2.2.1 _ (hrI k)).symm
      _ ≤ ψ (α k) := psi_mono hS (phi_mapsTo hS (hrI k)) (hαI k) (F4 k)
  have F5 : ∀ k, f (x k) ≤ ((ψ (α k) : ℝ) : EReal) := by
    intro k; rw [(hF k).1]; exact EReal.coe_le_coe_iff.mpr (hRψ k)
  have hφnn : ∀ k, 0 ≤ φ (r k) := fun k =>
    hS.1.2.2.1 _ ⟨(hF k).2.1, lt_of_le_of_lt (hF k).2.2 hS.2.2.1⟩
  -- one step of the finite-length estimate
  have F6 : ∀ m, 2 * d (m + 1) ≤ d m + b / a * (φ (r (m + 1)) - φ (r (m + 1 + 1))) := by
    intro m
    have h2 := F2 (m + 1)
    have hn2 := (hF (m + 1 + 1)).2.1
    by_cases h : r (m + 1) = 0
    · have hd1 : d (m + 1) = 0 := by
        have : a * d (m + 1) ^ 2 ≤ 0 := by linarith
        have : d (m + 1) ^ 2 ≤ 0 := by
          by_contra hc; push Not at hc; nlinarith
        nlinarith [hd0 (m + 1)]
      have hr2 : r (m + 1 + 1) = 0 := by
        have : a * d (m + 1) ^ 2 ≥ 0 := by positivity
        linarith
      rw [hd1, h, hr2]
      simp [hd0 m]
    · have hpos : 0 < r (m + 1) := lt_of_le_of_ne (hF _).2.1 (Ne.symm h)
      have hKLm := F3 m hpos
      have hq := hS.1.2.2.2.2.2 (r (m + 1)) ⟨hpos, lt_of_le_of_lt (hF _).2.2 hS.2.2.1⟩
      have htan := concave_tangent hS.1 ⟨hpos, lt_of_le_of_lt (hF _).2.2 hS.2.2.1⟩
        (r' := r (m + 1 + 1)) ⟨hn2, lt_of_le_of_lt (hF _).2.2 hS.2.2.1⟩
      generalize deriv φ (r (m + 1)) = q at hKLm hq htan
      have hΔ : a * (q * d (m + 1) ^ 2) ≤ φ (r (m + 1)) - φ (r (m + 1 + 1)) := by
        have : q * (a * d (m + 1) ^ 2) ≤ q * (r (m + 1) - r (m + 1 + 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) hq.le
        have e : q * (r (m + 1 + 1) - r (m + 1)) = -(q * (r (m + 1) - r (m + 1 + 1))) := by ring
        have e2 : a * (q * d (m + 1) ^ 2) = q * (a * d (m + 1) ^ 2) := by ring
        linarith
      have h7 : b * q * d (m + 1) ^ 2 ≤ b / a * (φ (r (m + 1)) - φ (r (m + 1 + 1))) := by
        have e : b * q * d (m + 1) ^ 2 = b / a * (a * (q * d (m + 1) ^ 2)) := by
          field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_left hΔ (by positivity)
      have hQ : 0 < b * q := mul_pos hb hq
      have h8 : 0 ≤ b * q * (d m + b * q * d (m + 1) ^ 2 - 2 * d (m + 1)) := by
        nlinarith [sq_nonneg (b * q * d (m + 1) - 1)]
      have h9 := (mul_nonneg_iff_of_pos_left hQ).mp h8
      linarith
  -- partial sums
  have F7 : ∀ k N, ∑ j ∈ Finset.range N, d (k + j + 1) + d (k + N) ≤
      d k + b / a * (φ (r (k + 1)) - φ (r (k + N + 1))) := by
    intro k N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, show k + (N + 1) = k + N + 1 by omega]
      have h6 := F6 (k + N)
      linarith
  have hba : 0 ≤ b / a := by positivity
  have F8 : ∀ k N, ∑ j ∈ Finset.range N, d (k + j + 1) ≤ d k + b / a * φ (r (k + 1)) := by
    intro k N
    have h7 := F7 k N
    have h1 := hd0 (k + N)
    have h2 : 0 ≤ b / a * φ (r (k + N + 1)) := mul_nonneg hba (hφnn _)
    have e : b / a * (φ (r (k + 1)) - φ (r (k + N + 1))) =
        b / a * φ (r (k + 1)) - b / a * φ (r (k + N + 1)) := by ring
    linarith
  have hsum : Summable d := by
    have h := summable_of_sum_range_le (fun j => hd0 (0 + j + 1)) (F8 0)
    simp only [zero_add] at h
    exact (summable_nat_add_iff 1).mp h
  have hcauchy : CauchySeq x :=
    cauchySeq_of_dist_le_of_summable d
      (fun n => le_of_eq (by rw [hddef, dist_comm, dist_eq_norm])) hsum
  obtain ⟨xs, hxs⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- distance to the limit
  have F9 : ∀ k, ‖x (k + 1) - xs‖ ≤ d k + b / a * φ (r (k + 1)) := by
    intro k
    have hb' : ∀ N, dist (x (k + 1)) (x (N + (k + 1))) ≤ d k + b / a * φ (r (k + 1)) := by
      intro N
      have h := dist_le_range_sum_dist (fun j => x (j + (k + 1))) N
      simp only [zero_add] at h
      refine le_trans h (le_trans (le_of_eq ?_) (F8 k N))
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hddef, dist_comm, dist_eq_norm, show i + 1 + (k + 1) = k + i + 1 + 1 by omega,
        show i + (k + 1) = k + i + 1 by omega]
    have ht : Tendsto (fun N => dist (x (k + 1)) (x (N + (k + 1)))) atTop
        (𝓝 (dist (x (k + 1)) xs)) :=
      tendsto_const_nhds.dist ((tendsto_add_atTop_iff_nat (k + 1)).mpr hxs)
    rw [← dist_eq_norm]
    exact le_of_tendsto' ht hb'
  -- f (x k) → 0
  obtain ⟨z, hz⟩ := hmin.2
  have F10 : ∀ k, r (k + 1) ≤ ‖z - x (k + 1)‖ * (b * d k) := by
    intro k
    obtain ⟨ω, hω, hωn⟩ := hH2 (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hωn
    have h := hω.2.2 z
    rw [hz, (hF _).1, ← EReal.coe_add, ← EReal.coe_zero, EReal.coe_le_coe_iff] at h
    have hi : -(‖z - x (k + 1)‖ * ‖ω‖) ≤ inner ℝ (z - x (k + 1)) ω := by
      have := abs_real_inner_le_norm (z - x (k + 1)) ω
      exact neg_le_of_abs_le this
    have : ‖z - x (k + 1)‖ * ‖ω‖ ≤ ‖z - x (k + 1)‖ * (b * d k) :=
      mul_le_mul_of_nonneg_left (by rw [hddef]; exact hωn) (norm_nonneg _)
    linarith
  have hx1 : Tendsto (fun k => x (k + 1)) atTop (𝓝 xs) := (tendsto_add_atTop_iff_nat 1).mpr hxs
  have hrt : Tendsto (fun k => r (k + 1)) atTop (𝓝 0) := by
    have hup : Tendsto (fun k => ‖z - x (k + 1)‖ * (b * d k)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => ‖z - x (k + 1)‖) atTop (𝓝 ‖z - xs‖) :=
        (tendsto_const_nhds.sub hx1).norm
      have h2 : Tendsto (fun k => b * d k) atTop (𝓝 (b * 0)) :=
        hsum.tendsto_atTop_zero.const_mul b
      simpa using h1.mul h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun k => (hF (k + 1)).2.1) F10
  have hfxs : f xs = 0 := by
    refine le_antisymm ?_ (hmin.1 xs)
    by_contra hc
    push Not at hc
    obtain ⟨y, hy0, hyf⟩ := EReal.lt_iff_exists_real_btwn.mp hc
    have hy0' : (0 : ℝ) < y := EReal.coe_pos.mp hy0
    have hev := hf.2.2.2 xs (y : EReal) hyf
    have h2 : ∀ᶠ k in atTop, (y : EReal) < f (x (k + 1)) := hx1.eventually hev
    have h3 : ∀ᶠ k in atTop, r (k + 1) < y := hrt.eventually (gt_mem_nhds hy0')
    obtain ⟨k, hk2, hk3⟩ := (h2.and h3).exists
    rw [(hF _).1, EReal.coe_lt_coe_iff] at hk2
    linarith
  refine ⟨xs, hfxs, hxs, F5, ?_⟩
  intro k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hdsq : d m ≤ Real.sqrt (ψ (α m) / a) := by
    have h2 := F2 m
    have h3 := (hF (m + 1)).2.1
    have h4 := hRψ m
    have : d m ^ 2 ≤ ψ (α m) / a := by
      rw [le_div_iff₀ ha]; nlinarith
    calc d m = Real.sqrt (d m ^ 2) := (Real.sqrt_sq (hd0 m)).symm
      _ ≤ Real.sqrt (ψ (α m) / a) := Real.sqrt_le_sqrt this
  have h9 := F9 m
  have h10 : b / a * φ (r (m + 1)) ≤ b / a * α (m + 1) :=
    mul_le_mul_of_nonneg_left (F4 (m + 1)) hba
  linarith
