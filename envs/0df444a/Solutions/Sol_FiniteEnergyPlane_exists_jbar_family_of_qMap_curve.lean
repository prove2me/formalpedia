-- Prove2me | solution 1 for FiniteEnergyPlane.exists_jbar_family_of_qMap_curve
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T10:46:38.282806+00:00
-- url     : https://prove2.me/submissions/b0c290d8-d829-4175-ae90-c546f8111814

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Definitions.Def_FiniteEnergyPlane_QMember
import Theorems.Thm_FiniteEnergyPlane_qMember_eq_add_clm
import Theorems.Thm_FiniteEnergyPlane_exists_norm_qMember_le
import Theorems.Thm_FiniteEnergyPlane_contDiff_qMember_of_qMap_eq_zero
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_qFamily_of_qMap_eq_zero
import Theorems.Thm_FiniteEnergyPlane_exists_norm_fderiv_qMember_le



-- FILE: _imports_RSK_RG.lean


-- FILE: RSK_RG.lean
/-!
# Reduction of `exists_jbar_family_of_qMap_curve` to its children

The family is `qFamily` along the curve. Its members are the plane maps `qMember`, which at each
`z` are affine in the unknown; the weighted bounds and closeness follow from the pointwise and
`C¹` estimates of the children.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

namespace QRG

/-- The linear part of `qMember` at `z`. -/
def pLc (χT χN β : ℝ → ℝ) (z : ℂ) : QDom →L[ℝ] ℂ × ℂ :=
  Classical.choose (qMember_eq_add_clm χT χN β z)

/-- The member of `x`. -/
def pG (χT χN β : ℝ → ℝ) (x : QDom) (z : ℂ) : ℂ × ℂ := (z, 0) + pLc χT χN β z x

/-- The family of a curve. -/
def fam (χT χN β : ℝ → ℝ) (γ : ℝ → QDom) (p : ℂ × ℝ) : ℂ × ℂ := pG χT χN β (γ p.2) p.1

lemma pG_eq_qMember (χT χN β : ℝ → ℝ) : pG χT χN β = qMember χT χN β := by
  funext x z
  exact (Classical.choose_spec (qMember_eq_add_clm χT χN β z) x).symm

lemma fam_eq_qFamily (χT χN β : ℝ → ℝ) : fam χT χN β = qFamily χT χN β := by
  funext γ p
  simp only [fam, qFamily, pG_eq_qMember]

lemma pLc_zero (χT χN β : ℝ → ℝ) (y : QDom) : pLc χT χN β 0 y = (0, y.2.1) := by
  have h := congrFun (congrFun (pG_eq_qMember χT χN β) y) 0
  simp only [pG, qMember] at h
  rwa [show ((0 : ℂ), (0 : ℂ)) = (0 : ℂ × ℂ) from rfl, zero_add] at h

@[simp] lemma pG_zero (χT χN β : ℝ → ℝ) (z : ℂ) : pG χT χN β 0 z = (z, 0) := by
  simp [pG]

/-! ### Elementary helpers -/

variable {χT χN β : ℝ → ℝ}

lemma fderiv_fam_apply {γ : ℝ → QDom} {z : ℂ} {t : ℝ}
    (hF : DifferentiableAt ℝ (fam χT χN β γ) (z, t)) (hγ : DifferentiableAt ℝ γ t) (Δ : ℂ)
    (τ : ℝ) :
    fderiv ℝ (fam χT χN β γ) (z, t) (Δ, τ) =
      fderiv ℝ (pG χT χN β (γ t)) z Δ + τ • pLc χT χN β z (deriv γ t) := by
  have h1 : HasFDerivAt (pG χT χN β (γ t))
      ((fderiv ℝ (fam χT χN β γ) (z, t)).comp (ContinuousLinearMap.inl ℝ ℂ ℝ)) z := by
    have h := hF.hasFDerivAt.comp z (hasFDerivAt_prodMk_left (𝕜 := ℝ) z t)
    exact h
  have h2 : HasDerivAt (fun t' => fam χT χN β γ (z, t'))
      (fderiv ℝ (fam χT χN β γ) (z, t) ((0 : ℂ), (1 : ℝ))) t := by
    have hl : HasDerivAt (fun t' : ℝ => (z, t')) ((0 : ℂ), (1 : ℝ)) t :=
      (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
    exact hF.hasFDerivAt.comp_hasDerivAt t hl
  have h3 : HasDerivAt (fun t' => fam χT χN β γ (z, t')) (pLc χT χN β z (deriv γ t)) t := by
    have := ((pLc χT χN β z).hasFDerivAt.comp_hasDerivAt t hγ.hasDerivAt).const_add ((z, 0) : ℂ × ℂ)
    exact this
  have e2 := h2.unique h3
  have e1 := h1.fderiv
  have hsplit : ((Δ, τ) : ℂ × ℝ) = (Δ, 0) + τ • ((0 : ℂ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, e2, e1]
  rfl

lemma fderiv_fst_apply {f : ℂ → ℂ × ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (w : ℂ) :
    fderiv ℝ (fun z => (f z).1) z w = (fderiv ℝ f z w).1 := by
  rw [hf.hasFDerivAt.fst.fderiv]; rfl

lemma fderiv_snd_apply {f : ℂ → ℂ × ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (w : ℂ) :
    fderiv ℝ (fun z => (f z).2) z w = (fderiv ℝ f z w).2 := by
  rw [hf.hasFDerivAt.snd.fderiv]; rfl

lemma exists_inv_of_near_id (A : ℂ →L[ℝ] ℂ) (hA : ‖A - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2)
    (w : ℂ) : ∃ Δ, A Δ = w ∧ ‖Δ‖ ≤ 2 * ‖w‖ := by
  have hlow : ∀ Δ, ‖Δ‖ ≤ 2 * ‖A Δ‖ := by
    intro Δ
    have h1 : ‖(A - ContinuousLinearMap.id ℝ ℂ) Δ‖ ≤ 1 / 2 * ‖Δ‖ :=
      ((A - ContinuousLinearMap.id ℝ ℂ).le_opNorm Δ).trans
        (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
    have h2 : Δ = A Δ - (A - ContinuousLinearMap.id ℝ ℂ) Δ := by simp
    have h3 : ‖Δ‖ ≤ ‖A Δ‖ + ‖(A - ContinuousLinearMap.id ℝ ℂ) Δ‖ := by
      conv_lhs => rw [h2]
      exact norm_sub_le _ _
    linarith
  have hinj : Function.Injective (A : ℂ →ₗ[ℝ] ℂ) := by
    intro a a' h
    have h' : A (a - a') = 0 := by
      rw [map_sub]; exact sub_eq_zero.2 h
    have := hlow (a - a')
    rw [h', norm_zero, mul_zero] at this
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  obtain ⟨Δ, hΔ⟩ := (LinearMap.injective_iff_surjective.1 hinj) w
  refine ⟨Δ, hΔ, ?_⟩
  have := hlow Δ
  have hΔ' : A Δ = w := hΔ
  rwa [hΔ'] at this

lemma one_add_norm_pos (z : ℂ) : 0 < 1 + ‖z‖ := by positivity

lemma one_le_one_add_norm (z : ℂ) : 1 ≤ 1 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg _)

lemma rpow_le_one' {z : ℂ} {e : ℝ} (he : e ≤ 0) : (1 + ‖z‖) ^ e ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_le_one_add_norm z) he

lemma rpow_le_self' {z : ℂ} {e : ℝ} (he : e ≤ 1) : (1 + ‖z‖) ^ e ≤ 1 + ‖z‖ := by
  have := Real.rpow_le_rpow_of_exponent_le (one_le_one_add_norm z) he
  rwa [Real.rpow_one] at this

lemma self_le_rpow' {z : ℂ} {e : ℝ} (he : 1 ≤ e) : 1 + ‖z‖ ≤ (1 + ‖z‖) ^ e := by
  have := Real.rpow_le_rpow_of_exponent_le (one_le_one_add_norm z) he
  rwa [Real.rpow_one] at this

/-- The rate algebra of the `Δ` clause. -/
lemma rate_alg {z : ℂ} {e eT B P K : ℝ} (heT : eT ≤ 0) (hB0 : 0 ≤ B)
    (hB : (1 + ‖z‖) ^ (1 - e) * B ≤ K) (hP : P ≤ (1 + ‖z‖) ^ (1 + eT)) :
    B * P ≤ K * (1 + ‖z‖) ^ e := by
  have ha := one_add_norm_pos z
  have hsplit : (1 + ‖z‖) ^ (1 + eT) = (1 + ‖z‖) ^ (1 - e) * (1 + ‖z‖) ^ (e + eT) := by
    rw [← Real.rpow_add ha]; ring_nf
  have hle : (1 + ‖z‖) ^ (e + eT) ≤ (1 + ‖z‖) ^ e :=
    Real.rpow_le_rpow_of_exponent_le (one_le_one_add_norm z) (by linarith)
  have hK : 0 ≤ K := le_trans (mul_nonneg (Real.rpow_nonneg ha.le _) hB0) hB
  calc B * P ≤ B * ((1 + ‖z‖) ^ (1 - e) * (1 + ‖z‖) ^ (e + eT)) := by
        rw [← hsplit]; exact mul_le_mul_of_nonneg_left hP hB0
    _ = ((1 + ‖z‖) ^ (1 - e) * B) * (1 + ‖z‖) ^ (e + eT) := by ring
    _ ≤ K * (1 + ‖z‖) ^ e :=
        mul_le_mul hB hle (Real.rpow_nonneg ha.le _) hK

/-- Small values along a continuous curve through `0`. -/
lemma exists_small {γ : ℝ → QDom} (hγ : ContinuousAt γ 0) (hγ0 : γ 0 = 0) {η : ℝ}
    (hη : 0 < η) : ∃ r > 0, ∀ t ∈ Ioo (-r) r, ‖γ t‖ < η := by
  have h := Metric.continuousAt_iff.1 hγ η hη
  obtain ⟨r, hr, hr'⟩ := h
  refine ⟨r, hr, fun t ht => ?_⟩
  have hd : dist t 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_lt]; exact ⟨ht.1, ht.2⟩
  have := hr' hd
  rwa [hγ0, dist_zero_right] at this

/-! ### The algebra of the `Δ` clause -/

lemma delta_alg {z : ℂ} {e eT K₀ K₁ X Y : ℝ} (heT : eT ≤ 0) (A B : ℂ →L[ℝ] ℂ) (w1 w2 : ℂ)
    (hA : ‖A - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2) (hB : (1 + ‖z‖) ^ (1 - e) * ‖B‖ ≤ K₁ * X)
    (hw1 : ‖w1‖ ≤ K₀ * Y * (1 + ‖z‖) ^ (1 + eT)) (hw2 : ‖w2‖ ≤ K₀ * Y * (1 + ‖z‖) ^ e)
    (hK₀ : 0 ≤ K₀) (hY : 0 ≤ Y) :
    ∃ Δ, A Δ + w1 = 0 ∧ ‖B Δ + w2‖ ≤ (2 * K₁ * X * K₀ * Y + K₀ * Y) * (1 + ‖z‖) ^ e := by
  obtain ⟨Δ, hΔ, hΔn⟩ := exists_inv_of_near_id A hA (-w1)
  refine ⟨Δ, by rw [hΔ]; ring, ?_⟩
  rw [norm_neg] at hΔn
  have hrate := rate_alg (P := (1 + ‖z‖) ^ (1 + eT)) heT (norm_nonneg B) hB le_rfl
  have hBΔ : ‖B Δ‖ ≤ 2 * K₀ * Y * (K₁ * X * (1 + ‖z‖) ^ e) := by
    calc ‖B Δ‖ ≤ ‖B‖ * (2 * (K₀ * Y * (1 + ‖z‖) ^ (1 + eT))) :=
          (B.le_opNorm Δ).trans (mul_le_mul_of_nonneg_left (hΔn.trans
            (mul_le_mul_of_nonneg_left hw1 (by norm_num))) (norm_nonneg _))
      _ = 2 * K₀ * Y * (‖B‖ * (1 + ‖z‖) ^ (1 + eT)) := by ring
      _ ≤ 2 * K₀ * Y * (K₁ * X * (1 + ‖z‖) ^ e) :=
          mul_le_mul_of_nonneg_left hrate (by positivity)
  calc ‖B Δ + w2‖ ≤ ‖B Δ‖ + ‖w2‖ := norm_add_le _ _
    _ ≤ 2 * K₀ * Y * (K₁ * X * (1 + ‖z‖) ^ e) + K₀ * Y * (1 + ‖z‖) ^ e := add_le_add hBΔ hw2
    _ = (2 * K₁ * X * K₀ * Y + K₀ * Y) * (1 + ‖z‖) ^ e := by ring

/-! ### The clauses for one member -/

lemma member_part {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {ρ δ δT K₀ K₁ : ℝ} (hπ : 0 < 2 * π)
    (he : δ / (2 * π) < 0) (heT : δT / (2 * π) < 0) (hK₀ : 0 < K₀)
    (hC0 : ∀ (y : QDom) (z : ℂ),
      ‖(pLc χT χN β z y).1‖ ≤ K₀ * ‖y‖ * (1 + ‖z‖) ^ (1 + δT / (2 * π)) ∧
      ‖(pLc χT χN β z y).2‖ ≤ K₀ * ‖y‖ * (1 + ‖z‖) ^ (δ / (2 * π)))
    {γ : ℝ → QDom} {t : ℝ}
    (hsm : ContDiff ℝ ∞ (pG χT χN β (γ t)) ∧ JHolomorphic.IsJHolomorphicOn Jbar univ (pG χT χN β (γ t)))
    (hFd : ∀ z, DifferentiableAt ℝ (fam χT χN β γ) (z, t)) (hγd : DifferentiableAt ℝ γ t)
    (hC1 : ∀ z : ℂ,
      ‖fderiv ℝ (fun z => (pG χT χN β (γ t) z).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ K₁ * ‖γ t‖ ∧
      (1 + ‖z‖) ^ (1 - δ / (2 * π)) * ‖fderiv ℝ (fun z => (pG χT χN β (γ t) z).2) z‖ ≤
        K₁ * ‖γ t‖)
    (hxs : K₁ * ‖γ t‖ ≤ 1 / 2) (hρ : K₀ * ‖γ t‖ < ρ) :
    ContDiff ℝ ∞ (fun z => fam χT χN β γ (z, t)) ∧
      (∀ z, (fam χT χN β γ (z, t)).2 ∈ ball (0 : ℂ) ρ) ∧
      JHolomorphic.IsJHolomorphicOn Jbar Set.univ (fun z => fam χT χN β γ (z, t)) ∧
      (∃ C β' : ℝ, 0 < β' ∧ ∀ z, ‖(fam χT χN β γ (z, t)).1 - z‖ ≤ C * (1 + ‖z‖) ^ (1 - β')) ∧
      (∃ C : ℝ, ∀ z, ‖(fam χT χN β γ (z, t)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
      ∃ C : ℝ, ∀ z, ∃ Δ : ℂ, (fderiv ℝ (fam χT χN β γ) (z, t) (Δ, 1)).1 = 0 ∧
        ‖(fderiv ℝ (fam χT χN β γ) (z, t) (Δ, 1)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π)) := by
  have hv : ∀ (x : QDom) z, (pG χT χN β x z).2 = (pLc χT χN β z x).2 := fun x z => by simp [pG]
  have hu : ∀ (x : QDom) z, (pG χT χN β x z).1 - z = (pLc χT χN β z x).1 := fun x z => by
    simp [pG]
  have hmd : ∀ z, DifferentiableAt ℝ (pG χT χN β (γ t)) z := fun z =>
    (hsm.1.differentiable (by simp)) z
  refine ⟨hsm.1, fun z => ?_, hsm.2, ⟨K₀ * ‖γ t‖, -(δT / (2 * π)), by linarith, fun z => ?_⟩,
    ⟨K₀ * ‖γ t‖, fun z => ?_⟩,
    ⟨2 * K₁ * ‖γ t‖ * K₀ * ‖deriv γ t‖ + K₀ * ‖deriv γ t‖, fun z => ?_⟩⟩
  · rw [mem_ball, dist_zero_right]
    show ‖(pG χT χN β (γ t) z).2‖ < ρ
    rw [hv]
    calc ‖(pLc χT χN β z (γ t)).2‖ ≤ K₀ * ‖γ t‖ * (1 + ‖z‖) ^ (δ / (2 * π)) := (hC0 _ z).2
      _ ≤ K₀ * ‖γ t‖ * 1 := mul_le_mul_of_nonneg_left (rpow_le_one' he.le) (by positivity)
      _ < ρ := by rw [mul_one]; exact hρ
  · show ‖(pG χT χN β (γ t) z).1 - z‖ ≤ _
    rw [hu, show (1 : ℝ) - -(δT / (2 * π)) = 1 + δT / (2 * π) by ring]
    exact (hC0 _ z).1
  · show ‖(pG χT χN β (γ t) z).2‖ ≤ _
    rw [hv]; exact (hC0 _ z).2
  · obtain ⟨Δ, h1, h2⟩ := delta_alg heT.le
      (fderiv ℝ (fun z => (pG χT χN β (γ t) z).1) z)
      (fderiv ℝ (fun z => (pG χT χN β (γ t) z).2) z)
      (pLc χT χN β z (deriv γ t)).1 (pLc χT χN β z (deriv γ t)).2
      ((hC1 z).1.trans hxs) (hC1 z).2 (hC0 _ z).1 (hC0 _ z).2 hK₀.le (norm_nonneg _)
    refine ⟨Δ, ?_, ?_⟩
    · rw [fderiv_fst_apply (hmd z)] at h1
      simp only [fderiv_fam_apply (hFd z) hγd, one_smul, Prod.fst_add]
      exact h1
    · rw [fderiv_snd_apply (hmd z)] at h2
      simp only [fderiv_fam_apply (hFd z) hγd, one_smul, Prod.snd_add]
      exact h2

/-! ### Closeness for one member -/

lemma close_part {δ δT K₀ K₁ ε : ℝ} (he : δ / (2 * π) < 0) (heT : δT / (2 * π) < 0)
    (hC0 : ∀ (y : QDom) (z : ℂ),
      ‖(pLc χT χN β z y).1‖ ≤ K₀ * ‖y‖ * (1 + ‖z‖) ^ (1 + δT / (2 * π)) ∧
      ‖(pLc χT χN β z y).2‖ ≤ K₀ * ‖y‖ * (1 + ‖z‖) ^ (δ / (2 * π)))
    (x : QDom) (hK0x : K₀ * ‖x‖ ≤ ε) (hK1x : K₁ * ‖x‖ ≤ ε) (hK₀ : 0 < K₀) (z : ℂ)
    (hA : ‖fderiv ℝ (fun z => (pG χT χN β x z).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ K₁ * ‖x‖)
    (hB : (1 + ‖z‖) ^ (1 - δ / (2 * π)) * ‖fderiv ℝ (fun z => (pG χT χN β x z).2) z‖ ≤
      K₁ * ‖x‖) :
    ‖(pG χT χN β x z).1 - z‖ ≤ ε * (1 + ‖z‖) ∧ ‖(pG χT χN β x z).2‖ ≤ ε ∧
      ‖fderiv ℝ (fun z => (pG χT χN β x z).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ ε ∧
      (1 + ‖z‖) * ‖fderiv ℝ (fun z => (pG χT χN β x z).2) z‖ ≤ ε := by
  have hv : (pG χT χN β x z).2 = (pLc χT χN β z x).2 := by simp [pG]
  have hu : (pG χT χN β x z).1 - z = (pLc χT χN β z x).1 := by simp [pG]
  refine ⟨?_, ?_, hA.trans hK1x, ?_⟩
  · rw [hu]
    calc ‖(pLc χT χN β z x).1‖ ≤ K₀ * ‖x‖ * (1 + ‖z‖) ^ (1 + δT / (2 * π)) := (hC0 x z).1
      _ ≤ K₀ * ‖x‖ * (1 + ‖z‖) :=
          mul_le_mul_of_nonneg_left (rpow_le_self' (by linarith)) (by positivity)
      _ ≤ ε * (1 + ‖z‖) := mul_le_mul_of_nonneg_right hK0x (one_add_norm_pos z).le
  · rw [hv]
    calc ‖(pLc χT χN β z x).2‖ ≤ K₀ * ‖x‖ * (1 + ‖z‖) ^ (δ / (2 * π)) := (hC0 x z).2
      _ ≤ K₀ * ‖x‖ * 1 := mul_le_mul_of_nonneg_left (rpow_le_one' he.le) (by positivity)
      _ ≤ ε := by rw [mul_one]; exact hK0x
  · calc (1 + ‖z‖) * ‖fderiv ℝ (fun z => (pG χT χN β x z).2) z‖
        ≤ (1 + ‖z‖) ^ (1 - δ / (2 * π)) * ‖fderiv ℝ (fun z => (pG χT χN β x z).2) z‖ :=
          mul_le_mul_of_nonneg_right (self_le_rpow' (by linarith)) (norm_nonneg _)
      _ ≤ ε := hB.trans hK1x

lemma mul_le_of_lt_div {K a ε : ℝ} (hK : 0 ≤ K) (ha : a < ε / (K + 1)) (hε : 0 < ε) :
    K * a ≤ ε := by
  rcases le_or_gt a 0 with h | h
  · nlinarith
  have h1 : a * (K + 1) < ε := by rwa [lt_div_iff₀ (by linarith)] at ha
  nlinarith

/-! ### The glue -/

lemma glue_core {ρ δ δT : ℝ} (hρ : 0 < ρ) {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ}
    (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0) (l : ℕ)
    {K₀ : ℝ} (hK₀ : 0 < K₀)
    (hC0 : ∀ (y : QDom) (z : ℂ),
      ‖(pLc χT χN β z y).1‖ ≤ K₀ * ‖y‖ * (1 + ‖z‖) ^ (1 + δT / (2 * π)) ∧
      ‖(pLc χT χN β z y).2‖ ≤ K₀ * ‖y‖ * (1 + ‖z‖) ^ (δ / (2 * π)))
    {ε₁ : ℝ} (hε₁ : 0 < ε₁)
    (hreg : ∀ x ∈ ball (0 : QDom) ε₁, qMap Jbar χT χN β x = 0 →
      ContDiff ℝ ∞ (pG χT χN β x) ∧ JHolomorphic.IsJHolomorphicOn Jbar univ (pG χT χN β x))
    {ε₂ : ℝ} (hε₂ : 0 < ε₂)
    (hfam : ∀ r > 0, ∀ γ : ℝ → QDom, ContDiffOn ℝ ∞ γ (Ioo (-r) r) →
      (∀ t ∈ Ioo (-r) r, γ t ∈ ball (0 : QDom) ε₂ ∧ qMap Jbar χT χN β (γ t) = 0) →
      ∀ n : ℕ, ContDiffOn ℝ n (fam χT χN β γ) (univ ×ˢ Ioo (-r) r))
    {ε₃ K₁ : ℝ} (hε₃ : 0 < ε₃) (hK₁ : 0 ≤ K₁)
    (hC1 : ∀ x ∈ ball (0 : QDom) ε₃, qMap Jbar χT χN β x = 0 → ∀ z : ℂ,
      ‖fderiv ℝ (fun z => (pG χT χN β x z).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ K₁ * ‖x‖ ∧
      (1 + ‖z‖) ^ (1 - δ / (2 * π)) * ‖fderiv ℝ (fun z => (pG χT χN β x z).2) z‖ ≤ K₁ * ‖x‖) :
    ∃ ε₀ > 0, ∀ r > 0, ∀ (γ : ℝ → QDom) (k : QDom), ContDiffOn ℝ ∞ γ (Set.Ioo (-r) r) →
      γ 0 = 0 → HasDerivAt γ k 0 →
      (∀ t ∈ Set.Ioo (-r) r, γ t ∈ ball 0 ε₀ ∧ qMap Jbar χT χN β (γ t) = 0) →
    ∃ r > 0, ∃ G : ℂ × ℝ → ℂ × ℂ, ContDiffOn ℝ l G (Set.univ ×ˢ Set.Ioo (-r) r) ∧
      (∀ z, G (z, 0) = (z, 0)) ∧ (fderiv ℝ G (0, 0) (0, 1)).2 = k.2.1 ∧
      (∀ t ∈ Set.Ioo (-r) r,
        ContDiff ℝ ∞ (fun z => G (z, t)) ∧ (∀ z, (G (z, t)).2 ∈ ball (0 : ℂ) ρ) ∧
        JHolomorphic.IsJHolomorphicOn Jbar Set.univ (fun z => G (z, t)) ∧
        (∃ C β : ℝ, 0 < β ∧ ∀ z, ‖(G (z, t)).1 - z‖ ≤ C * (1 + ‖z‖) ^ (1 - β)) ∧
        (∃ C : ℝ, ∀ z, ‖(G (z, t)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
        ∃ C : ℝ, ∀ z, ∃ Δ : ℂ, (fderiv ℝ G (z, t) (Δ, 1)).1 = 0 ∧
          ‖(fderiv ℝ G (z, t) (Δ, 1)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
      ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r', ∀ z,
        ‖(G (z, t)).1 - z‖ ≤ ε * (1 + ‖z‖) ∧ ‖(G (z, t)).2‖ ≤ ε ∧
        ‖fderiv ℝ (fun z => (G (z, t)).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ ε ∧
        (1 + ‖z‖) * ‖fderiv ℝ (fun z => (G (z, t)).2) z‖ ≤ ε := by
  have hπ : 0 < 2 * π := by positivity
  have he : δ / (2 * π) < 0 := div_neg_of_neg_of_pos hδ hπ
  have heT : δT / (2 * π) < 0 := div_neg_of_neg_of_pos hδT.2 hπ
  refine ⟨min (min ε₁ ε₂) (min ε₃ (ρ / (K₀ + 1))),
    lt_min (lt_min hε₁ hε₂) (lt_min hε₃ (div_pos hρ (by linarith))), ?_⟩
  intro r hr γ k hγ hγ0 hγk hγt
  have hγt' : ∀ t ∈ Ioo (-r) r, qMap Jbar χT χN β (γ t) = 0 ∧ γ t ∈ ball (0 : QDom) ε₁ ∧
      γ t ∈ ball (0 : QDom) ε₂ ∧ γ t ∈ ball (0 : QDom) ε₃ ∧ ‖γ t‖ < ρ / (K₀ + 1) := by
    intro t ht
    obtain ⟨h1, h2⟩ := hγt t ht
    rw [mem_ball, dist_zero_right] at h1
    refine ⟨h2, ?_, ?_, ?_, ?_⟩
    · rw [mem_ball, dist_zero_right]
      exact lt_of_lt_of_le h1 ((min_le_left _ _).trans (min_le_left _ _))
    · rw [mem_ball, dist_zero_right]
      exact lt_of_lt_of_le h1 ((min_le_left _ _).trans (min_le_right _ _))
    · rw [mem_ball, dist_zero_right]
      exact lt_of_lt_of_le h1 ((min_le_right _ _).trans (min_le_left _ _))
    · exact lt_of_lt_of_le h1 ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨η, hη, hηt⟩ := exists_small hγk.continuousAt hγ0
    (show (0 : ℝ) < (1 / 2) / (K₁ + 1) by positivity)
  have hr₁r : min r η ≤ r := min_le_left _ _
  have hsub : ∀ t ∈ Ioo (-min r η) (min r η), t ∈ Ioo (-r) r := fun t ht =>
    ⟨by linarith [ht.1], lt_of_lt_of_le ht.2 hr₁r⟩
  have hsubη : ∀ t ∈ Ioo (-min r η) (min r η), t ∈ Ioo (-η) η := fun t ht =>
    ⟨by linarith [ht.1, min_le_right r η], lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  have hFC := hfam r hr γ hγ (fun t ht => ⟨(hγt' t ht).2.2.1, (hγt' t ht).1⟩)
  have hopen : IsOpen ((univ : Set ℂ) ×ˢ Ioo (-r) r) := isOpen_univ.prod isOpen_Ioo
  have hFd : ∀ t ∈ Ioo (-r) r, ∀ z, DifferentiableAt ℝ (fam χT χN β γ) (z, t) := by
    intro t ht z
    exact ((hFC 1).differentiableOn (by simp) (z, t) ⟨mem_univ _, ht⟩).differentiableAt
      (hopen.mem_nhds ⟨mem_univ _, ht⟩)
  have hγd : ∀ t ∈ Ioo (-r) r, DifferentiableAt ℝ γ t := fun t ht =>
    (hγ.differentiableOn (by simp) t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)
  refine ⟨min r η, lt_min hr hη, fam χT χN β γ, (hFC l).mono (prod_mono subset_rfl
    (Ioo_subset_Ioo (neg_le_neg hr₁r) hr₁r)), ?_, ?_, ?_, ?_⟩
  · intro z
    simp [fam, hγ0]
  · have h0 : (0 : ℝ) ∈ Ioo (-r) r := ⟨by linarith, hr⟩
    rw [fderiv_fam_apply (hFd 0 h0 0) (hγd 0 h0) 0 1, map_zero, zero_add, one_smul, pLc_zero,
      hγk.deriv]
  · intro t ht
    have ht' := hsub t ht
    have hq := (hγt' t ht').1
    have hρt : K₀ * ‖γ t‖ < ρ := by
      have h3 : ‖γ t‖ * (K₀ + 1) < ρ := by
        have := (hγt' t ht').2.2.2.2
        rwa [lt_div_iff₀ (by linarith)] at this
      nlinarith [norm_nonneg (γ t)]
    exact member_part hπ he heT hK₀ hC0 (hreg (γ t) (hγt' t ht').2.1 hq) (hFd t ht')
      (hγd t ht') (hC1 (γ t) (hγt' t ht').2.2.2.1 hq)
      (mul_le_of_lt_div hK₁ (hηt t (hsubη t ht)) (by norm_num)) hρt
  · intro ε hε
    obtain ⟨η', hη', hη't⟩ := exists_small hγk.continuousAt hγ0
      (show (0 : ℝ) < ε / (K₀ + K₁ + 1) by positivity)
    refine ⟨min (min r η) η', ⟨lt_min (lt_min hr hη) hη', min_le_left _ _⟩, fun t ht z => ?_⟩
    have ht1 : t ∈ Ioo (-min r η) (min r η) := ⟨by linarith [ht.1, min_le_left (min r η) η'],
      lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
    have ht' := hsub t ht1
    have hq := (hγt' t ht').1
    have hxs : ‖γ t‖ < ε / (K₀ + K₁ + 1) :=
      hη't t ⟨by linarith [ht.1, min_le_right (min r η) η'], lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
    have hK0x : K₀ * ‖γ t‖ ≤ ε := by
      have h1 : ‖γ t‖ < ε / (K₀ + 1) := lt_of_lt_of_le hxs
        (div_le_div_of_nonneg_left hε.le (by positivity) (by linarith))
      exact mul_le_of_lt_div hK₀.le h1 hε
    have hK1x : K₁ * ‖γ t‖ ≤ ε := by
      have h1 : ‖γ t‖ < ε / (K₁ + 1) := lt_of_lt_of_le hxs
        (div_le_div_of_nonneg_left hε.le (by positivity) (by linarith))
      exact mul_le_of_lt_div hK₁ h1 hε
    obtain ⟨hA, hB⟩ := hC1 (γ t) (hγt' t ht').2.2.2.1 hq z
    exact close_part he heT hC0 (γ t) hK0x hK1x hK₀ z hA hB



set_option maxHeartbeats 2000000 in
theorem exists_jbar_family_of_qMap_curve_aux (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) (l : ℕ) :
    ∃ ε₀ > 0, ∀ r > 0, ∀ (γ : ℝ → QDom) (k : QDom), ContDiffOn ℝ ∞ γ (Set.Ioo (-r) r) →
      γ 0 = 0 → HasDerivAt γ k 0 →
      (∀ t ∈ Set.Ioo (-r) r, γ t ∈ ball 0 ε₀ ∧ qMap Jbar χT χN β (γ t) = 0) →
    ∃ r > 0, ∃ G : ℂ × ℝ → ℂ × ℂ, ContDiffOn ℝ l G (Set.univ ×ˢ Set.Ioo (-r) r) ∧
      (∀ z, G (z, 0) = (z, 0)) ∧ (fderiv ℝ G (0, 0) (0, 1)).2 = k.2.1 ∧
      (∀ t ∈ Set.Ioo (-r) r,
        ContDiff ℝ ∞ (fun z => G (z, t)) ∧ (∀ z, (G (z, t)).2 ∈ ball (0 : ℂ) ρ) ∧
        JHolomorphic.IsJHolomorphicOn Jbar Set.univ (fun z => G (z, t)) ∧
        (∃ C β : ℝ, 0 < β ∧ ∀ z, ‖(G (z, t)).1 - z‖ ≤ C * (1 + ‖z‖) ^ (1 - β)) ∧
        (∃ C : ℝ, ∀ z, ‖(G (z, t)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
        ∃ C : ℝ, ∀ z, ∃ Δ : ℂ, (fderiv ℝ G (z, t) (Δ, 1)).1 = 0 ∧
          ‖(fderiv ℝ G (z, t) (Δ, 1)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
      ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r', ∀ z,
        ‖(G (z, t)).1 - z‖ ≤ ε * (1 + ‖z‖) ∧ ‖(G (z, t)).2‖ ≤ ε ∧
        ‖fderiv ℝ (fun z => (G (z, t)).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ ε ∧
        (1 + ‖z‖) * ‖fderiv ℝ (fun z => (G (z, t)).2) z‖ ≤ ε := by
  obtain ⟨K₀, hK₀, hC0⟩ := exists_norm_qMember_le δ δT hδ hδT χT χN β hχT hχN hβ
  obtain ⟨ε₁, hε₁, hreg⟩ := contDiff_qMember_of_qMap_eq_zero ρ b hρ hb Jbar Jinf Sinf hstd δ δT
    hδ hδT χT χN β hχT hχN hβ
  obtain ⟨ε₂, hε₂, hfam⟩ := contDiffOn_qFamily_of_qMap_eq_zero ρ b hρ hb Jbar Jinf Sinf hstd δ δT
    hδ hδT χT χN β hχT hχN hβ
  obtain ⟨ε₃, hε₃, K₁, hK₁, hC1⟩ := exists_norm_fderiv_qMember_le ρ b hρ hb Jbar Jinf Sinf hstd
    δ δT hδ hδT χT χN β hχT hχN hβ
  rw [← pG_eq_qMember] at hreg hC1
  rw [← fam_eq_qFamily] at hfam
  have hC0' : ∀ (y : QDom) (z : ℂ),
      ‖(pLc χT χN β z y).1‖ ≤ K₀ * ‖y‖ * (1 + ‖z‖) ^ (1 + δT / (2 * π)) ∧
      ‖(pLc χT χN β z y).2‖ ≤ K₀ * ‖y‖ * (1 + ‖z‖) ^ (δ / (2 * π)) := by
    intro y z
    have h := hC0 y z
    rw [← pG_eq_qMember] at h
    simpa [pG] using h
  exact glue_core hρ hδ hδT l hK₀ hC0' hε₁ hreg hε₂ hfam hε₃ hK₁ hC1

end QRG

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff ENNReal Real

theorem solution (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) (l : ℕ) :
    ∃ ε₀ > 0, ∀ r > 0, ∀ (γ : ℝ → QDom) (k : QDom), ContDiffOn ℝ ∞ γ (Set.Ioo (-r) r) →
      γ 0 = 0 → HasDerivAt γ k 0 →
      (∀ t ∈ Set.Ioo (-r) r, γ t ∈ ball 0 ε₀ ∧ qMap Jbar χT χN β (γ t) = 0) →
    ∃ r > 0, ∃ G : ℂ × ℝ → ℂ × ℂ, ContDiffOn ℝ l G (Set.univ ×ˢ Set.Ioo (-r) r) ∧
      (∀ z, G (z, 0) = (z, 0)) ∧ (fderiv ℝ G (0, 0) (0, 1)).2 = k.2.1 ∧
      (∀ t ∈ Set.Ioo (-r) r,
        ContDiff ℝ ∞ (fun z => G (z, t)) ∧ (∀ z, (G (z, t)).2 ∈ ball (0 : ℂ) ρ) ∧
        JHolomorphic.IsJHolomorphicOn Jbar Set.univ (fun z => G (z, t)) ∧
        (∃ C β : ℝ, 0 < β ∧ ∀ z, ‖(G (z, t)).1 - z‖ ≤ C * (1 + ‖z‖) ^ (1 - β)) ∧
        (∃ C : ℝ, ∀ z, ‖(G (z, t)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
        ∃ C : ℝ, ∀ z, ∃ Δ : ℂ, (fderiv ℝ G (z, t) (Δ, 1)).1 = 0 ∧
          ‖(fderiv ℝ G (z, t) (Δ, 1)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
      ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r', ∀ z,
        ‖(G (z, t)).1 - z‖ ≤ ε * (1 + ‖z‖) ∧ ‖(G (z, t)).2‖ ≤ ε ∧
        ‖fderiv ℝ (fun z => (G (z, t)).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ ε ∧
        (1 + ‖z‖) * ‖fderiv ℝ (fun z => (G (z, t)).2) z‖ ≤ ε :=
  QRG.exists_jbar_family_of_qMap_curve_aux ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ l
