-- Prove2me | solution 1 for FiniteEnergyPlane.halfCyl_asymptotic_formula_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T09:43:13.042677+00:00
-- url     : https://prove2.me/submissions/9e853c1e-fb65-443c-bcc6-37f864c493d8

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_halfCyl_asymptotic_formula
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff Real

/-- The smooth reparametrization `ψ(s) = -1/2 + (s + 1/2) φ(2s + 1)`: `ψ = id` on `[0, ∞)`,
`ψ ≥ -1/2`. -/
noncomputable def afePsi (s : ℝ) : ℝ := -(1 / 2) + (s + 1 / 2) * Real.smoothTransition (2 * s + 1)

lemma afePsi_contDiff : ContDiff ℝ ∞ afePsi := by
  unfold afePsi
  have h : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (2 * s + 1)) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  exact contDiff_const.add ((contDiff_id.add contDiff_const).mul h)

lemma afePsi_of_nonneg {s : ℝ} (hs : 0 ≤ s) : afePsi s = s := by
  unfold afePsi
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

lemma afePsi_ge (s : ℝ) : -(1 / 2) ≤ afePsi s := by
  unfold afePsi
  rcases le_or_gt (-(1 / 2)) s with h | h
  · have := mul_nonneg (show (0 : ℝ) ≤ s + 1 / 2 by linarith)
      (Real.smoothTransition.nonneg (2 * s + 1))
    linarith
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
    simp

/-- The reparametrization map `(s, t) ↦ (s₁ + 1 + ψ(s), t)`. -/
noncomputable def afePhi (s₁ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (s₁ + 1 + afePsi p.1, p.2)

lemma afePhi_contDiff (s₁ : ℝ) : ContDiff ℝ ∞ (afePhi s₁) := by
  unfold afePhi
  exact ((contDiff_const.add (afePsi_contDiff.comp contDiff_fst))).prodMk contDiff_snd

lemma afePhi_mem (s₁ : ℝ) (p : ℝ × ℝ) : afePhi s₁ p ∈ Set.Ioi s₁ ×ˢ (Set.univ : Set ℝ) := by
  refine ⟨?_, Set.mem_univ _⟩
  show s₁ < s₁ + 1 + afePsi p.1
  linarith [afePsi_ge p.1]

lemma afePhi_eventuallyEq {F : Type*} (f : ℝ × ℝ → F) (s₁ : ℝ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    (fun q => f (afePhi s₁ q)) =ᶠ[𝓝 p] fun q => f (q + (s₁ + 1, 0)) := by
  have hopen : IsOpen {q : ℝ × ℝ | 0 < q.1} := isOpen_lt continuous_const continuous_fst
  filter_upwards [hopen.mem_nhds hp] with q hq
  congr 1
  simp only [afePhi, afePsi_of_nonneg (le_of_lt hq)]
  ext <;> simp <;> ring

theorem halfCyl_asymptotic_formula_eventually_aux {n : ℕ} (s₁ : ℝ)
    (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : ContDiffOn ℝ ∞ ζ (Set.Ioi s₁ ×ˢ Set.univ))
    (hper : ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t) ∧ ζ (s, t + 1) = ζ (s, t))
    (heq : ∀ s > s₁, ∀ t : ℝ, CauchyRiemannIndex.crOp S ζ (s, t) = 0)
    (hne : ∀ s₀ : ℝ, ∃ s ≥ s₀, ∃ t : ℝ, ζ (s, t) ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > s₁, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ ∃ e : ℝ → CauchyRiemannIndex.Vec n, IsLoopEigen Sinf μ e ∧
      TendstoZeroCInfty (fun p : ℝ × ℝ => Real.exp (-(μ * p.1)) • ζ p - e p.2) := by
  set v : ℝ × ℝ := (s₁ + 1, 0) with hv
  set S' : ℝ × ℝ → CauchyRiemannIndex.Mat n := fun p => S (afePhi s₁ p) with hS'
  set ζ' : ℝ × ℝ → CauchyRiemannIndex.Vec n := fun p => ζ (afePhi s₁ p) with hζ'
  have hS'c : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S' p i j) := fun i j =>
    (hS i j).comp_contDiff (afePhi_contDiff s₁) (afePhi_mem s₁)
  have hζ'c : ContDiff ℝ ∞ ζ' := hζ.comp_contDiff (afePhi_contDiff s₁) (afePhi_mem s₁)
  have hmem : ∀ p : ℝ × ℝ, s₁ < (afePhi s₁ p).1 := fun p => (afePhi_mem s₁ p).1
  have hS'per : ∀ s t : ℝ, S' (s, t + 1) = S' (s, t) := fun s t =>
    (hper _ (hmem (s, t)) t).1
  have hζ'per : ∀ s t : ℝ, ζ' (s, t + 1) = ζ' (s, t) := fun s t =>
    (hper _ (hmem (s, t)) t).2
  have hshift : ∀ {s : ℝ}, 0 ≤ s → ∀ t : ℝ, afePhi s₁ (s, t) = (s + s₁ + 1, t) := by
    intro s hs t
    simp only [afePhi, afePsi_of_nonneg hs]
    ring_nf
  -- the equation on `s > 0`
  have hsol : IsHalfCylSolution S' ζ' := by
    refine ⟨hζ'c.contDiffOn, hζ'per, fun s hs t => ?_⟩
    have hE := afePhi_eventuallyEq ζ s₁ (p := (s, t)) hs
    have hd : fderiv ℝ ζ' (s, t) = fderiv ℝ ζ ((s, t) + v) := by
      rw [hE.fderiv_eq, fderiv_comp_add_right]
    have hpt : (s, t) + v = (s + s₁ + 1, t) := by
      simp only [hv, Prod.mk_add_mk, add_zero]; ring_nf
    have h0 := heq (s + s₁ + 1) (by linarith) t
    simp only [CauchyRiemannIndex.crOp, CauchyRiemannIndex.partialS,
      CauchyRiemannIndex.partialT] at h0 ⊢
    rw [hd, hpt]
    have e1 : S' (s, t) = S (s + s₁ + 1, t) := by simp only [hS', hshift hs.le]
    have e2 : ζ' (s, t) = ζ (s + s₁ + 1, t) := by simp only [hζ', hshift hs.le]
    rw [e1, e2]
    exact h0
  -- exponential convergence of the reparametrized coefficient
  have hSas' : IsExpAsymptoticTo S' Sinf d := by
    intro i j
    obtain ⟨-, hdd⟩ := hSas i j
    refine ⟨⟨0, ((hS'c i j).sub ((hSinf' i j).comp contDiff_snd)).contDiffOn⟩, fun m => ?_⟩
    obtain ⟨C₃, s₃, hs₃⟩ := hdd m
    refine ⟨C₃ * Real.exp (-(d * (s₁ + 1))), max (s₃ - s₁ - 1) 1, fun s hs t => ?_⟩
    have hs0 : 0 < s := by linarith [le_max_right (s₃ - s₁ - 1) 1]
    have hE : (fun p : ℝ × ℝ => S' p i j - Sinf p.2 i j) =ᶠ[𝓝 (s, t)]
        fun p => (fun q : ℝ × ℝ => S q i j - Sinf q.2 i j) (p + v) := by
      filter_upwards [afePhi_eventuallyEq S s₁ (p := (s, t)) hs0] with q hq
      simp only [hS'] at hq ⊢
      rw [hq]
      simp [hv]
    rw [(hE.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds,
      iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun q : ℝ × ℝ => S q i j - Sinf q.2 i j) m v
        (s, t)]
    have hpt : (s, t) + v = (s + s₁ + 1, t) := by
      simp only [hv, Prod.mk_add_mk, add_zero]; ring_nf
    rw [hpt]
    refine (hs₃ _ (by linarith [le_max_left (s₃ - s₁ - 1) 1]) t).trans (le_of_eq ?_)
    rw [mul_assoc, ← Real.exp_add]; ring_nf
  -- nonvanishing and growth of the reparametrized solution
  have hne' : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ' p ≠ 0 := by
    obtain ⟨s, hs, t, ht⟩ := hne (s₁ + 2)
    refine ⟨(s - s₁ - 1, t), by simp only; linarith, ?_⟩
    simp only [hζ', hshift (show 0 ≤ s - s₁ - 1 by linarith)]
    rw [show s - s₁ - 1 + s₁ + 1 = s by ring]
    exact ht
  have hgrowth' : ∀ s > 0, ∀ t : ℝ,
      ‖ζ' (s, t)‖ ≤ (C * Real.exp (δ₀ * (s₁ + 1))) * Real.exp (δ₀ * s) := by
    intro s hs t
    simp only [hζ', hshift hs.le]
    refine (hgrowth _ (by linarith) t).trans (le_of_eq ?_)
    rw [mul_assoc, ← Real.exp_add]; ring_nf
  obtain ⟨μ, hμ, e, he, hconv⟩ := halfCyl_asymptotic_formula S' hS'c hS'per Sinf hSinf hSinf' d hd
    hSas' ζ' hsol hne' _ δ₀ hgrowth'
  obtain ⟨heC, heP, ⟨t₀, het₀⟩, heE⟩ := he
  set κ : ℝ := Real.exp (-(μ * (s₁ + 1))) with hκ
  have hκ0 : κ ≠ 0 := (Real.exp_pos _).ne'
  refine ⟨μ, hμ, κ • e, ⟨heC.const_smul κ, fun t => by simp [heP t], ⟨t₀, smul_ne_zero hκ0 het₀⟩,
    fun t => ?_⟩, ?_⟩
  · have hd' : deriv (κ • e) t = κ • deriv e t :=
      deriv_const_smul κ (heC.differentiable (by simp) t)
    rw [hd']
    simp only [Pi.smul_apply, map_smul]
    rw [smul_comm μ κ, ← heE t, smul_sub, smul_neg]
  -- convergence for the original solution
  set F : ℝ × ℝ → CauchyRiemannIndex.Vec n := fun p => Real.exp (-(μ * p.1)) • ζ' p - e p.2 with hF
  have hexpc : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.exp (-(μ * p.1))) :=
    Real.contDiff_exp.comp ((contDiff_const.mul contDiff_fst).neg)
  have hFc : ContDiff ℝ ∞ F := (hexpc.smul hζ'c).sub (heC.comp contDiff_snd)
  have hU : IsOpen (Set.Ioi (s₁ + 1) ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hloc : ∀ p : ℝ × ℝ, s₁ + 1 < p.1 →
      (fun q : ℝ × ℝ => Real.exp (-(μ * q.1)) • ζ q - (κ • e) q.2) =ᶠ[𝓝 p]
        fun q => κ • F (q + (-v)) := by
    intro p hp
    filter_upwards [hU.mem_nhds ⟨hp, Set.mem_univ _⟩] with q hq
    obtain ⟨a, b⟩ := q
    have ha : s₁ + 1 < a := hq.1
    have hq' : (a, b) + -v = (a - s₁ - 1, b) := by
      simp only [hv, Prod.neg_mk, neg_zero, Prod.mk_add_mk, add_zero]; ring_nf
    have hq'' : afePhi s₁ (a - s₁ - 1, b) = (a, b) := by
      rw [hshift (by linarith : (0 : ℝ) ≤ a - s₁ - 1)]
      congr 1; ring
    simp only [hF, hζ', hq', hq'', Pi.smul_apply, smul_sub, smul_smul]
    congr 2
    rw [hκ, ← Real.exp_add]
    ring_nf
  refine ⟨⟨s₁ + 1, ?_⟩, fun m e' he' => ?_⟩
  · intro p hp
    exact ((hFc.comp (contDiff_id.add contDiff_const)).const_smul κ).contDiffAt.congr_of_eventuallyEq
      (hloc p hp.1) |>.contDiffWithinAt
  obtain ⟨-, hFd⟩ := hconv
  obtain ⟨s₃, hs₃⟩ := hFd m (e' / (|κ| + 1)) (by positivity)
  refine ⟨max (s₃ + s₁ + 1) (s₁ + 2), fun s hs t => ?_⟩
  have hs1 : s₁ + 1 < s := by linarith [le_max_right (s₃ + s₁ + 1) (s₁ + 2)]
  have hFeq : F = fun p : ℝ × ℝ => Real.exp (-(μ * p.1)) • ζ' p - e p.2 := rfl
  rw [((hloc (s, t) hs1).iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds,
    iteratedFDeriv_const_smul_apply' (by
      have hc : ContDiff ℝ ∞ (fun q : ℝ × ℝ => F (q + -v)) :=
        hFc.comp (contDiff_id.add contDiff_const)
      exact hc.contDiffAt.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := F) m (-v) (s, t), norm_smul]
  have hpt : (s, t) + -v = (s - s₁ - 1, t) := by
    simp only [hv, Prod.neg_mk, neg_zero, Prod.mk_add_mk, add_zero]; ring_nf
  rw [hpt]
  have h1 := hs₃ (s - s₁ - 1) (by linarith [le_max_left (s₃ + s₁ + 1) (s₁ + 2)]) t
  have hk : ‖κ‖ * ‖iteratedFDeriv ℝ m F (s - s₁ - 1, t)‖ ≤ ‖κ‖ * (e' / (|κ| + 1)) :=
    mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  have hk2 : ‖κ‖ * (e' / (|κ| + 1)) ≤ e' := by
    rw [Real.norm_eq_abs, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg κ]
  linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (s₁ : ℝ)
    (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : ContDiffOn ℝ ∞ ζ (Set.Ioi s₁ ×ˢ Set.univ))
    (hper : ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t) ∧ ζ (s, t + 1) = ζ (s, t))
    (heq : ∀ s > s₁, ∀ t : ℝ, CauchyRiemannIndex.crOp S ζ (s, t) = 0)
    (hne : ∀ s₀ : ℝ, ∃ s ≥ s₀, ∃ t : ℝ, ζ (s, t) ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > s₁, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ ∃ e : ℝ → CauchyRiemannIndex.Vec n, IsLoopEigen Sinf μ e ∧
      TendstoZeroCInfty (fun p : ℝ × ℝ => Real.exp (-(μ * p.1)) • ζ p - e p.2) :=
  halfCyl_asymptotic_formula_eventually_aux s₁ S hS Sinf hSinf hSinf' d hd hSas ζ hζ hper heq hne C δ₀ hgrowth
