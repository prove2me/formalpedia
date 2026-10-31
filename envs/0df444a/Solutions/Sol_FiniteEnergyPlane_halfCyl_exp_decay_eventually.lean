-- Prove2me | solution 1 for FiniteEnergyPlane.halfCyl_exp_decay_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T09:33:01.97127+00:00
-- url     : https://prove2.me/submissions/db6a170c-96ef-4931-8830-854861e973e6

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_halfCyl_exp_decay
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The smooth reparametrization `ψ(s) = -1/2 + (s + 1/2) φ(2s + 1)`: `ψ = id` on `[0, ∞)`,
`ψ ≥ -1/2`. -/
noncomputable def knPsi (s : ℝ) : ℝ := -(1 / 2) + (s + 1 / 2) * Real.smoothTransition (2 * s + 1)

lemma knPsi_contDiff : ContDiff ℝ ∞ knPsi := by
  unfold knPsi
  have h : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (2 * s + 1)) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  exact contDiff_const.add ((contDiff_id.add contDiff_const).mul h)

lemma knPsi_of_nonneg {s : ℝ} (hs : 0 ≤ s) : knPsi s = s := by
  unfold knPsi
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

lemma knPsi_ge (s : ℝ) : -(1 / 2) ≤ knPsi s := by
  unfold knPsi
  rcases le_or_gt (-(1 / 2)) s with h | h
  · have := mul_nonneg (show (0 : ℝ) ≤ s + 1 / 2 by linarith)
      (Real.smoothTransition.nonneg (2 * s + 1))
    linarith
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
    simp

/-- The reparametrization map `(s, t) ↦ (s₁ + 1 + ψ(s), t)`. -/
noncomputable def knPhi (s₁ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (s₁ + 1 + knPsi p.1, p.2)

lemma knPhi_contDiff (s₁ : ℝ) : ContDiff ℝ ∞ (knPhi s₁) := by
  unfold knPhi
  exact ((contDiff_const.add (knPsi_contDiff.comp contDiff_fst))).prodMk contDiff_snd

lemma knPhi_mem (s₁ : ℝ) (p : ℝ × ℝ) : knPhi s₁ p ∈ Set.Ioi s₁ ×ˢ (Set.univ : Set ℝ) := by
  refine ⟨?_, Set.mem_univ _⟩
  show s₁ < s₁ + 1 + knPsi p.1
  linarith [knPsi_ge p.1]

/-- Near a point with `s > 0`, `f ∘ knPhi s₁` is the translate of `f` by `(s₁ + 1, 0)`. -/
lemma knPhi_eventuallyEq {F : Type*} (f : ℝ × ℝ → F) (s₁ : ℝ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    (fun q => f (knPhi s₁ q)) =ᶠ[𝓝 p] fun q => f (q + (s₁ + 1, 0)) := by
  have hopen : IsOpen {q : ℝ × ℝ | 0 < q.1} := isOpen_lt continuous_const continuous_fst
  filter_upwards [hopen.mem_nhds hp] with q hq
  congr 1
  simp only [knPhi, knPsi_of_nonneg (le_of_lt hq)]
  ext <;> simp <;> ring

theorem halfCyl_exp_decay_eventually_aux {n : ℕ} (s₁ : ℝ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : IsCInftyAsymptoticTo S Sinf) (hnd : CauchyRiemannIndex.IsNondegenerate Sinf)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : ContDiffOn ℝ ∞ ζ (Set.Ioi s₁ ×ˢ Set.univ))
    (hper : ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t) ∧ ζ (s, t + 1) = ζ (s, t))
    (heq : ∀ s > s₁, ∀ t : ℝ, CauchyRiemannIndex.crOp S ζ (s, t) = 0)
    (hζ0 : TendstoZeroUnif ζ) :
    ∃ δ > 0, ∃ C s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (-(δ * s)) := by
  set v : ℝ × ℝ := (s₁ + 1, 0) with hv
  set S' : ℝ × ℝ → CauchyRiemannIndex.Mat n := fun p => S (knPhi s₁ p) with hS'
  set ζ' : ℝ × ℝ → CauchyRiemannIndex.Vec n := fun p => ζ (knPhi s₁ p) with hζ'
  have hS'c : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S' p i j) := fun i j =>
    (hS i j).comp_contDiff (knPhi_contDiff s₁) (knPhi_mem s₁)
  have hζ'c : ContDiff ℝ ∞ ζ' := hζ.comp_contDiff (knPhi_contDiff s₁) (knPhi_mem s₁)
  have hmem : ∀ p : ℝ × ℝ, s₁ < (knPhi s₁ p).1 := fun p => (knPhi_mem s₁ p).1
  have hS'per : ∀ s t : ℝ, S' (s, t + 1) = S' (s, t) := fun s t =>
    (hper _ (hmem (s, t)) t).1
  have hζ'per : ∀ s t : ℝ, ζ' (s, t + 1) = ζ' (s, t) := fun s t =>
    (hper _ (hmem (s, t)) t).2
  have hshift : ∀ {s : ℝ}, 0 ≤ s → ∀ t : ℝ, knPhi s₁ (s, t) = (s + s₁ + 1, t) := by
    intro s hs t
    simp only [knPhi, knPsi_of_nonneg hs]
    ring_nf
  -- the equation on `s > 0`
  have hsol : IsHalfCylSolution S' ζ' := by
    refine ⟨hζ'c.contDiffOn, hζ'per, fun s hs t => ?_⟩
    have hE := knPhi_eventuallyEq ζ s₁ (p := (s, t)) hs
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
  -- `C^∞` convergence of the reparametrized coefficient
  have hSas' : IsCInftyAsymptoticTo S' Sinf := by
    intro i j
    obtain ⟨-, hd⟩ := hSas i j
    refine ⟨⟨0, ((hS'c i j).sub ((hSinf' i j).comp contDiff_snd)).contDiffOn⟩, fun m e he => ?_⟩
    obtain ⟨s₃, hs₃⟩ := hd m e he
    refine ⟨max (s₃ - s₁ - 1) 1, fun s hs t => ?_⟩
    have hs0 : 0 < s := by linarith [le_max_right (s₃ - s₁ - 1) 1]
    have hE : (fun p : ℝ × ℝ => S' p i j - Sinf p.2 i j) =ᶠ[𝓝 (s, t)]
        fun p => (fun q : ℝ × ℝ => S q i j - Sinf q.2 i j) (p + v) := by
      filter_upwards [knPhi_eventuallyEq S s₁ (p := (s, t)) hs0] with q hq
      simp only [hS'] at hq ⊢
      rw [hq]
      simp [hv]
    rw [(hE.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds,
      iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun q : ℝ × ℝ => S q i j - Sinf q.2 i j) m v (s, t)]
    have hpt : (s, t) + v = (s + s₁ + 1, t) := by
      simp only [hv, Prod.mk_add_mk, add_zero]; ring_nf
    rw [hpt]
    exact hs₃ _ (by linarith [le_max_left (s₃ - s₁ - 1) 1]) t
  -- uniform convergence of the reparametrized solution
  have hζ'0 : TendstoZeroUnif ζ' := by
    intro e he
    obtain ⟨s₃, hs₃⟩ := hζ0 e he
    refine ⟨max (s₃ - s₁ - 1) 0, fun s hs t => ?_⟩
    have hs0 : 0 ≤ s := le_trans (le_max_right _ _) hs
    show ‖ζ (knPhi s₁ (s, t))‖ ≤ e
    rw [hshift hs0]
    exact hs₃ _ (by linarith [le_max_left (s₃ - s₁ - 1) 0]) t
  obtain ⟨δ, hδ, C, hC⟩ :=
    halfCyl_exp_decay S' hS'c hS'per Sinf hSinf hSinf' hSas' hnd ζ' hsol hζ'0
  refine ⟨δ, hδ, C * Real.exp (δ * (s₁ + 1)), s₁ + 2, fun s hs t => ?_⟩
  have h1 := hC (s - s₁ - 1) (by linarith) t
  have e : ζ' (s - s₁ - 1, t) = ζ (s, t) := by
    simp only [hζ', hshift (show 0 ≤ s - s₁ - 1 by linarith)]
    ring_nf
  rw [e] at h1
  calc ‖ζ (s, t)‖ ≤ C * Real.exp (-(δ * (s - s₁ - 1))) := h1
    _ = C * Real.exp (δ * (s₁ + 1)) * Real.exp (-(δ * s)) := by
      rw [mul_assoc, ← Real.exp_add]; ring_nf

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (s₁ : ℝ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : IsCInftyAsymptoticTo S Sinf) (hnd : CauchyRiemannIndex.IsNondegenerate Sinf)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : ContDiffOn ℝ ∞ ζ (Set.Ioi s₁ ×ˢ Set.univ))
    (hper : ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t) ∧ ζ (s, t + 1) = ζ (s, t))
    (heq : ∀ s > s₁, ∀ t : ℝ, CauchyRiemannIndex.crOp S ζ (s, t) = 0)
    (hζ0 : TendstoZeroUnif ζ) :
    ∃ δ > 0, ∃ C s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (-(δ * s)) :=
  halfCyl_exp_decay_eventually_aux s₁ S hS Sinf hSinf hSinf' hSas hnd ζ hζ hper heq hζ0
