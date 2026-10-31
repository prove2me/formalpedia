-- Prove2me | solution 1 for FiniteEnergyPlane.halfCyl_exp_decay_of_drift
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T16:12:46.287246+00:00
-- url     : https://prove2.me/submissions/3e7dc256-5e74-4b5f-8bf0-c476f17a65f7

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_halfCyl_exp_decay_of_shift_close
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.MeanValue



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff Real

/-- The smooth reparametrization `ψ(s) = -1/2 + (s + 1/2) φ(2s + 1)`: `ψ = id` on `[0, ∞)`,
`ψ ≥ -1/2`. -/
noncomputable def dePsi (s : ℝ) : ℝ := -(1 / 2) + (s + 1 / 2) * Real.smoothTransition (2 * s + 1)

lemma dePsi_contDiff : ContDiff ℝ ∞ dePsi := by
  unfold dePsi
  have h : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (2 * s + 1)) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  exact contDiff_const.add ((contDiff_id.add contDiff_const).mul h)

lemma dePsi_of_nonneg {s : ℝ} (hs : 0 ≤ s) : dePsi s = s := by
  unfold dePsi
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

lemma dePsi_ge (s : ℝ) : -(1 / 2) ≤ dePsi s := by
  unfold dePsi
  rcases le_or_gt (-(1 / 2)) s with h | h
  · have := mul_nonneg (show (0 : ℝ) ≤ s + 1 / 2 by linarith)
      (Real.smoothTransition.nonneg (2 * s + 1))
    linarith
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
    simp

/-- The reparametrization map `(s, t) ↦ (s₁ + 1 + ψ(s), t)`. -/
noncomputable def dePhi (s₁ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (s₁ + 1 + dePsi p.1, p.2)

lemma dePhi_contDiff (s₁ : ℝ) : ContDiff ℝ ∞ (dePhi s₁) := by
  unfold dePhi
  exact ((contDiff_const.add (dePsi_contDiff.comp contDiff_fst))).prodMk contDiff_snd

lemma dePhi_mem (s₁ : ℝ) (p : ℝ × ℝ) : dePhi s₁ p ∈ Set.Ioi s₁ ×ˢ (Set.univ : Set ℝ) := by
  refine ⟨?_, Set.mem_univ _⟩
  show s₁ < s₁ + 1 + dePsi p.1
  linarith [dePsi_ge p.1]

lemma dePhi_eventuallyEq {F : Type*} (f : ℝ × ℝ → F) (s₁ : ℝ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    (fun q => f (dePhi s₁ q)) =ᶠ[𝓝 p] fun q => f (q + (s₁ + 1, 0)) := by
  have hopen : IsOpen {q : ℝ × ℝ | 0 < q.1} := isOpen_lt continuous_const continuous_fst
  filter_upwards [hopen.mem_nhds hp] with q hq
  congr 1
  simp only [dePhi, dePsi_of_nonneg (le_of_lt hq)]
  ext <;> simp <;> ring

lemma dePhi_shift (s₁ : ℝ) {s : ℝ} (hs : 0 ≤ s) (t : ℝ) : dePhi s₁ (s, t) = (s + s₁ + 1, t) := by
  simp only [dePhi, dePsi_of_nonneg hs]
  ring_nf

/-- derivatives of a reparametrized function at `s > 0` are those of the original at the shift -/
lemma de_iter_shift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ × ℝ → F)
    (s₁ : ℝ) (m : ℕ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    iteratedFDeriv ℝ m (fun q => f (dePhi s₁ q)) (s, t) = iteratedFDeriv ℝ m f (s + s₁ + 1, t) := by
  rw [((dePhi_eventuallyEq f s₁ (p := (s, t)) hs).iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds,
    iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) m ((s₁ + 1, 0) : ℝ × ℝ) (s, t)]
  congr 1
  simp only [Prod.mk_add_mk, add_zero]
  ring_nf

/-- a uniform threshold for finitely many eventual statements -/
lemma de_uniform {ι : Type*} [Fintype ι] (P : ι → ℝ → Prop)
    (h : ∀ i, ∃ s₀ : ℝ, ∀ s ≥ s₀, P i s) : ∃ s₀ : ℝ, ∀ s ≥ s₀, ∀ i, P i s := by
  choose f hf using h
  refine ⟨∑ i, |f i|, fun s hs i => hf i s (le_trans ?_ hs)⟩
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |f i|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ i))

/-- pure `s`-derivatives as derivatives along the line `σ ↦ (σ, t)` -/
lemma de_line (h : ℝ × ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (k : ℕ) (s t : ℝ) :
    iteratedFDeriv ℝ k h (s, t) (fun _ => (1, 0)) = iteratedDeriv k (fun σ => h (σ, t)) s := by
  have hc : ContDiff ℝ ∞ (fun y : ℝ × ℝ => h (y + (0, t))) :=
    hh.comp (contDiff_id.add contDiff_const)
  have hF : (fun σ => h (σ, t)) =
      (fun y : ℝ × ℝ => h (y + (0, t))) ∘ ContinuousLinearMap.inl ℝ ℝ ℝ := by
    funext σ; simp
  rw [iteratedDeriv_eq_iteratedFDeriv, hF,
    ContinuousLinearMap.iteratedFDeriv_comp_right _ hc s (by exact_mod_cast le_top),
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := h)]
  simp

lemma de_abs_line_le (h : ℝ × ℝ → ℝ) (k : ℕ) (x : ℝ × ℝ) :
    |iteratedFDeriv ℝ k h x (fun _ => (1, 0))| ≤ ‖iteratedFDeriv ℝ k h x‖ := by
  have := (iteratedFDeriv ℝ k h x).le_opNorm (fun _ => ((1 : ℝ), (0 : ℝ)))
  simpa using this

lemma de_comp_derivs (f q : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hq : ContDiff ℝ ∞ q) (t s : ℝ) :
    iteratedDeriv 1 (fun σ => f (t + q σ)) s = deriv f (t + q s) * deriv q s ∧
    iteratedDeriv 2 (fun σ => f (t + q σ)) s = deriv (deriv f) (t + q s) * deriv q s * deriv q s +
      deriv f (t + q s) * deriv (deriv q) s := by
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hqd : Differentiable ℝ q := hq.differentiable (by simp)
  have hf'd : Differentiable ℝ (deriv f) :=
    (contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)
  have hq'd : Differentiable ℝ (deriv q) :=
    (contDiff_infty_iff_deriv.mp hq).2.differentiable (by simp)
  have hin : ∀ σ, HasDerivAt (fun σ => t + q σ) (deriv q σ) σ := fun σ =>
    (hqd σ).hasDerivAt.const_add t
  have hd : ∀ σ, HasDerivAt (fun σ => f (t + q σ)) (deriv f (t + q σ) * deriv q σ) σ :=
    fun σ => HasDerivAt.comp (h₂ := f) σ (hfd (t + q σ)).hasDerivAt (hin σ)
  have hD : deriv (fun σ => f (t + q σ)) = fun σ => deriv f (t + q σ) * deriv q σ :=
    funext fun σ => (hd σ).deriv
  constructor
  · rw [iteratedDeriv_one, hD]
  · rw [iteratedDeriv_succ, iteratedDeriv_one, hD]
    have a1 : HasDerivAt (fun σ => deriv f (t + q σ)) (deriv (deriv f) (t + q s) * deriv q s) s :=
      HasDerivAt.comp (h₂ := deriv f) s (hf'd (t + q s)).hasDerivAt (hin s)
    exact (a1.mul (hq'd s).hasDerivAt).deriv

/-- a smooth `1`-periodic real function and its first two derivatives are bounded -/
lemma de_periodic_bounds (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x, |deriv f x| ≤ L ∧ |deriv (deriv f) x| ≤ L := by
  have hf1 : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hf2 : ContDiff ℝ ∞ (deriv (deriv f)) := (contDiff_infty_iff_deriv.mp hf1).2
  have hp1 : Function.Periodic (deriv f) 1 := fun x => by
    rw [← deriv_comp_add_const]; congr 1; funext y; exact hp y
  have hp2 : Function.Periodic (deriv (deriv f)) 1 := fun x => by
    rw [← deriv_comp_add_const]; congr 1; funext y; exact hp1 y
  obtain ⟨B1, hB1⟩ := (hp1.isBounded_of_continuous one_ne_zero hf1.continuous).exists_norm_le
  obtain ⟨B2, hB2⟩ := (hp2.isBounded_of_continuous one_ne_zero hf2.continuous).exists_norm_le
  refine ⟨|B1| + |B2|, by positivity, fun x => ⟨?_, ?_⟩⟩
  · have := hB1 _ ⟨x, rfl⟩
    rw [Real.norm_eq_abs] at this
    linarith [le_abs_self B1, abs_nonneg B2]
  · have := hB2 _ ⟨x, rfl⟩
    rw [Real.norm_eq_abs] at this
    linarith [le_abs_self B2, abs_nonneg B1]

/-- Exponential decay for linear Cauchy–Riemann equations on an end `(s₁, ∞) × ℝ/ℤ`, with a
coefficient asymptotic to a nondegenerate loop along a drifting phase. -/
theorem halfCyl_exp_decay_of_drift_aux {n : ℕ} (s₁ : ℝ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hnd : CauchyRiemannIndex.IsNondegenerate Sinf) (φ : ℝ × ℝ → ℝ)
    (hφs : ∃ s₂ : ℝ, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => φ p - p.2) (Set.Ioi s₂ ×ˢ Set.univ))
    (hφ : ∀ m : ℕ, 1 ≤ m → ∀ η > 0, ∃ s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => φ p - p.2) (s, t)‖ ≤ η)
    (hSas : ∀ i j, TendstoZeroCInfty (fun p : ℝ × ℝ => S p i j - Sinf (φ p) i j))
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : ContDiffOn ℝ ∞ ζ (Set.Ioi s₁ ×ˢ Set.univ))
    (hper : ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t) ∧ ζ (s, t + 1) = ζ (s, t))
    (heq : ∀ s > s₁, ∀ t : ℝ, CauchyRiemannIndex.crOp S ζ (s, t) = 0)
    (hζ0 : TendstoZeroUnif ζ) :
    ∃ δ > 0, ∃ C s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (-(δ * s)) := by
  set ψ : ℝ × ℝ → ℝ := fun p => φ p - p.2 with hψ
  obtain ⟨s₂, hψC⟩ := hφs
  set s₃ := max s₁ s₂ with hs₃
  have hs₁₃ : s₁ ≤ s₃ := le_max_left _ _
  have hs₂₃ : s₂ ≤ s₃ := le_max_right _ _
  have hmem : ∀ p : ℝ × ℝ, s₃ < (dePhi s₃ p).1 := fun p => (dePhi_mem s₃ p).1
  have hsub : ∀ a, s₃ ≤ a → Set.Ioi a ×ˢ (Set.univ : Set ℝ) ⊆ Set.Ioi s₁ ×ˢ Set.univ :=
    fun a ha => Set.prod_mono (Set.Ioi_subset_Ioi (hs₁₃.trans ha)) le_rfl
  have hsub2 : Set.Ioi s₃ ×ˢ (Set.univ : Set ℝ) ⊆ Set.Ioi s₂ ×ˢ Set.univ :=
    Set.prod_mono (Set.Ioi_subset_Ioi hs₂₃) le_rfl
  set S' : ℝ × ℝ → CauchyRiemannIndex.Mat n := fun p => S (dePhi s₃ p) with hS'
  set ζ' : ℝ × ℝ → CauchyRiemannIndex.Vec n := fun p => ζ (dePhi s₃ p) with hζ'
  set ψ' : ℝ × ℝ → ℝ := fun p => ψ (dePhi s₃ p) with hψ'
  have hS'c : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S' p i j) := fun i j =>
    ((hS i j).mono (hsub s₃ le_rfl)).comp_contDiff (dePhi_contDiff s₃) (dePhi_mem s₃)
  have hζ'c : ContDiff ℝ ∞ ζ' :=
    (hζ.mono (hsub s₃ le_rfl)).comp_contDiff (dePhi_contDiff s₃) (dePhi_mem s₃)
  have hψ'c : ContDiff ℝ ∞ ψ' :=
    (hψC.mono hsub2).comp_contDiff (dePhi_contDiff s₃) (dePhi_mem s₃)
  have hgt : ∀ p : ℝ × ℝ, s₁ < (dePhi s₃ p).1 := fun p => lt_of_le_of_lt hs₁₃ (hmem p)
  have hS'per : ∀ s t : ℝ, S' (s, t + 1) = S' (s, t) := fun s t => (hper _ (hgt (s, t)) t).1
  have hζ'per : ∀ s t : ℝ, ζ' (s, t + 1) = ζ' (s, t) := fun s t => (hper _ (hgt (s, t)) t).2
  -- the equation on `s > 0`
  have hsol : IsHalfCylSolution S' ζ' := by
    refine ⟨hζ'c.contDiffOn, hζ'per, fun s hs t => ?_⟩
    have hE := dePhi_eventuallyEq ζ s₃ (p := (s, t)) hs
    have hd : fderiv ℝ ζ' (s, t) = fderiv ℝ ζ ((s, t) + ((s₃ + 1, 0) : ℝ × ℝ)) := by
      rw [hE.fderiv_eq, fderiv_comp_add_right]
    have hpt : (s, t) + ((s₃ + 1, 0) : ℝ × ℝ) = (s + s₃ + 1, t) := by
      simp only [Prod.mk_add_mk, add_zero]; ring_nf
    have h0 := heq (s + s₃ + 1) (by linarith) t
    simp only [CauchyRiemannIndex.crOp, CauchyRiemannIndex.partialS,
      CauchyRiemannIndex.partialT] at h0 ⊢
    rw [hd, hpt]
    have e1 : S' (s, t) = S (s + s₃ + 1, t) := by simp only [hS', dePhi_shift s₃ hs.le]
    have e2 : ζ' (s, t) = ζ (s + s₃ + 1, t) := by simp only [hζ', dePhi_shift s₃ hs.le]
    rw [e1, e2]
    exact h0
  have hζ'0 : TendstoZeroUnif ζ' := by
    intro e he
    obtain ⟨s₄, hs₄⟩ := hζ0 e he
    refine ⟨max (s₄ - s₃ - 1) 0, fun s hs t => ?_⟩
    have hs0 : 0 ≤ s := le_trans (le_max_right _ _) hs
    show ‖ζ (dePhi s₃ (s, t))‖ ≤ e
    rw [dePhi_shift s₃ hs0]
    exact hs₄ _ (by linarith [le_max_left (s₄ - s₃ - 1) 0]) t
  -- bounds on the loop entries
  have hLij : ∀ ij : (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n), ∃ L : ℝ, 0 ≤ L ∧ ∀ x,
      |deriv (fun t => Sinf t ij.1 ij.2) x| ≤ L ∧
      |deriv (deriv (fun t => Sinf t ij.1 ij.2)) x| ≤ L := fun ij =>
    de_periodic_bounds _ (hSinf' ij.1 ij.2) (fun x => by show Sinf (x + 1) ij.1 ij.2 = Sinf x ij.1 ij.2; rw [hSinf.2.1 x])
  choose Lf hLf0 hLf using hLij
  set L : ℝ := ∑ ij, Lf ij with hLd
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun ij _ => hLf0 ij
  have hLle : ∀ ij, Lf ij ≤ L := fun ij =>
    Finset.single_le_sum (f := Lf) (fun ij _ => hLf0 ij) (Finset.mem_univ ij)
  have hfd : ∀ i j, Differentiable ℝ (fun t => Sinf t i j) := fun i j =>
    (hSinf' i j).differentiable (by simp)
  have hLip : ∀ i j (a b : ℝ), |Sinf a i j - Sinf b i j| ≤ L * |a - b| := by
    intro i j a b
    have := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := fun t => Sinf t i j)
      (fun x _ => hfd i j x) (fun x _ => by
        rw [Real.norm_eq_abs]; exact ((hLf (i, j) x).1).trans (hLle (i, j)))
      (Set.mem_univ b) (Set.mem_univ a)
    simpa [Real.norm_eq_abs] using this
  -- the derivative bounds of `ψ` along the reparametrization
  have hψ'd : ∀ m : ℕ, 1 ≤ m → ∀ η > 0, ∃ s₄ : ℝ, ∀ s ≥ s₄, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m ψ' (s, t)‖ ≤ η := by
    intro m hm η hη
    obtain ⟨s₅, hs₅⟩ := hφ m hm η hη
    refine ⟨max (s₅ - s₃ - 1) 1, fun s hs t => ?_⟩
    have hs0 : 0 < s := by linarith [le_max_right (s₅ - s₃ - 1) 1]
    rw [show ψ' = fun q => ψ (dePhi s₃ q) from rfl, de_iter_shift ψ s₃ m hs0 t]
    exact hs₅ _ (by linarith [le_max_left (s₅ - s₃ - 1) 1]) t
  -- closeness to a phase shift
  have hclose : ∀ η > 0, ∃ s₄ : ℝ, ∀ s ≥ s₄, ∃ c : ℝ, ∀ t : ℝ, ∀ i j,
      |S' (s, t) i j - Sinf (t + c) i j| ≤ η := by
    intro η hη
    have hη2 : 0 < η / 2 := half_pos hη
    have hη3 : 0 < η / (2 * (L + 1)) := by positivity
    obtain ⟨sa, hsa⟩ := de_uniform (fun ij : (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) => fun s =>
      ∀ t : ℝ, ‖iteratedFDeriv ℝ 0 (fun p : ℝ × ℝ => S p ij.1 ij.2 - Sinf (φ p) ij.1 ij.2) (s, t)‖
        ≤ η / 2) (fun ij => (hSas ij.1 ij.2).2 0 (η / 2) hη2)
    obtain ⟨sb, hsb⟩ := hφ 1 le_rfl _ hη3
    refine ⟨max (max sa sb - s₃ - 1) 0 + 1, fun s hs => ?_⟩
    have hs0 : 0 ≤ s := by linarith [le_max_right (max sa sb - s₃ - 1) 0]
    set σ := s + s₃ + 1 with hσ
    have hσa : sa ≤ σ := by linarith [le_max_left (max sa sb - s₃ - 1) 0, le_max_left sa sb]
    have hσb : sb < σ := by linarith [le_max_left (max sa sb - s₃ - 1) 0, le_max_right sa sb]
    have hσ1 : s₁ < σ := by linarith
    refine ⟨ψ (σ, 0), fun t i j => ?_⟩
    rw [show S' (s, t) = S (σ, t) by simp only [hS', dePhi_shift s₃ hs0, hσ]]
    -- reduce to `t ∈ [0, 1)`
    have hFp : Function.Periodic (fun t => S (σ, t) i j - Sinf (t + ψ (σ, 0)) i j) 1 := by
      intro x
      show S (σ, x + 1) i j - Sinf (x + 1 + ψ (σ, 0)) i j = S (σ, x) i j - Sinf (x + ψ (σ, 0)) i j
      rw [(hper σ hσ1 x).1, show x + 1 + ψ (σ, 0) = x + ψ (σ, 0) + 1 by ring, hSinf.2.1]
    obtain ⟨y, hy, hyt⟩ := hFp.exists_mem_Ico₀ zero_lt_one t
    rw [hyt]
    have h1 : |S (σ, y) i j - Sinf (φ (σ, y)) i j| ≤ η / 2 := by
      have := hsa σ hσa (i, j) y
      simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using this
    -- `ψ` moves little along the slice
    have hψmv : |ψ (σ, y) - ψ (σ, 0)| ≤ η / (2 * (L + 1)) := by
      have hdiff : ∀ x ∈ Set.Ioi (max sb s₂) ×ˢ (Set.univ : Set ℝ), DifferentiableAt ℝ ψ x :=
        fun x hx => ((hψC.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds
          ⟨lt_of_le_of_lt (le_max_right sb s₂) hx.1, trivial⟩)).differentiableAt (by simp))
      have hbd : ∀ x ∈ Set.Ioi (max sb s₂) ×ˢ (Set.univ : Set ℝ), ‖fderiv ℝ ψ x‖ ≤
          η / (2 * (L + 1)) := by
        rintro ⟨x1, x2⟩ hx
        rw [← norm_iteratedFDeriv_one]
        exact hsb x1 (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx.1)) x2
      have hσm : max sb s₂ < σ := max_lt hσb (by linarith)
      have := ((convex_Ioi (max sb s₂)).prod convex_univ).norm_image_sub_le_of_norm_fderiv_le
        hdiff hbd (show ((σ, 0) : ℝ × ℝ) ∈ Set.Ioi (max sb s₂) ×ˢ Set.univ from ⟨hσm, trivial⟩)
        (show ((σ, y) : ℝ × ℝ) ∈ Set.Ioi (max sb s₂) ×ˢ Set.univ from ⟨hσm, trivial⟩)
      have hn : ‖((σ, y) : ℝ × ℝ) - (σ, 0)‖ ≤ 1 := by
        rw [Prod.mk_sub_mk, sub_self, sub_zero, Prod.norm_def]
        simp only [norm_zero, Real.norm_eq_abs]
        rw [max_le_iff]
        exact ⟨zero_le_one, by rw [abs_of_nonneg hy.1]; exact hy.2.le⟩
      rw [Real.norm_eq_abs] at this
      calc |ψ (σ, y) - ψ (σ, 0)| ≤ η / (2 * (L + 1)) * ‖((σ, y) : ℝ × ℝ) - (σ, 0)‖ := this
        _ ≤ η / (2 * (L + 1)) * 1 := mul_le_mul_of_nonneg_left hn hη3.le
        _ = η / (2 * (L + 1)) := mul_one _
    have hφy : φ (σ, y) = y + ψ (σ, y) := by simp only [hψ]; ring
    have h2 : |Sinf (φ (σ, y)) i j - Sinf (y + ψ (σ, 0)) i j| ≤ η / 2 := by
      refine (hLip i j _ _).trans ?_
      rw [hφy, show y + ψ (σ, y) - (y + ψ (σ, 0)) = ψ (σ, y) - ψ (σ, 0) by ring]
      calc L * |ψ (σ, y) - ψ (σ, 0)| ≤ L * (η / (2 * (L + 1))) :=
            mul_le_mul_of_nonneg_left hψmv hL0
        _ ≤ η / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    calc |S (σ, y) i j - Sinf (y + ψ (σ, 0)) i j|
        = |(S (σ, y) i j - Sinf (φ (σ, y)) i j) + (Sinf (φ (σ, y)) i j - Sinf (y + ψ (σ, 0)) i j)| := by
          ring_nf
      _ ≤ η / 2 + η / 2 := (abs_add_le _ _).trans (add_le_add h1 h2)
      _ = η := by ring
  -- small `s`-derivatives
  have hds : ∀ η > 0, ∃ s₄ : ℝ, ∀ s ≥ s₄, ∀ t : ℝ, ∀ i j,
      |iteratedFDeriv ℝ 1 (fun p => S' p i j) (s, t) (fun _ => (1, 0))| ≤ η ∧
      |iteratedFDeriv ℝ 2 (fun p => S' p i j) (s, t) (fun _ => (1, 0))| ≤ η := by
    intro η hη
    set e : ℝ := min 1 (η / (2 * (2 * L + 1))) with he
    have he0 : 0 < e := lt_min one_pos (by positivity)
    have he1 : e ≤ 1 := min_le_left _ _
    have heL : (2 * L + 1) * e ≤ η / 2 := by
      have : e ≤ η / (2 * (2 * L + 1)) := min_le_right _ _
      calc (2 * L + 1) * e ≤ (2 * L + 1) * (η / (2 * (2 * L + 1))) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = η / 2 := by field_simp
    obtain ⟨sa, hsa⟩ := de_uniform (fun ij : (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) => fun s =>
      ∀ t : ℝ, ‖iteratedFDeriv ℝ 1 (fun p : ℝ × ℝ => S p ij.1 ij.2 - Sinf (φ p) ij.1 ij.2) (s, t)‖
        ≤ η / 2 ∧
        ‖iteratedFDeriv ℝ 2 (fun p : ℝ × ℝ => S p ij.1 ij.2 - Sinf (φ p) ij.1 ij.2) (s, t)‖
        ≤ η / 2) (fun ij => by
          obtain ⟨a1, ha1⟩ := (hSas ij.1 ij.2).2 1 (η / 2) (half_pos hη)
          obtain ⟨a2, ha2⟩ := (hSas ij.1 ij.2).2 2 (η / 2) (half_pos hη)
          exact ⟨max a1 a2, fun s hs t =>
            ⟨ha1 s (le_trans (le_max_left _ _) hs) t, ha2 s (le_trans (le_max_right _ _) hs) t⟩⟩)
    obtain ⟨sb1, hsb1⟩ := hψ'd 1 le_rfl e he0
    obtain ⟨sb2, hsb2⟩ := hψ'd 2 (by norm_num) e he0
    refine ⟨max (max (sa - s₃ - 1) 1) (max sb1 sb2), fun s hs t i j => ?_⟩
    have hm1 := le_max_right (sa - s₃ - 1) 1
    have hm2 := le_max_left (sa - s₃ - 1) 1
    have hm3 := le_max_left (max (sa - s₃ - 1) 1) (max sb1 sb2)
    have hs0 : 0 < s := by linarith
    have hsa' : sa ≤ s + s₃ + 1 := by linarith
    have hsb1' : sb1 ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
    have hsb2' : sb2 ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs
    set f : ℝ → ℝ := fun x => Sinf x i j with hf
    set g' : ℝ × ℝ → ℝ := fun p => f (p.2 + ψ' p) with hg'
    set D' : ℝ × ℝ → ℝ := fun p => S' p i j - g' p with hD'
    have hg'c : ContDiff ℝ ∞ g' := (hSinf' i j).comp (contDiff_snd.add hψ'c)
    have hD'c : ContDiff ℝ ∞ D' := (hS'c i j).sub hg'c
    have hsplit : (fun p => S' p i j) = D' + g' := by
      funext p; simp only [hD', Pi.add_apply, sub_add_cancel]
    -- `D'` is the reparametrized remainder
    have hD'eq : D' = fun q => (fun p : ℝ × ℝ => S p i j - Sinf (φ p) i j) (dePhi s₃ q) := by
      funext q
      simp only [hD', hg', hf, hS', hψ', hψ, dePhi]
      ring_nf
    have hDk : ∀ k, k = 1 ∨ k = 2 → |iteratedFDeriv ℝ k D' (s, t) (fun _ => (1, 0))| ≤ η / 2 := by
      intro k hk
      refine (de_abs_line_le D' k (s, t)).trans ?_
      rw [hD'eq, de_iter_shift (fun p : ℝ × ℝ => S p i j - Sinf (φ p) i j) s₃ k hs0 t]
      rcases hk with rfl | rfl
      · exact (hsa _ hsa' (i, j) t).1
      · exact (hsa _ hsa' (i, j) t).2
    -- the phase part along the line
    set q : ℝ → ℝ := fun σ => ψ' (σ, t) with hq
    have hqc : ContDiff ℝ ∞ q := hψ'c.comp (contDiff_id.prodMk contDiff_const)
    have hline : (fun σ => g' (σ, t)) = fun σ => f (t + q σ) := rfl
    obtain ⟨hG1, hG2⟩ := de_comp_derivs f q (hSinf' i j) hqc t s
    have hq1 : |deriv q s| ≤ e := by
      have := de_line ψ' hψ'c 1 s t
      rw [iteratedDeriv_one] at this
      rw [show deriv q s = _ from this.symm]
      exact (de_abs_line_le ψ' 1 (s, t)).trans (hsb1 s hsb1' t)
    have hq2 : |deriv (deriv q) s| ≤ e := by
      have := de_line ψ' hψ'c 2 s t
      rw [iteratedDeriv_succ, iteratedDeriv_one] at this
      rw [show deriv (deriv q) s = _ from this.symm]
      exact (de_abs_line_le ψ' 2 (s, t)).trans (hsb2 s hsb2' t)
    have hL1 := (hLf (i, j) (t + q s)).1
    have hL2 := (hLf (i, j) (t + q s)).2
    have hdf1 : |deriv f (t + q s)| ≤ L := hL1.trans (hLle (i, j))
    have hdf2 : |deriv (deriv f) (t + q s)| ≤ L := hL2.trans (hLle (i, j))
    have hgk : ∀ k, k = 1 ∨ k = 2 → |iteratedFDeriv ℝ k g' (s, t) (fun _ => (1, 0))| ≤ η / 2 := by
      intro k hk
      rw [de_line g' hg'c k s t, hline]
      have hq1' : |deriv q s| ≤ 1 := hq1.trans he1
      rcases hk with rfl | rfl
      · rw [hG1, abs_mul]
        calc |deriv f (t + q s)| * |deriv q s| ≤ L * e :=
              mul_le_mul hdf1 hq1 (abs_nonneg _) hL0
          _ ≤ (2 * L + 1) * e := by nlinarith
          _ ≤ η / 2 := heL
      · rw [hG2]
        calc |deriv (deriv f) (t + q s) * deriv q s * deriv q s + deriv f (t + q s) * deriv (deriv q) s|
            ≤ |deriv (deriv f) (t + q s)| * |deriv q s| * |deriv q s| +
                |deriv f (t + q s)| * |deriv (deriv q) s| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_mul, abs_mul]
          _ ≤ L * e * 1 + L * e := by
              gcongr
          _ ≤ (2 * L + 1) * e := by nlinarith
          _ ≤ η / 2 := heL
    have hsum : ∀ k, k = 1 ∨ k = 2 →
        |iteratedFDeriv ℝ k (fun p => S' p i j) (s, t) (fun _ => (1, 0))| ≤ η := by
      intro k hk
      rw [hsplit, iteratedFDeriv_add_apply (hD'c.contDiffAt.of_le (by exact_mod_cast le_top))
        (hg'c.contDiffAt.of_le (by exact_mod_cast le_top)), ContinuousMultilinearMap.add_apply]
      calc _ ≤ |iteratedFDeriv ℝ k D' (s, t) (fun _ => (1, 0))| +
            |iteratedFDeriv ℝ k g' (s, t) (fun _ => (1, 0))| := abs_add_le _ _
        _ ≤ η / 2 + η / 2 := add_le_add (hDk k hk) (hgk k hk)
        _ = η := by ring
    exact ⟨hsum 1 (Or.inl rfl), hsum 2 (Or.inr rfl)⟩
  obtain ⟨δ, hδ, C, hC⟩ := halfCyl_exp_decay_of_shift_close S' hS'c hS'per Sinf hSinf hnd
    hclose hds ζ' hsol hζ'0
  refine ⟨δ, hδ, C * Real.exp (δ * (s₃ + 1)), s₃ + 2, fun s hs t => ?_⟩
  have h1 := hC (s - s₃ - 1) (by linarith) t
  have e : ζ' (s - s₃ - 1, t) = ζ (s, t) := by
    simp only [hζ', dePhi_shift s₃ (show 0 ≤ s - s₃ - 1 by linarith)]
    ring_nf
  rw [e] at h1
  calc ‖ζ (s, t)‖ ≤ C * Real.exp (-(δ * (s - s₃ - 1))) := h1
    _ = C * Real.exp (δ * (s₃ + 1)) * Real.exp (-(δ * s)) := by
      rw [mul_assoc, ← Real.exp_add]; ring_nf

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (s₁ : ℝ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hnd : CauchyRiemannIndex.IsNondegenerate Sinf) (φ : ℝ × ℝ → ℝ)
    (hφs : ∃ s₂ : ℝ, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => φ p - p.2) (Set.Ioi s₂ ×ˢ Set.univ))
    (hφ : ∀ m : ℕ, 1 ≤ m → ∀ η > 0, ∃ s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => φ p - p.2) (s, t)‖ ≤ η)
    (hSas : ∀ i j, TendstoZeroCInfty (fun p : ℝ × ℝ => S p i j - Sinf (φ p) i j))
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : ContDiffOn ℝ ∞ ζ (Set.Ioi s₁ ×ˢ Set.univ))
    (hper : ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t) ∧ ζ (s, t + 1) = ζ (s, t))
    (heq : ∀ s > s₁, ∀ t : ℝ, CauchyRiemannIndex.crOp S ζ (s, t) = 0)
    (hζ0 : TendstoZeroUnif ζ) :
    ∃ δ > 0, ∃ C s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (-(δ * s)) :=
  halfCyl_exp_decay_of_drift_aux s₁ S hS Sinf hSinf hSinf' hnd φ hφs hφ hSas ζ hζ hper heq hζ0
