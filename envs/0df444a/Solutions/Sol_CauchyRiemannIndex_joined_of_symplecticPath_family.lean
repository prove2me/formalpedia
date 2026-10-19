-- Prove2me | solution 1 for CauchyRiemannIndex.joined_of_symplecticPath_family
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T13:31:07.097806+00:00
-- url     : https://prove2.me/submissions/1352e525-c000-4ce4-93d6-9b3894806174

import Definitions.Def_CauchyRiemannIndex_Setting
import Theorems.Thm_CauchyRiemannIndex_joined_of_reparametrization
import Theorems.Thm_CauchyRiemannIndex_joined_of_fundamentalSolution_close
import Theorems.Thm_CauchyRiemannIndex_exists_loop_fundamentalSolution_close
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Connected.PathConnected

open CauchyRiemannIndex

namespace CRJ3

variable {n : ℕ}

/-- Two loops are joined through nondegenerate loops of symmetric matrices. -/
def Jn (A B : ℝ → Mat n) : Prop :=
  ∃ H : C(unitInterval × ℝ, Mat n), (∀ t, H (0, t) = A t) ∧ (∀ t, H (1, t) = B t) ∧
    ∀ τ, IsSymLoop (fun t => H (τ, t)) ∧ IsNondegenerate (fun t => H (τ, t))

theorem Jn_trans {A B C : ℝ → Mat n} (h₁ : Jn A B) (h₂ : Jn B C) : Jn A C := by
  obtain ⟨H₁, a₁, b₁, c₁⟩ := h₁
  obtain ⟨H₂, a₂, b₂, c₂⟩ := h₂
  let F : Set C(ℝ, Mat n) := {f | IsSymLoop f ∧ IsNondegenerate f}
  have j₁ : JoinedIn F (H₁.curry 0) (H₁.curry 1) := ⟨⟨H₁.curry, rfl, rfl⟩, fun τ => c₁ τ⟩
  have j₂ : JoinedIn F (H₂.curry 0) (H₂.curry 1) := ⟨⟨H₂.curry, rfl, rfl⟩, fun τ => c₂ τ⟩
  have e : H₁.curry 1 = H₂.curry 0 := ContinuousMap.ext fun t => by
    simp only [ContinuousMap.curry_apply, b₁, a₂]
  rw [e] at j₁
  have j := j₁.trans j₂
  refine ⟨ContinuousMap.uncurry j.somePath.toContinuousMap, fun t => ?_, fun t => ?_,
    fun τ => j.somePath_mem τ⟩
  · show j.somePath 0 t = A t
    rw [Path.source]; exact a₁ t
  · show j.somePath 1 t = C t
    rw [Path.target]; exact b₂ t

theorem Jn_symm {A B : ℝ → Mat n} (h : Jn A B) : Jn B A := by
  obtain ⟨H, a, b, c⟩ := h
  refine ⟨H.comp ⟨fun p => (unitInterval.symm p.1, p.2), by fun_prop⟩, fun t => ?_,
    fun t => ?_, fun τ => c (unitInterval.symm τ)⟩
  · simpa using b t
  · simpa using a t

/-- The time change `β t = t - sin (2πt) / (2π)`. -/
noncomputable def β (t : ℝ) : ℝ := t - Real.sin (2 * Real.pi * t) / (2 * Real.pi)

/-- Its derivative `β' t = 1 - cos (2πt)`. -/
noncomputable def β' (t : ℝ) : ℝ := 1 - Real.cos (2 * Real.pi * t)

theorem hasDerivAt_β (t : ℝ) : HasDerivAt β (β' t) t := by
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun x => 2 * Real.pi * x) (2 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)
  have h3 := (hasDerivAt_id t).sub ((h1.sin).div_const (2 * Real.pi))
  show HasDerivAt (fun x => x - Real.sin (2 * Real.pi * x) / (2 * Real.pi)) _ t
  refine h3.congr_deriv ?_
  unfold β'
  field_simp

theorem continuous_β' : Continuous β' := by unfold β'; fun_prop

theorem β_add_one (t : ℝ) : β (t + 1) = β t + 1 := by
  unfold β
  rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring, Real.sin_add_two_pi]
  ring

theorem β_zero : β 0 = 0 := by simp [β]

theorem β_one : β 1 = 1 := by simp [β]

theorem β'_zero : β' 0 = 0 := by simp [β']

theorem β_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : β t ∈ Set.Icc (0 : ℝ) 1 := by
  have hπ : 0 < 2 * Real.pi := by positivity
  constructor
  · unfold β
    have := Real.sin_le (by have := ht.1; positivity : 0 ≤ 2 * Real.pi * t)
    rw [sub_nonneg, div_le_iff₀ hπ]
    linarith
  · unfold β
    have := Real.sin_le (by nlinarith [ht.2] : 0 ≤ 2 * Real.pi * (1 - t))
    have e : Real.sin (2 * Real.pi * (1 - t)) = - Real.sin (2 * Real.pi * t) := by
      rw [show 2 * Real.pi * (1 - t) = -(2 * Real.pi * t) + 2 * Real.pi by ring,
        Real.sin_add_two_pi, Real.sin_neg]
    have h2 : -Real.sin (2 * Real.pi * t) / (2 * Real.pi) ≤ 1 - t := by
      rw [div_le_iff₀ hπ]; linarith
    rw [neg_div] at h2
    linarith

theorem continuous_β : Continuous β :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_β t).continuousAt

/-- `β` as a self-map of `[0, 1]`. -/
noncomputable def βI : C(unitInterval, unitInterval) :=
  ⟨fun t => ⟨β t, β_mem t.2⟩, (continuous_β.comp continuous_subtype_val).subtype_mk _⟩

theorem βI_zero : βI 0 = 0 := Subtype.ext β_zero

theorem βI_one : βI 1 = 1 := Subtype.ext β_one

theorem fund_comp {S Ψ : ℝ → Mat n} (h : IsFundamentalSolution S Ψ) :
    IsFundamentalSolution (fun t => β' t • S (β t)) (fun t => Ψ (β t)) := by
  refine ⟨by simp only [β_zero]; exact h.1, fun t => ?_⟩
  letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Mat n) := Matrix.normedSpace
  have := (h.2 (β t)).scomp t (hasDerivAt_β t)
  refine this.congr_deriv ?_
  simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem main (n : ℕ) (S₀ S₁ : ℝ → Mat n) (h₀ : IsSymLoop S₀)
    (h₁ : IsSymLoop S₁) (hn₀ : IsNondegenerate S₀) (hn₁ : IsNondegenerate S₁)
    (Ψ₀ Ψ₁ : ℝ → Mat n) (hΨ₀ : IsFundamentalSolution S₀ Ψ₀) (hΨ₁ : IsFundamentalSolution S₁ Ψ₁)
    (G : C(unitInterval × unitInterval, Mat n)) (hG₀ : ∀ t : unitInterval, G (0, t) = Ψ₀ t)
    (hG₁ : ∀ t : unitInterval, G (1, t) = Ψ₁ t) (hGs : ∀ s t, IsSymplectic (G (s, t)))
    (hG0 : ∀ s, G (s, 0) = 1) (hG1 : ∀ s, (1 - G (s, 1)).det ≠ 0) : Jn S₀ S₁ := by
  -- time change of both ends
  obtain ⟨K₀, k₀0, k₀1, k₀τ⟩ := joined_of_reparametrization n S₀ h₀ hn₀ β β' hasDerivAt_β
    continuous_β' β_zero β_add_one
  obtain ⟨K₁, k₁0, k₁1, k₁τ⟩ := joined_of_reparametrization n S₁ h₁ hn₁ β β' hasDerivAt_β
    continuous_β' β_zero β_add_one
  set S₀β : ℝ → Mat n := fun t => β' t • S₀ (β t) with hS₀βdef
  set S₁β : ℝ → Mat n := fun t => β' t • S₁ (β t) with hS₁βdef
  have J0 : Jn S₀ S₀β := ⟨K₀, k₀0, k₀1, k₀τ⟩
  have J1 : Jn S₁ S₁β := ⟨K₁, k₁0, k₁1, k₁τ⟩
  have hS₀β : IsSymLoop S₀β ∧ IsNondegenerate S₀β := by
    have e : (fun t => K₀ (1, t)) = S₀β := funext k₀1
    exact e ▸ k₀τ 1
  have hS₁β : IsSymLoop S₁β ∧ IsNondegenerate S₁β := by
    have e : (fun t => K₁ (1, t)) = S₁β := funext k₁1
    exact e ▸ k₁τ 1
  -- the time-changed family
  let G' : C(unitInterval × unitInterval, Mat n) :=
    ⟨fun p => G (p.1, βI p.2),
      G.continuous.comp (continuous_fst.prodMk (βI.continuous.comp continuous_snd))⟩
  let Good : ℝ → unitInterval → (ℝ → Mat n) → Prop := fun r c S =>
    IsSymLoop S ∧ IsNondegenerate S ∧ S 0 = 0 ∧ ∃ Ψ, IsFundamentalSolution S Ψ ∧
      ∀ t : unitInterval, ∀ i j, |Ψ t i j - G' (c, t) i j| < r
  have mono : ∀ r r' c S, Good r c S → r ≤ r' → Good r' c S := by
    rintro r r' c S ⟨a1, a2, a3, Ψ, a4, a5⟩ hr
    exact ⟨a1, a2, a3, Ψ, a4, fun t i j => (a5 t i j).trans_le hr⟩
  have shift : ∀ r δ c c' S, Good r c S →
      (∀ (t : unitInterval) i j, |G' (c, t) i j - G' (c', t) i j| < δ) → Good (r + δ) c' S := by
    rintro r δ c c' S ⟨a1, a2, a3, Ψ, a4, a5⟩ hcc
    refine ⟨a1, a2, a3, Ψ, a4, fun t i j => ?_⟩
    have := abs_sub_le (Ψ t i j) (G' (c, t) i j) (G' (c', t) i j)
    linarith [a5 t i j, hcc t i j]
  -- centers
  have hψs : ∀ c t, IsSymplectic (G'.curry c t) := fun c t => hGs _ _
  have hψ0 : ∀ c, G'.curry c 0 = 1 := fun c => by
    show G (c, βI 0) = 1; rw [βI_zero]; exact hG0 c
  have hψ1 : ∀ c, (1 - G'.curry c 1).det ≠ 0 := fun c => by
    show (1 - G (c, βI 1)).det ≠ 0; rw [βI_one]; exact hG1 c
  have D2 : ∀ c, ∃ e > 0, ∀ S S', Good e c S → Good e c S' → Jn S S' := by
    intro c
    obtain ⟨e, he, hD⟩ := joined_of_fundamentalSolution_close n (G'.curry c) (hψs c) (hψ1 c)
    exact ⟨e, he, fun S S' ⟨a1, a2, a3, Ψ, a4, a5⟩ ⟨b1, b2, b3, Ψ', b4, b5⟩ =>
      hD S S' Ψ Ψ' a1 b1 a2 b2 a3 b3 a4 b4 a5 b5⟩
  have D3 : ∀ c, ∀ r > 0, ∃ S, Good r c S := by
    intro c r hr
    obtain ⟨S, Ψ, a1, a2, a3, a4, a5⟩ :=
      exists_loop_fundamentalSolution_close n (G'.curry c) (hψs c) (hψ0 c) (hψ1 c) r hr
    exact ⟨S, a1, a2, a3, Ψ, a4, a5⟩
  have UC : ∀ δ > 0, ∃ η > 0, ∀ c c' : unitInterval, dist c c' < η →
      ∀ (t : unitInterval) i j, |G' (c, t) i j - G' (c', t) i j| < δ := by
    intro δ hδ
    letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
    have hu := CompactSpace.uniformContinuous_of_continuous G'.continuous
    rw [Metric.uniformContinuous_iff] at hu
    obtain ⟨η, hη, h⟩ := hu δ hδ
    refine ⟨η, hη, fun c c' hc t i j => ?_⟩
    have hd : dist (c, t) (c', t) < η := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]; exact hc
    have h2 := h hd
    rw [dist_eq_norm] at h2
    have h3 := (Matrix.norm_entry_le_entrywise_sup_norm (G' (c, t) - G' (c', t))
      (i := i) (j := j)).trans_lt h2
    simpa [Real.norm_eq_abs] using h3
  -- the set of centers whose neighbourhood is joined to `S₀β`
  let U : Set unitInterval := {c | ∃ ε > 0, ∀ S, Good ε c S → Jn S₀β S}
  have hopen : IsOpen U := by
    rw [Metric.isOpen_iff]
    rintro c ⟨ε₁, hε₁, hQ⟩
    obtain ⟨e, he, hD⟩ := D2 c
    obtain ⟨η, hη, hU⟩ := UC (e / 2) (by positivity)
    refine ⟨η, hη, fun c' hc' => ⟨e / 2, by positivity, fun S hS => ?_⟩⟩
    have hS' : Good e c S := by
      have := shift _ _ c' c S hS (hU c' c (by rwa [Metric.mem_ball] at hc'))
      rwa [add_halves] at this
    obtain ⟨χ, hχ⟩ := D3 c (min ε₁ e) (lt_min hε₁ he)
    exact Jn_trans (hQ χ (mono _ _ _ _ hχ (min_le_left _ _)))
      (hD χ S (mono _ _ _ _ hχ (min_le_right _ _)) hS')
  have hclosed : IsClosed U := by
    rw [← isOpen_compl_iff, Metric.isOpen_iff]
    intro c hc
    obtain ⟨e, he, hD⟩ := D2 c
    obtain ⟨η, hη, hU⟩ := UC (e / 2) (by positivity)
    refine ⟨η, hη, fun c' hc' hc'U => hc ?_⟩
    obtain ⟨ε₂, hε₂, hQ⟩ := hc'U
    refine ⟨e, he, fun S hS => ?_⟩
    obtain ⟨χ, hχ⟩ := D3 c' (min ε₂ (e / 2)) (lt_min hε₂ (by positivity))
    have hχc : Good e c χ := by
      have := shift _ _ c' c χ (mono _ _ _ _ hχ (min_le_right _ _))
        (hU c' c (by rwa [Metric.mem_ball] at hc'))
      rwa [add_halves] at this
    exact Jn_trans (hQ χ (mono _ _ _ _ hχ (min_le_left _ _))) (hD χ S hχc hS)
  have h0U : (0 : unitInterval) ∈ U := by
    obtain ⟨e, he, hD⟩ := D2 0
    refine ⟨e, he, fun S hS => hD S₀β S ?_ hS⟩
    refine ⟨hS₀β.1, hS₀β.2, by simp [S₀β, β'_zero], fun t => Ψ₀ (β t), fund_comp hΨ₀,
      fun t i j => ?_⟩
    have : G' (0, t) = Ψ₀ (β t) := hG₀ (βI t)
    simp [this, he]
  have hUu : U = Set.univ := by
    rcases isClopen_iff.1 ⟨hclosed, hopen⟩ with h | h
    · rw [h] at h0U; simp at h0U
    · exact h
  obtain ⟨ε, hε, hQ⟩ : (1 : unitInterval) ∈ U := hUu ▸ Set.mem_univ _
  have J01 : Jn S₀β S₁β := by
    refine hQ S₁β ⟨hS₁β.1, hS₁β.2, by simp [S₁β, β'_zero], fun t => Ψ₁ (β t), fund_comp hΨ₁,
      fun t i j => ?_⟩
    have : G' (1, t) = Ψ₁ (β t) := hG₁ (βI t)
    simp [this, hε]
  exact Jn_trans (Jn_trans J0 J01) (Jn_symm J1)

end CRJ3

theorem solution (n : ℕ) (S₀ S₁ : ℝ → Mat n) (h₀ : IsSymLoop S₀)
    (h₁ : IsSymLoop S₁) (hn₀ : IsNondegenerate S₀) (hn₁ : IsNondegenerate S₁)
    (Ψ₀ Ψ₁ : ℝ → Mat n) (hΨ₀ : IsFundamentalSolution S₀ Ψ₀) (hΨ₁ : IsFundamentalSolution S₁ Ψ₁)
    (G : C(unitInterval × unitInterval, Mat n)) (hG₀ : ∀ t : unitInterval, G (0, t) = Ψ₀ t)
    (hG₁ : ∀ t : unitInterval, G (1, t) = Ψ₁ t) (hGs : ∀ s t, IsSymplectic (G (s, t)))
    (hG0 : ∀ s, G (s, 0) = 1) (hG1 : ∀ s, (1 - G (s, 1)).det ≠ 0) :
    ∃ H : C(unitInterval × ℝ, Mat n), (∀ t, H (0, t) = S₀ t) ∧ (∀ t, H (1, t) = S₁ t) ∧
      ∀ τ, IsSymLoop (fun t => H (τ, t)) ∧ IsNondegenerate (fun t => H (τ, t)) :=
  CRJ3.main n S₀ S₁ h₀ h₁ hn₀ hn₁ Ψ₀ Ψ₁ hΨ₀ hΨ₁ G hG₀ hG₁ hGs hG0 hG1
