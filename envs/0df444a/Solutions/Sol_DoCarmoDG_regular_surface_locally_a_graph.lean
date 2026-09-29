-- Prove2me | solution 1 for DoCarmoDG.regular_surface_locally_a_graph
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T17:20:46.892132+00:00
-- url     : https://prove2.me/submissions/05e27087-7cec-46de-851a-20d9725acf94

import Mathlib
import Definitions.Def_DoCarmo_regular_surface

/-! 3ad3b8f2 DoCarmoDG.regular_surface_locally_a_graph (do Carmo §2-2, Prop. 3).
Take a chart `y : W → V ∩ S` at `p = y w₀` with continuous inverse `h`. Some 2×2 minor of
`dy(w₀)` is nonzero (else `dy(w₀)` kills `(b_m, -a_m)`), say in rows `i, j`; with
`π = (proj i, proj j)` the map `π ∘ y` has invertible derivative at `w₀`. The inverse function
theorem gives a partial homeomorphism `Φ = π ∘ y`, which we restrict to the open set where
`π ∘ dy` is invertible, so `Φ.symm` is C^∞ on the open set `Φ.target` (`contDiffAt_symm`).
With `f = y_k ∘ Φ.symm` and `W' = V ∩ O`, where `O ∩ y(W) = h⁻¹(Φ.source) ∩ y(W)`, one has
`W' ∩ S = W' ∩ graph(f)`. -/

set_option autoImplicit false

namespace GraphBuild

open DoCarmoDG Filter Topology

theorem lin2 (D : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3)) (s t : ℝ) :
    D (s, t) = s • D (1, 0) + t • D (0, 1) := by
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  ext <;> simp

theorem minors (D : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3)) (hD : Function.Injective D) :
    D (1, 0) 0 * D (0, 1) 1 - D (1, 0) 1 * D (0, 1) 0 ≠ 0 ∨
    D (1, 0) 0 * D (0, 1) 2 - D (1, 0) 2 * D (0, 1) 0 ≠ 0 ∨
    D (1, 0) 1 * D (0, 1) 2 - D (1, 0) 2 * D (0, 1) 1 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨m01, m02, m12⟩ := hcon
  by_cases ha : D (1, 0) = 0
  · have h1 : D (1, 0) = D 0 := by rw [map_zero]; exact ha
    have h2 := hD h1
    simp at h2
  · obtain ⟨m, hm⟩ : ∃ m, D (1, 0) m ≠ 0 := by
      by_contra hc
      push Not at hc
      exact ha (by ext n; simp [hc n])
    have key : D (D (0, 1) m, -D (1, 0) m) = 0 := by
      rw [lin2]
      ext n
      fin_cases m <;> fin_cases n <;> simp <;> linarith
    have h3 := hD (key.trans (map_zero D).symm)
    simp only [Prod.mk_eq_zero, neg_eq_zero] at h3
    exact hm h3.2

theorem graph_local (S V : Set (EuclideanSpace ℝ (Fin 3))) (W : Set (ℝ × ℝ))
    (y : ℝ × ℝ → EuclideanSpace ℝ (Fin 3)) (h : EuclideanSpace ℝ (Fin 3) → ℝ × ℝ)
    (hV : IsOpen V) (hW : IsOpen W) (hys : ContDiffOn ℝ (⊤ : ℕ∞) y W)
    (hVS : y '' W = V ∩ S) (hhc : ContinuousOn h (y '' W)) (hhy : ∀ q ∈ W, h (y q) = q)
    (w₀ : ℝ × ℝ) (hw₀ : w₀ ∈ W) (i j k : Fin 3)
    (hijk : ∀ n : Fin 3, n = i ∨ n = j ∨ n = k)
    (hminor : fderiv ℝ y w₀ (1, 0) i * fderiv ℝ y w₀ (0, 1) j -
      fderiv ℝ y w₀ (1, 0) j * fderiv ℝ y w₀ (0, 1) i ≠ 0) :
    ∃ W' : Set (EuclideanSpace ℝ (Fin 3)), IsOpen W' ∧ y w₀ ∈ W' ∧
      ∃ (U' : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ), IsOpen U' ∧ ContDiffOn ℝ (⊤ : ℕ∞) f U' ∧
        W' ∩ S = W' ∩ {s | (s i, s j) ∈ U' ∧ s k = f (s i, s j)} := by
  set π : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ × ℝ :=
    (EuclideanSpace.proj i).prod (EuclideanSpace.proj j) with hπ
  have hπapp : ∀ s, π s = (s i, s j) := fun s => rfl
  set A := π.comp (fderiv ℝ y w₀) with hA
  have hinjA : Function.Injective A := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨s, t⟩ hst
    rw [hA, ContinuousLinearMap.comp_apply, lin2, hπapp] at hst
    simp only [Prod.mk_eq_zero, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hst
    obtain ⟨e1, e2⟩ := hst
    have hs : (fderiv ℝ y w₀ (1, 0) i * fderiv ℝ y w₀ (0, 1) j -
      fderiv ℝ y w₀ (1, 0) j * fderiv ℝ y w₀ (0, 1) i) * s = 0 := by
      linear_combination fderiv ℝ y w₀ (0, 1) j * e1 - fderiv ℝ y w₀ (0, 1) i * e2
    have ht : (fderiv ℝ y w₀ (1, 0) i * fderiv ℝ y w₀ (0, 1) j -
      fderiv ℝ y w₀ (1, 0) j * fderiv ℝ y w₀ (0, 1) i) * t = 0 := by
      linear_combination fderiv ℝ y w₀ (1, 0) i * e2 - fderiv ℝ y w₀ (1, 0) j * e1
    rw [mul_eq_zero] at hs ht
    simp only [Prod.mk_eq_zero]
    exact ⟨hs.resolve_left hminor, ht.resolve_left hminor⟩
  have hdiff : ∀ w ∈ W, ContDiffAt ℝ (⊤ : ℕ∞) y w := fun w hw => hys.contDiffAt (hW.mem_nhds hw)
  set De : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    (LinearEquiv.ofInjectiveEndo (A : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) hinjA).toContinuousLinearEquiv
  have hDe : (De : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = A := ContinuousLinearMap.ext fun v => rfl
  have hF : HasStrictFDerivAt (fun w => π (y w)) (De : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) w₀ := by
    rw [hDe]
    exact π.hasStrictFDerivAt.comp w₀ ((hdiff w₀ hw₀).hasStrictFDerivAt (by simp))
  set Ω := W ∩ (fun w => π.comp (fderiv ℝ y w)) ⁻¹'
    Set.range ((↑) : ((ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) with hΩdef
  have hΩ : IsOpen Ω := by
    have hc : ContinuousOn (fun w => π.comp (fderiv ℝ y w)) W :=
      continuousOn_const.clm_comp (hys.continuousOn_fderiv_of_isOpen hW (by simp))
    exact hc.isOpen_inter_preimage hW ContinuousLinearEquiv.isOpen
  have hw₀Ω : w₀ ∈ Ω := ⟨hw₀, De, hDe⟩
  set Φ := (hF.toOpenPartialHomeomorph (fun w => π (y w))).restrOpen Ω hΩ with hΦdef
  have hΦsrc : Φ.source = (hF.toOpenPartialHomeomorph (fun w => π (y w))).source ∩ Ω :=
    OpenPartialHomeomorph.restrOpen_source _ _ _
  have hΦcoe : ∀ w, Φ w = π (y w) := fun w => rfl
  have hw₀src : w₀ ∈ Φ.source := by
    rw [hΦsrc]; exact ⟨hF.mem_toOpenPartialHomeomorph_source, hw₀Ω⟩
  have hsrcΩ : ∀ w ∈ Φ.source, w ∈ Ω := fun w hw => by rw [hΦsrc] at hw; exact hw.2
  obtain ⟨O, hO, hOeq⟩ := continuousOn_iff'.1 hhc Φ.source Φ.open_source
  have hyW : y w₀ ∈ y '' W := ⟨w₀, hw₀, rfl⟩
  refine ⟨V ∩ O, hV.inter hO, ⟨?_, ?_⟩, Φ.target, fun z => y (Φ.symm z) k, Φ.open_target,
    ?_, ?_⟩
  · rw [hVS] at hyW; exact hyW.1
  · have : y w₀ ∈ h ⁻¹' Φ.source ∩ y '' W := ⟨by simp [hhy w₀ hw₀, hw₀src], hyW⟩
    rw [hOeq] at this; exact this.1
  · intro z hz
    apply ContDiffAt.contDiffWithinAt
    have hwz : Φ.symm z ∈ Φ.source := Φ.map_target hz
    obtain ⟨hWz, e, he⟩ := hsrcΩ _ hwz
    have hyz := hdiff _ hWz
    have hΦd : HasFDerivAt Φ (e : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (Φ.symm z) := by
      have h1 := π.hasFDerivAt.comp (Φ.symm z) (hyz.differentiableAt (by simp)).hasFDerivAt
      rw [he]; exact h1
    have hΦc : ContDiffAt ℝ (⊤ : ℕ∞) Φ (Φ.symm z) := π.contDiff.contDiffAt.comp _ hyz
    have hsymm : ContDiffAt ℝ (⊤ : ℕ∞) Φ.symm z := Φ.contDiffAt_symm hz hΦd hΦc
    exact (EuclideanSpace.proj k).contDiff.contDiffAt.comp z (hyz.comp z hsymm)
  · ext s
    constructor
    · rintro ⟨hsW', hsS⟩
      refine ⟨hsW', ?_⟩
      have hsy : s ∈ y '' W := by rw [hVS]; exact ⟨hsW'.1, hsS⟩
      have hsh : s ∈ h ⁻¹' Φ.source ∩ y '' W := by rw [hOeq]; exact ⟨hsW'.2, hsy⟩
      obtain ⟨w, hw, rfl⟩ := hsy
      have hws : w ∈ Φ.source := by have := hsh.1; simp only [Set.mem_preimage, hhy w hw] at this; exact this
      have hmap := Φ.map_source hws
      rw [hΦcoe, hπapp] at hmap
      refine ⟨hmap, ?_⟩
      have hl := Φ.left_inv hws
      rw [hΦcoe, hπapp] at hl
      show y w k = y (Φ.symm (y w i, y w j)) k
      rw [hl]
    · rintro ⟨hsW', hsU', hsk⟩
      refine ⟨hsW', ?_⟩
      have hwsrc := Φ.map_target hsU'
      have hr := Φ.right_inv hsU'
      rw [hΦcoe, hπapp] at hr
      have hWw : Φ.symm (s i, s j) ∈ W := (hsrcΩ _ hwsrc).1
      have hys' : y (Φ.symm (s i, s j)) = s := by
        obtain ⟨hi, hj⟩ := Prod.mk.inj hr
        ext n
        rcases hijk n with rfl | rfl | rfl
        · exact hi
        · exact hj
        · exact hsk.symm
      have : s ∈ y '' W := ⟨_, hWw, hys'⟩
      rw [hVS] at this
      exact this.2

end GraphBuild

open DoCarmoDG in
theorem solution
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : IsRegularSurface S)
    (p : EuclideanSpace ℝ (Fin 3)) (hp : p ∈ S) :
    ∃ W : Set (EuclideanSpace ℝ (Fin 3)), IsOpen W ∧ p ∈ W ∧
      ((∃ (U : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ),
          IsOpen U ∧ ContDiffOn ℝ (⊤ : ℕ∞) f U ∧ W ∩ S = W ∩ graphOf U f) ∨
       (∃ (U : Set (ℝ × ℝ)) (g : ℝ × ℝ → ℝ),
          IsOpen U ∧ ContDiffOn ℝ (⊤ : ℕ∞) g U ∧ W ∩ S = W ∩ graphOfXZ U g) ∨
       (∃ (U : Set (ℝ × ℝ)) (h : ℝ × ℝ → ℝ),
          IsOpen U ∧ ContDiffOn ℝ (⊤ : ℕ∞) h U ∧ W ∩ S = W ∩ graphOfYZ U h)) := by
  obtain ⟨V, W, y, hV, hpV, ⟨hW, hys, _, _, ⟨h, hhc, hhy⟩, hyreg⟩, hVS⟩ := hS p hp
  have hpy : p ∈ y '' W := by rw [hVS]; exact ⟨hpV, hp⟩
  obtain ⟨w₀, hw₀, rfl⟩ := hpy
  rcases GraphBuild.minors _ (hyreg w₀ hw₀) with hm | hm | hm
  · obtain ⟨W', hW', hpW', U', f, hU', hf, heq⟩ := GraphBuild.graph_local S V W y h hV hW hys
      hVS hhc hhy w₀ hw₀ 0 1 2 (by decide) hm
    exact ⟨W', hW', hpW', Or.inl ⟨U', f, hU', hf, heq⟩⟩
  · obtain ⟨W', hW', hpW', U', f, hU', hf, heq⟩ := GraphBuild.graph_local S V W y h hV hW hys
      hVS hhc hhy w₀ hw₀ 0 2 1 (by decide) hm
    exact ⟨W', hW', hpW', Or.inr (Or.inl ⟨U', f, hU', hf, heq⟩)⟩
  · obtain ⟨W', hW', hpW', U', f, hU', hf, heq⟩ := GraphBuild.graph_local S V W y h hV hW hys
      hVS hhc hhy w₀ hw₀ 1 2 0 (by decide) hm
    exact ⟨W', hW', hpW', Or.inr (Or.inr ⟨U', f, hU', hf, heq⟩)⟩
