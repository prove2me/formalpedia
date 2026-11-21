-- Prove2me | solution 1 for FiniteEnergyPlane.exists_tubeCoords_of_isCylCloseTo
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T09:41:03.237191+00:00
-- url     : https://prove2.me/submissions/d242c421-0f05-4cb8-bac9-58427e4fc71f

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Definitions.Def_FiniteEnergyPlane_CylClose
import Theorems.Thm_FiniteEnergyPlane_exists_cylBounds_tubeMap
import Theorems.Thm_FiniteEnergyPlane_exists_homeomorph_of_norm_fderiv_sub_id_le
import Theorems.Thm_FiniteEnergyPlane_weighted_norm_sub_inl_le_of_cylBounds
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj



/-!
# A2: tube coordinates of a map close to the plane in cylindrical scale
-/

namespace FiniteEnergyPlane

namespace DGA2

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

lemma exp_smul_proj (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V 1) (hy : y ≠ 0) :
    Real.exp (2 * aCoord H y) • proj H y = y := by
  have hex : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := (hH.2.1 y hy).exists
  have hr : 0 < scaleToS H y := by
    unfold scaleToS; rw [dif_pos hex]; exact (Classical.choose_spec hex).1
  unfold proj aCoord
  have e : Real.exp (2 * (-Real.log (scaleToS H y) / 2)) = (scaleToS H y)⁻¹ := by
    rw [show 2 * (-Real.log (scaleToS H y) / 2) = -Real.log (scaleToS H y) by ring, Real.exp_neg,
      Real.exp_log hr]
  rw [e, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

variable {H : V 1 → ℝ} {Φ : ℂ × ℂ → V 1} {ρ c : ℝ}

lemma uniq (hc : 0 < c)
    (hlow : ∀ p ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ, ∀ q ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ,
      c * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤
        |aCoord H (Φ p) - aCoord H (Φ q)| + ‖proj H (Φ p) - proj H (Φ q)‖)
    {p q : ℂ × ℂ} (hp : p ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ)
    (hq : q ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ) (he : Φ p = Φ q) : p = q := by
  have h := hlow p hp q hq
  rw [he, sub_self, sub_self, abs_zero, norm_zero, add_zero] at h
  have hX : 0 ≤ ‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) := by positivity
  have hY : 0 ≤ ‖p.2 - q.2‖ := norm_nonneg _
  have hs : ‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖ ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_pos hc hcon]
  have h2 : ‖p.2 - q.2‖ = 0 := by linarith
  have h1 : ‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) = 0 := by linarith
  rw [div_eq_zero_iff] at h1
  have h1' : ‖p.1 - q.1‖ = 0 := h1.resolve_right (by positivity)
  exact Prod.ext (sub_eq_zero.1 (norm_eq_zero.1 h1')) (sub_eq_zero.1 (norm_eq_zero.1 h2))

lemma bound0 (hρ : 0 < ρ)
    (hlow : ∀ p ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ, ∀ q ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ,
      c * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤
        |aCoord H (Φ p) - aCoord H (Φ q)| + ‖proj H (Φ p) - proj H (Φ q)‖)
    {ε : ℝ} {p : ℂ × ℂ} (hp : p ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ) {z : ℂ} {y y₀ : V 1}
    (hpz : Φ p = y) (h0 : Φ (z, 0) = y₀) (ha : |aCoord H y - aCoord H y₀| ≤ ε)
    (hπ : ‖proj H y - proj H y₀‖ ≤ ε) :
    c * (‖p.1 - z‖ / (1 + ‖p.1‖ + ‖z‖) + ‖p.2‖) ≤ 2 * ε := by
  have h := hlow p hp (z, 0) ⟨Set.mem_univ _, by simp [hρ]⟩
  rw [hpz, h0] at h
  have e : ‖p.2 - (z, (0 : ℂ)).2‖ = ‖p.2‖ := by simp
  have e1 : ‖(z, (0 : ℂ)).1‖ = ‖z‖ := rfl
  have e2 : p.1 - (z, (0 : ℂ)).1 = p.1 - z := rfl
  rw [e, e1, e2] at h
  linarith

lemma small_of_bound {c ε X Y : ℝ} (hc : 0 < c) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : c * (X + Y) ≤ 2 * ε) : X ≤ 2 * ε / c ∧ Y ≤ 2 * ε / c := by
  constructor <;> rw [le_div_iff₀ hc] <;> nlinarith

lemma norm_le_of_X {a z : ℂ} (h : ‖a - z‖ / (1 + ‖a‖ + ‖z‖) ≤ 1 / 4) :
    ‖a‖ ≤ 2 * ‖z‖ + 1 ∧ ‖z‖ ≤ 2 * ‖a‖ + 1 := by
  have hD : 0 < 1 + ‖a‖ + ‖z‖ := by positivity
  rw [div_le_iff₀ hD] at h
  have h1 := norm_sub_norm_le a z
  have h2 := norm_sub_norm_le z a
  rw [norm_sub_rev] at h2
  constructor <;> nlinarith [norm_nonneg z, norm_nonneg a]

/-- The constant bookkeeping. -/
lemma arith {c c₁ C ε m X Y : ℝ} (hc : 0 < c) (hc₁ : 0 < c₁) (hC : 0 ≤ C) (hε : 0 < ε)
    (h1 : ε ≤ c * m / 8) (h2 : ε ≤ c / 8) (h4 : ε ≤ c₁ * c / (8 * (c + 36 * C)))
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hX : X ≤ 2 * ε / c) (hY : Y ≤ 2 * ε / c) :
    2 / c₁ * (ε + 16 * C * X + 2 * C * Y) ≤ 1 / 4 ∧ C * Y ≤ c₁ / 2 ∧
      2 * ε / c ≤ 1 / 4 ∧ 2 * ε / c ≤ m / 4 := by
  have hcX : c * X ≤ 2 * ε := by rw [le_div_iff₀ hc] at hX; linarith
  have hcY : c * Y ≤ 2 * ε := by rw [le_div_iff₀ hc] at hY; linarith
  have hpos : 0 < 8 * (c + 36 * C) := by positivity
  have h4' : ε * (8 * (c + 36 * C)) ≤ c₁ * c := by rwa [le_div_iff₀ hpos] at h4
  -- S * c ≤ ε (c + 36 C)
  set S := ε + 16 * C * X + 2 * C * Y
  have hS : S * c ≤ ε * (c + 36 * C) := by
    have : C * (c * X) ≤ C * (2 * ε) := mul_le_mul_of_nonneg_left hcX hC
    have : C * (c * Y) ≤ C * (2 * ε) := mul_le_mul_of_nonneg_left hcY hC
    simp only [S]; nlinarith
  have hS8 : 8 * S ≤ c₁ := by
    have : 8 * S * c ≤ c₁ * c := by nlinarith
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_le_iff₀ hc₁]; linarith
  · have hCY : 8 * (2 * C * Y) ≤ c₁ := by
      have : 0 ≤ 16 * C * X := by positivity
      simp only [S] at hS8; linarith
    linarith
  · rw [div_le_iff₀ hc]; linarith
  · rw [div_le_iff₀ hc]; linarith

lemma arith_psi {A K hn zn ζn : ℝ} (hK : K ≤ 1 / 4) (hK0 : 0 ≤ K) (hz : 0 ≤ zn) (hζ : 0 ≤ ζn)
    (hr : 1 + ζn ≤ 2 * (1 + zn)) (hh : 0 ≤ hn)
    (hA : A / (1 + ζn) ≤ K * (hn / (1 + zn))) : A ≤ 1 / 2 * hn := by
  have h1 : 0 < 1 + ζn := by linarith
  have h2 : 0 < 1 + zn := by linarith
  rw [div_le_iff₀ h1] at hA
  have : K * (hn / (1 + zn)) * (1 + ζn) ≤ K * (hn / (1 + zn)) * (2 * (1 + zn)) :=
    mul_le_mul_of_nonneg_left hr (by positivity)
  have e : K * (hn / (1 + zn)) * (2 * (1 + zn)) = 2 * K * hn := by field_simp
  nlinarith

set_option maxHeartbeats 1600000 in
theorem exists_tubeCoords_of_isCylCloseTo_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 < c)
    (hΦ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p))
    (hlow : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, ∀ q ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      c * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤
        |aCoord H (u p.1 + N p.1 p.2) - aCoord H (u q.1 + N q.1 q.2)| +
          ‖proj H (u p.1 + N p.1 p.2) - proj H (u q.1 + N q.1 q.2)‖) :
    ∃ ε > 0, ∀ f : ℂ → V 1, ContDiff ℝ ∞ f → (∀ z, f z ≠ 0) → IsCylCloseTo H ε f u →
      ∃ (ψ : ℂ ≃ₜ ℂ) (v : ℂ → ℂ), ContDiff ℝ ∞ ψ ∧ ContDiff ℝ ∞ ψ.symm ∧ ContDiff ℝ ∞ v ∧
        (∀ z, ‖v z‖ ≤ ρ / 2) ∧ (∀ z, f z = u (ψ z) + N (ψ z) (v z)) ∧
        (∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2) ∧
        (∀ z, (1 + ‖z‖) * ‖fderiv ℝ v z‖ ≤ 1) := by
  classical
  obtain ⟨ρc, hρc, C, c₁, hc₁, -, hFsm, hCb, hlow1⟩ :=
    exists_cylBounds_tubeMap H hH J P u hu hu0 d b hb ha hw N hN hNinj M hM hNM
  set Φ : ℂ × ℂ → V 1 := fun q => u q.1 + N q.1 q.2 with hΦdef
  set F : ℂ × ℂ → ℝ × V 1 := fun q => (aCoord H (Φ q), proj H (Φ q)) with hFdef
  set T : Set (ℂ × ℂ) := (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ with hT
  have hTo : IsOpen T := isOpen_univ.prod isOpen_ball
  have hΦs : ContDiff ℝ ∞ Φ :=
    (hu.comp contDiff_fst).add ((hN.comp contDiff_fst).clm_apply contDiff_snd)
  have hΦ0 : ∀ z, Φ (z, 0) = u z := fun z => by simp [Φ]
  have hfin : Module.finrank ℝ (ℂ × ℂ) = Module.finrank ℝ (V 1) := by
    rw [Module.finrank_prod, Complex.finrank_real_complex, Module.finrank_fin_fun]
  have heq : ∀ p ∈ T, ∃ e : (ℂ × ℂ) ≃L[ℝ] V 1, (e : ℂ × ℂ →L[ℝ] V 1) = fderiv ℝ Φ p := by
    intro p hp
    refine ⟨(LinearMap.linearEquivOfInjective (fderiv ℝ Φ p : ℂ × ℂ →ₗ[ℝ] V 1)
      (hΦ p hp).2 hfin).toContinuousLinearEquiv, ?_⟩
    exact ContinuousLinearMap.ext fun x => rfl
  have hnhds : ∀ p ∈ T, Φ '' T ∈ 𝓝 (Φ p) := by
    intro p hp
    obtain ⟨e, he⟩ := heq p hp
    have hs : HasStrictFDerivAt Φ (e : ℂ × ℂ →L[ℝ] V 1) p := by
      rw [he]; exact hΦs.contDiffAt.hasStrictFDerivAt (by simp)
    rw [← hs.map_nhds_eq_of_equiv]
    exact image_mem_map (hTo.mem_nhds hp)
  have h00 : ((0 : ℂ), (0 : ℂ)) ∈ T := ⟨Set.mem_univ _, by simp [hρ]⟩
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.1 (hnhds _ h00)
  set g : ℝ × V 1 → V 1 := fun q => Real.exp (2 * q.1) • q.2 with hg
  have hgc : Continuous g :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).smul continuous_snd
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuous_iff.1 hgc (aCoord H (u 0), proj H (u 0)) r₀ hr₀
  -- constants
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hC2 : ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) (ρc / 2) → ∀ h k : ℂ × ℂ,
      ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
        C' * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖) := by
    intro ζ w hw' h k
    refine ((hCb ζ w hw').2 h k).trans ?_
    gcongr
    exact le_max_left _ _
  set m := min ρ ρc with hm
  have hm0 : 0 < m := lt_min hρ hρc
  obtain ⟨ε, hε0, hε1, hε2, hε3, hε4⟩ : ∃ ε > 0, ε ≤ c * m / 8 ∧ ε ≤ c / 8 ∧ ε < δ ∧
      ε ≤ c₁ * c / (8 * (c + 36 * C')) := by
    refine ⟨min (min (c * m / 8) (c / 8)) (min (δ / 2) (c₁ * c / (8 * (c + 36 * C')))), ?_,
      ?_, ?_, ?_, ?_⟩
    · have : 0 < c + 36 * C' := by positivity
      exact lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity))
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε, hε0, fun f hf hf0 hclose => ?_⟩
  have hfc : Continuous f := hf.continuous
  -- size of a preimage point
  have hsmall : ∀ z, ∀ p ∈ T, Φ p = f z →
      ‖p.1 - z‖ / (1 + ‖p.1‖ + ‖z‖) ≤ 2 * ε / c ∧ ‖p.2‖ ≤ 2 * ε / c := by
    intro z p hp hpe
    have := bound0 (Φ := Φ) (H := H) hρ hlow hp hpe (hΦ0 z) (hclose z).1 (hclose z).2.1
    exact small_of_bound hc (by positivity) (norm_nonneg _) this
  have har0 := arith (X := 0) (Y := 0) hc hc₁ hC'0 hε0 hε1 hε2 hε4 le_rfl le_rfl
    (by positivity) (by positivity)
  have h2ec : 2 * ε / c ≤ 1 / 4 := har0.2.2.1
  have h2em : 2 * ε / c ≤ m / 4 := har0.2.2.2
  have h2ρ : 2 * ε / c < ρ := by
    have : m ≤ ρ := min_le_left _ _
    linarith
  -- every value of f lies in the image of the tube
  have hZ : f ⁻¹' (Φ '' T) = Set.univ := by
    have hopen : IsOpen (f ⁻¹' (Φ '' T)) := by
      refine (isOpen_iff_mem_nhds.2 ?_).preimage hfc
      rintro _ ⟨p, hp, rfl⟩
      exact hnhds p hp
    have hclosed : IsClosed (f ⁻¹' (Φ '' T)) := by
      refine isClosed_of_closure_subset fun z hz => ?_
      have hz' : z ∈ closure (ball z 1 ∩ f ⁻¹' (Φ '' T)) :=
        isOpen_ball.inter_closure ⟨mem_ball_self one_pos, hz⟩
      set K := closedBall (0 : ℂ) (2 * (‖z‖ + 1) + 1) ×ˢ closedBall (0 : ℂ) (2 * ε / c)
      have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
      have hKc : IsClosed (Φ '' K) := (hK.image hΦs.continuous).isClosed
      have hmaps : MapsTo f (ball z 1 ∩ f ⁻¹' (Φ '' T)) (Φ '' K) := by
        rintro z' ⟨hz'1, p, hp, hpe⟩
        obtain ⟨hX, hY⟩ := hsmall z' p hp hpe
        refine ⟨p, ⟨?_, mem_closedBall_zero_iff.2 hY⟩, hpe⟩
        have h1 := (norm_le_of_X (hX.trans h2ec)).1
        have h2 : ‖z'‖ ≤ ‖z‖ + 1 := by
          have := mem_ball.1 hz'1
          rw [dist_eq_norm] at this
          have := norm_sub_norm_le z' z
          linarith
        exact mem_closedBall_zero_iff.2 (by linarith)
      obtain ⟨p, hpK, hpe⟩ := hKc.closure_subset (map_mem_closure hfc hz' hmaps)
      exact ⟨p, ⟨Set.mem_univ _, mem_ball_zero_iff.2
        (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hpK.2) h2ρ)⟩, hpe⟩
    have h0 : (0 : ℂ) ∈ f ⁻¹' (Φ '' T) := by
      apply hball
      have hd : dist (aCoord H (f 0), proj H (f 0)) (aCoord H (u 0), proj H (u 0)) < δ := by
        rw [Prod.dist_eq, Real.dist_eq, dist_eq_norm]
        exact max_lt (lt_of_le_of_lt (hclose 0).1 hε3) (lt_of_le_of_lt (hclose 0).2.1 hε3)
      have := hδg _ hd
      simp only [g] at this
      rw [exp_smul_proj H hH _ (hf0 0), exp_smul_proj H hH _ (hu0 0)] at this
      rw [mem_ball, hΦ0]
      exact this
    exact (isClopen_iff.1 ⟨hclosed, hopen⟩).resolve_left
      (Set.nonempty_iff_ne_empty.1 ⟨0, h0⟩)
  have hex : ∀ z, ∃ p ∈ T, Φ p = f z := fun z => by
    have : z ∈ f ⁻¹' (Φ '' T) := hZ ▸ Set.mem_univ z
    exact this
  choose G hGT hGe using hex
  have hGu : ∀ z z', z' ∈ T → Φ z' = f z → G z = z' := fun z z' hz' he =>
    uniq hc hlow (hGT z) hz' ((hGe z).trans he.symm)
  -- smoothness of G
  have hGs : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro z
    obtain ⟨e, he⟩ := heq (G z) (hGT z)
    have hf' : HasFDerivAt Φ (e : ℂ × ℂ →L[ℝ] V 1) (G z) := by
      rw [he]; exact (hΦs.differentiable (by simp) _).hasFDerivAt
    have hca : ContDiffAt ℝ ∞ Φ (G z) := hΦs.contDiffAt
    have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
    have hs := hca.hasStrictFDerivAt' hf' hn
    have hgc : ContDiffAt ℝ ∞ (hs.localInverse Φ e (G z)) (Φ (G z)) := hca.to_localInverse hf' hn
    have h1 : ∀ᶠ y in 𝓝 (Φ (G z)), Φ (hs.localInverse Φ e (G z) y) = y :=
      hs.eventually_right_inverse
    have h2 : ∀ᶠ y in 𝓝 (Φ (G z)), hs.localInverse Φ e (G z) y ∈ T := by
      have hcont := hs.localInverse_continuousAt
      have hval : hs.localInverse Φ e (G z) (Φ (G z)) = G z := hs.localInverse_apply_image
      exact hcont.preimage_mem_nhds (by rw [hval]; exact hTo.mem_nhds (hGT z))
    rw [hGe z] at hgc h1 h2
    have hcomp := hgc.comp z hf.contDiffAt
    refine hcomp.congr_of_eventuallyEq ?_
    have h3 := (hfc.tendsto z).eventually (h1.and h2)
    filter_upwards [h3] with z' hz'
    exact hGu z' _ hz'.2 hz'.1
  set ψ₀ : ℂ → ℂ := fun z => (G z).1 with hψ₀
  set v : ℂ → ℂ := fun z => (G z).2 with hv
  have hψ₀s : ContDiff ℝ ∞ ψ₀ := contDiff_fst.comp hGs
  have hvs : ContDiff ℝ ∞ v := contDiff_snd.comp hGs
  have hvb : ∀ z, ‖v z‖ ≤ 2 * ε / c := fun z => (hsmall z (G z) (hGT z) (hGe z)).2
  have hXb : ∀ z, ‖ψ₀ z - z‖ / (1 + ‖ψ₀ z‖ + ‖z‖) ≤ 2 * ε / c :=
    fun z => (hsmall z (G z) (hGT z) (hGe z)).1
  -- derivative estimates
  have hGd : ∀ z, DifferentiableAt ℝ G z := fun z => hGs.differentiable (by simp) z
  have hderiv : ∀ z, (∀ h : ℂ, ‖fderiv ℝ ψ₀ z h - h‖ ≤ 1 / 2 * ‖h‖) ∧
      ∀ h : ℂ, ‖fderiv ℝ v z h‖ ≤ 1 / 4 * (‖h‖ / (1 + ‖z‖)) := by
    intro z
    have hX := hXb z
    have hY := hvb z
    have har := arith hc hc₁ hC'0 hε0 hε1 hε2 hε4 (by positivity) (norm_nonneg _) hX hY
    set K := 2 / c₁ * (ε + 16 * C' * (‖ψ₀ z - z‖ / (1 + ‖ψ₀ z‖ + ‖z‖)) + 2 * C' * ‖v z‖)
    have hGTc : G z ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρc := by
      refine ⟨Set.mem_univ _, mem_ball_zero_iff.2 ?_⟩
      have : m ≤ ρc := min_le_right _ _
      have := hvb z
      simp only [v] at this
      linarith
    have hFd : DifferentiableAt ℝ F (G z) :=
      (hFsm.contDiffAt ((isOpen_univ.prod isOpen_ball).mem_nhds hGTc)).differentiableAt (by simp)
    -- F ∘ G = Ψ ∘ f
    have hfa : DifferentiableAt ℝ (fun x => aCoord H (f x)) z :=
      ((contDiffAt_aCoord_proj H hH (f z) (hf0 z)).1.differentiableAt (by simp)).comp z
        (hf.differentiable (by simp) z)
    have hfp : DifferentiableAt ℝ (fun x => proj H (f x)) z :=
      ((contDiffAt_aCoord_proj H hH (f z) (hf0 z)).2.differentiableAt (by simp)).comp z
        (hf.differentiable (by simp) z)
    have hua : DifferentiableAt ℝ (fun x => aCoord H (u x)) z :=
      ((contDiffAt_aCoord_proj H hH (u z) (hu0 z)).1.differentiableAt (by simp)).comp z
        (hu.differentiable (by simp) z)
    have hup : DifferentiableAt ℝ (fun x => proj H (u x)) z :=
      ((contDiffAt_aCoord_proj H hH (u z) (hu0 z)).2.differentiableAt (by simp)).comp z
        (hu.differentiable (by simp) z)
    have eFG : (F ∘ G) = fun x => (aCoord H (f x), proj H (f x)) := by
      funext x; simp only [Function.comp, F, hGe x]
    have hDf : (fderiv ℝ F (G z)).comp (fderiv ℝ G z) =
        (fderiv ℝ (fun x => aCoord H (f x)) z).prod (fderiv ℝ (fun x => proj H (f x)) z) := by
      rw [← fderiv_comp z hFd (hGd z), eFG, DifferentiableAt.fderiv_prodMk hfa hfp]
    have hT0 : (z, (0 : ℂ)) ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρc :=
      ⟨Set.mem_univ _, by simp [hρc]⟩
    have hFd0 : DifferentiableAt ℝ F (z, 0) :=
      (hFsm.contDiffAt ((isOpen_univ.prod isOpen_ball).mem_nhds hT0)).differentiableAt (by simp)
    have hi : HasFDerivAt (fun x : ℂ => (x, (0 : ℂ)))
        ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℂ)) z :=
      (hasFDerivAt_id z).prodMk (hasFDerivAt_const 0 z)
    have eFu : (F ∘ fun x : ℂ => (x, (0 : ℂ))) = fun x => (aCoord H (u x), proj H (u x)) := by
      funext x; simp only [Function.comp, F, hΦ0 x]
    have hDu : (fderiv ℝ F (z, 0)).comp ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℂ)) =
        (fderiv ℝ (fun x => aCoord H (u x)) z).prod (fderiv ℝ (fun x => proj H (u x)) z) := by
      rw [← (hFd0.hasFDerivAt.comp z hi).fderiv, eFu, DifferentiableAt.fderiv_prodMk hua hup]
    have hL : ∀ h : ℂ, ‖fderiv ℝ F ((G z).1, (G z).2) (fderiv ℝ G z h) -
        fderiv ℝ F (z, 0) (h, 0)‖ ≤ ε * (‖h‖ / (1 + ‖z‖)) := by
      intro h
      have e1 : fderiv ℝ F ((G z).1, (G z).2) (fderiv ℝ G z h) =
          (fderiv ℝ (fun x => aCoord H (f x)) z h, fderiv ℝ (fun x => proj H (f x)) z h) := by
        have := congrArg (fun L : ℂ →L[ℝ] ℝ × V 1 => L h) hDf
        simpa using this
      have e2 : fderiv ℝ F (z, 0) (h, 0) =
          (fderiv ℝ (fun x => aCoord H (u x)) z h, fderiv ℝ (fun x => proj H (u x)) z h) := by
        have := congrArg (fun L : ℂ →L[ℝ] ℝ × V 1 => L h) hDu
        simpa using this
      rw [e1, e2, Prod.mk_sub_mk, Prod.norm_mk]
      have hcz := (hclose z).2.2
      set A := fderiv ℝ (fun x => aCoord H (f x)) z - fderiv ℝ (fun x => aCoord H (u x)) z
      set B := fderiv ℝ (fun x => proj H (f x)) z - fderiv ℝ (fun x => proj H (u x)) z
      have hA : ‖fderiv ℝ (fun x => aCoord H (f x)) z h - fderiv ℝ (fun x => aCoord H (u x)) z h‖
          ≤ ‖A‖ * ‖h‖ := by
        have := A.le_opNorm h; simpa [A] using this
      have hB : ‖fderiv ℝ (fun x => proj H (f x)) z h - fderiv ℝ (fun x => proj H (u x)) z h‖
          ≤ ‖B‖ * ‖h‖ := by
        have := B.le_opNorm h; simpa [B] using this
      have hz1 : 0 < 1 + ‖z‖ := by positivity
      have hAB : (‖A‖ + ‖B‖) * ‖h‖ ≤ ε * (‖h‖ / (1 + ‖z‖)) := by
        rw [mul_div_assoc', le_div_iff₀ hz1]
        have : (1 + ‖z‖) * (‖A‖ + ‖B‖) ≤ ε := hcz
        nlinarith [norm_nonneg h]
      refine (max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)).trans ?_
      nlinarith [norm_nonneg A, norm_nonneg B, norm_nonneg h]
    have hX' : ‖z - (G z).1‖ ≤ 1 / 4 * (1 + ‖z‖ + ‖(G z).1‖) := by
      have h1 := hX.trans h2ec
      simp only [ψ₀] at h1
      rw [div_le_iff₀ (by positivity), norm_sub_rev] at h1
      linarith
    have hw' : ‖(G z).2‖ ≤ ρc / 2 := by
      have : m ≤ ρc := min_le_right _ _
      have := hvb z; simp only [v] at this; linarith
    have hwc : C' * ‖(G z).2‖ ≤ c₁ / 2 := har.2.1
    have key := fun h => weighted_norm_sub_inl_le_of_cylBounds (F := F) hFsm (by linarith)
      (by linarith) hC2 hC'0 hc₁ hlow1 hX' hw' hwc (fderiv ℝ G z) hL h
    have hψd : fderiv ℝ ψ₀ z = (ContinuousLinearMap.fst ℝ ℂ ℂ).comp (fderiv ℝ G z) :=
      (hGd z).hasFDerivAt.fst.fderiv
    have hvd : fderiv ℝ v z = (ContinuousLinearMap.snd ℝ ℂ ℂ).comp (fderiv ℝ G z) :=
      (hGd z).hasFDerivAt.snd.fderiv
    have hK : 2 / c₁ * (ε + 16 * C' * (‖z - (G z).1‖ / (1 + ‖z‖ + ‖(G z).1‖)) +
        2 * C' * ‖(G z).2‖) ≤ 1 / 4 := by
      have e : ‖z - (G z).1‖ / (1 + ‖z‖ + ‖(G z).1‖) =
          ‖ψ₀ z - z‖ / (1 + ‖ψ₀ z‖ + ‖z‖) := by
        simp only [ψ₀]; rw [norm_sub_rev, add_assoc, add_comm ‖z‖, ← add_assoc]
      rw [e]; exact har.1
    have hK0 : 0 ≤ 2 / c₁ * (ε + 16 * C' * (‖z - (G z).1‖ / (1 + ‖z‖ + ‖(G z).1‖)) +
        2 * C' * ‖(G z).2‖) := by positivity
    have hr : 1 + ‖(G z).1‖ ≤ 2 * (1 + ‖z‖) := by
      have h1 := hX.trans h2ec
      simp only [ψ₀] at h1
      have := (norm_le_of_X h1).1
      linarith
    constructor
    · intro h
      have k := key h
      rw [hψd]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.coe_fst']
      have hk1 : ‖(fderiv ℝ G z h).1 - h‖ / (1 + ‖(G z).1‖) ≤
          2 / c₁ * (ε + 16 * C' * (‖z - (G z).1‖ / (1 + ‖z‖ + ‖(G z).1‖)) +
            2 * C' * ‖(G z).2‖) * (‖h‖ / (1 + ‖z‖)) := by
        have : 0 ≤ ‖(fderiv ℝ G z h).2‖ := norm_nonneg _
        linarith
      exact arith_psi hK hK0 (norm_nonneg _) (norm_nonneg _) hr (norm_nonneg _) hk1
    · intro h
      have k := key h
      rw [hvd]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.coe_snd']
      have : 0 ≤ ‖(fderiv ℝ G z h).1 - h‖ / (1 + ‖(G z).1‖) := by positivity
      have h4 : 0 ≤ ‖h‖ / (1 + ‖z‖) := by positivity
      nlinarith
  have hDψ₀ : ∀ z, ‖fderiv ℝ ψ₀ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2 := fun z =>
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun h => by
      simpa using (hderiv z).1 h
  obtain ⟨e, hecoe, hes⟩ := exists_homeomorph_of_norm_fderiv_sub_id_le ψ₀ hψ₀s hDψ₀
  refine ⟨e, v, by rw [hecoe]; exact hψ₀s, hes, hvs, ?_, ?_, ?_, ?_⟩
  · intro z
    have : m ≤ ρ := min_le_left _ _
    have := hvb z
    linarith
  · intro z
    rw [hecoe]
    exact (hGe z).symm
  · intro z; rw [hecoe]; exact hDψ₀ z
  · intro z
    have hz1 : 0 < 1 + ‖z‖ := by positivity
    have hb' : ‖fderiv ℝ v z‖ ≤ 1 / 4 / (1 + ‖z‖) :=
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => by
        have := (hderiv z).2 h
        calc ‖fderiv ℝ v z h‖ ≤ 1 / 4 * (‖h‖ / (1 + ‖z‖)) := this
          _ = 1 / 4 / (1 + ‖z‖) * ‖h‖ := by ring
    rw [le_div_iff₀ hz1] at hb'
    linarith

end DGA2

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 < c)
    (hΦ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p))
    (hlow : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, ∀ q ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      c * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤
        |aCoord H (u p.1 + N p.1 p.2) - aCoord H (u q.1 + N q.1 q.2)| +
          ‖proj H (u p.1 + N p.1 p.2) - proj H (u q.1 + N q.1 q.2)‖) :
    ∃ ε > 0, ∀ f : ℂ → V 1, ContDiff ℝ ∞ f → (∀ z, f z ≠ 0) → IsCylCloseTo H ε f u →
      ∃ (ψ : ℂ ≃ₜ ℂ) (v : ℂ → ℂ), ContDiff ℝ ∞ ψ ∧ ContDiff ℝ ∞ ψ.symm ∧ ContDiff ℝ ∞ v ∧
        (∀ z, ‖v z‖ ≤ ρ / 2) ∧ (∀ z, f z = u (ψ z) + N (ψ z) (v z)) ∧
        (∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2) ∧
        (∀ z, (1 + ‖z‖) * ‖fderiv ℝ v z‖ ≤ 1) :=
  DGA2.exists_tubeCoords_of_isCylCloseTo_aux H hH J hJ P u hu hu0 d b hb ha hw N hN hNinj M hM hNM ρ c hρ hc hΦ hlow
