-- Prove2me | solution 1 for DissipativePrep.Unique.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:22:08.125007+00:00
-- url     : https://prove2.me/submissions/cb560940-4356-43a2-98b9-213aba879d53

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DissipativePrep.Unique


lemma gksl_apply {d : ℕ} (D : LindbladData d) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    gkslGenerator D ρ = ∑ k, D.jump k * ρ * (D.jump k)ᴴ - driftK D * ρ - ρ * (driftK D)ᴴ := by
  simp [gkslGenerator, cpGenerator, sandwich, mul_assoc]

open scoped ComplexOrder in
lemma kill_of_zero {d m : ℕ} (ρ K : Matrix (Fin d) (Fin d) ℂ) (V : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef) (h : ∑ k, V k * ρ * (V k)ᴴ = K * ρ + ρ * Kᴴ) (u : Fin d → ℂ)
    (hu : star u ⬝ᵥ ((K * ρ + ρ * Kᴴ) *ᵥ u) = 0) : ∀ k, ρ *ᵥ ((V k)ᴴ *ᵥ u) = 0 := by
  have h1 : ∑ k, star ((V k)ᴴ *ᵥ u) ⬝ᵥ (ρ *ᵥ ((V k)ᴴ *ᵥ u)) = 0 := by
    rw [← h] at hu
    rw [← hu, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
    simp [Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.star_mulVec]
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hρ.dotProduct_mulVec_nonneg ((V k)ᴴ *ᵥ u))).1 h1
  intro k
  exact (hρ.dotProduct_mulVec_zero_iff _).1 (h2 k (Finset.mem_univ k))



lemma mem_dark_iff {d m : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (c : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (E : ℝ) (ψ : EuclideanSpace ℂ (Fin d)) :
    ψ ∈ darkSpace H c E ↔ (∀ l, c l *ᵥ WithLp.ofLp ψ = 0) ∧ H *ᵥ WithLp.ofLp ψ = (E : ℂ) • WithLp.ofLp ψ := by
  simp only [darkSpace, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    Matrix.toEuclideanLin_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun l => ?_, ?_⟩
    · have := congrArg WithLp.ofLp (h1 l); simpa using this
    · have := congrArg WithLp.ofLp h2; simpa [sub_eq_zero] using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun l => ?_, ?_⟩
    · ext i; simpa using congrFun (h1 l) i
    · ext i; simpa [sub_eq_zero] using congrFun h2 i

lemma mem_range_iff {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) (ψ : EuclideanSpace ℂ (Fin d)) :
    ψ ∈ densitySupport ρ ↔ ∃ w : Fin d → ℂ, WithLp.ofLp ψ = ρ *ᵥ w := by
  simp only [densitySupport, LinearMap.mem_range, Matrix.toEuclideanLin_apply]
  constructor
  · rintro ⟨w, rfl⟩; exact ⟨WithLp.ofLp w, rfl⟩
  · rintro ⟨w, h⟩; exact ⟨WithLp.toLp 2 w, by ext i; simp [h]⟩

lemma range_of_orth {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.IsHermitian) (x : Fin d → ℂ)
    (hx : ∀ v : Fin d → ℂ, ρ *ᵥ v = 0 → star v ⬝ᵥ x = 0) : ∃ w, x = ρ *ᵥ w := by
  have hT : (Matrix.toEuclideanLin ρ).IsSymmetric := Matrix.isHermitian_iff_isSymmetric.1 hρ
  have : WithLp.toLp 2 x ∈ (LinearMap.range (Matrix.toEuclideanLin ρ))ᗮᗮ := by
    rw [hT.orthogonal_range]
    rw [Submodule.mem_orthogonal]
    intro v hv
    have := hx (WithLp.ofLp v) (by
      have := congrArg WithLp.ofLp (LinearMap.mem_ker.1 hv)
      simpa [Matrix.toEuclideanLin_apply] using this)
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simpa [dotProduct_comm] using this
  rw [Submodule.orthogonal_orthogonal] at this
  have := (mem_range_iff ρ (WithLp.toLp 2 x)).1 this
  simpa using this


theorem theorem_2 {d m : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (c : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → ℝ) (hg : ∀ l, 0 < g l) (E : ℝ)
    (hD : ∀ (ψ : EuclideanSpace ℂ (Fin d)) (E' : ℝ), ψ ≠ 0 → (∀ l, act (c l) ψ = 0) →
      act H ψ = (E' : ℂ) • ψ → E' = E)
    (hS : ∀ S : Submodule ℂ (EuclideanSpace ℂ (Fin d)), lazy c S → ¬ S ≤ (darkSpace H c E)ᗮ) :
    ∀ ρ : Matrix (Fin d) (Fin d) ℂ, stationary (krausData H hH c g) ρ →
      densitySupport ρ ≤ darkSpace H c E := by
  intro ρ hst
  obtain ⟨⟨hρ, -⟩, hG⟩ := hst
  have hρH : ρ.IsHermitian := by
    open scoped ComplexOrder in exact hρ.isHermitian
  set V : Fin m → Matrix (Fin d) (Fin d) ℂ := fun k => ((Real.sqrt (2 * g k) : ℝ) : ℂ) • c k with hV
  set K : Matrix (Fin d) (Fin d) ℂ := Complex.I • H + (1 / 2 : ℂ) • ∑ k, (V k)ᴴ * V k with hK
  have hs : ∀ k, ((Real.sqrt (2 * g k) : ℝ) : ℂ) ≠ 0 := fun k => by
    have := hg k
    have : 0 < Real.sqrt (2 * g k) := Real.sqrt_pos.2 (by linarith)
    exact_mod_cast this.ne'
  have h : ∑ k, V k * ρ * (V k)ᴴ = K * ρ + ρ * Kᴴ := by
    have h0 : ∑ k, V k * ρ * (V k)ᴴ - K * ρ - ρ * Kᴴ = 0 := by
      have := hG
      rw [gksl_apply] at this
      exact this
    rw [sub_sub, sub_eq_zero] at h0
    exact h0
  have hkill : ∀ u : Fin d → ℂ, star u ⬝ᵥ ((K * ρ + ρ * Kᴴ) *ᵥ u) = 0 →
      ∀ k, ρ *ᵥ ((c k)ᴴ *ᵥ u) = 0 := by
    intro u hu k
    have := kill_of_zero ρ K V hρ h u hu k
    simp only [hV, Matrix.conjTranspose_smul, Matrix.smul_mulVec, Matrix.mulVec_smul] at this
    rcases smul_eq_zero.1 this with h0 | h0
    · exact absurd (by simpa using h0) (hs k)
    · exact h0
  have hz : ∀ v, ρ *ᵥ v = 0 → ∀ w, star v ⬝ᵥ (ρ *ᵥ w) = 0 := by
    intro v hv w
    rw [Matrix.dotProduct_mulVec]
    have := Matrix.star_mulVec ρᴴ v
    rw [Matrix.conjTranspose_conjTranspose, hρH.eq] at this
    rw [← this, hv]; simp
  -- (a)
  have ha : ∀ v, ρ *ᵥ v = 0 → ∀ k, ρ *ᵥ ((c k)ᴴ *ᵥ v) = 0 := by
    intro v hv
    apply hkill
    have h1 : (K * ρ) *ᵥ v = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    rw [Matrix.add_mulVec, h1, zero_add, ← Matrix.mulVec_mulVec]
    exact hz v hv _
  have hKc : Kᴴ = (-Complex.I) • H + (1 / 2 : ℂ) • ∑ k, (V k)ᴴ * V k := by
    simp [hK, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_mul, hH.eq]
  have hz' : ∀ k v, ρ *ᵥ ((c k)ᴴ *ᵥ v) = 0 → ∀ w, star v ⬝ᵥ (c k *ᵥ (ρ *ᵥ w)) = 0 := by
    intro k v hv w
    rw [Matrix.dotProduct_mulVec]
    have := Matrix.star_mulVec (c k)ᴴ v
    rw [Matrix.conjTranspose_conjTranspose] at this
    rw [← this]
    exact hz _ hv w
  have ha' : ∀ k w, ∃ w', c k *ᵥ (ρ *ᵥ w) = ρ *ᵥ w' := fun k w =>
    range_of_orth ρ hρH _ (fun v hv => hz' k v (ha v hv k) w)
  -- (b)
  have hb : ∀ dv : Fin d → ℂ, (∀ l, c l *ᵥ dv = 0) → H *ᵥ dv = (E : ℂ) • dv →
      ∀ k, ρ *ᵥ ((c k)ᴴ *ᵥ dv) = 0 := by
    intro dv hc hHd
    have hVd : ∀ k, V k *ᵥ dv = 0 := by
      intro k
      simp only [hV, Matrix.smul_mulVec, hc k, smul_zero]
    have hKd : Kᴴ *ᵥ dv = (-(Complex.I * (E : ℂ))) • dv := by
      rw [hKc, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hHd, Matrix.sum_mulVec]
      simp [← Matrix.mulVec_mulVec, hVd]
      ext i; simp [Complex.real_smul, mul_assoc]
    have e1 : star dv ⬝ᵥ (K *ᵥ (ρ *ᵥ dv)) = (Complex.I * (E : ℂ)) * (star dv ⬝ᵥ (ρ *ᵥ dv)) := by
      rw [Matrix.dotProduct_mulVec]
      have := Matrix.star_mulVec Kᴴ dv
      rw [Matrix.conjTranspose_conjTranspose, hKd] at this
      rw [← this]
      simp [star_smul, smul_dotProduct]
    apply hkill
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hKd, Matrix.mulVec_smul,
      dotProduct_add, e1]
    simp [dotProduct_smul]
  have hSinv : ∀ s ∈ densitySupport ρ, ∀ k, act (c k) s ∈ densitySupport ρ := by
    intro s hs k
    obtain ⟨w, hw⟩ := (mem_range_iff ρ s).1 hs
    obtain ⟨w', hw'⟩ := ha' k w
    refine (mem_range_iff ρ _).2 ⟨w', ?_⟩
    simp [act, hw, hw']
  have hSperp : ∀ s ∈ densitySupport ρ, ∀ k, act (c k) s ∈ (darkSpace H c E)ᗮ := by
    intro s hs k
    obtain ⟨w, hw⟩ := (mem_range_iff ρ s).1 hs
    rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨hcu, hHu⟩ := (mem_dark_iff H c E u).1 hu
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    have := hz' k (WithLp.ofLp u) (hb _ hcu hHu k) w
    simpa [act, hw] using this
  have hS1 : densitySupport ρ ⊓ (darkSpace H c E)ᗮ = ⊥ := by
    by_contra hne
    refine hS _ ⟨hne, ?_⟩ inf_le_right
    rintro X ⟨k, rfl⟩ v hv
    exact ⟨hSinv v hv.1 k, hSperp v hv.1 k⟩
  have hcS : ∀ s ∈ densitySupport ρ, ∀ k, c k *ᵥ WithLp.ofLp s = 0 := by
    intro s hs k
    have : act (c k) s ∈ densitySupport ρ ⊓ (darkSpace H c E)ᗮ := ⟨hSinv s hs k, hSperp s hs k⟩
    rw [hS1, Submodule.mem_bot] at this
    simpa [act] using congrArg WithLp.ofLp this
  have hcρ : ∀ k, c k * ρ = 0 := by
    intro k
    have hv : ∀ v, (c k * ρ) *ᵥ v = 0 := fun v => by
      rw [← Matrix.mulVec_mulVec]
      exact hcS (WithLp.toLp 2 (ρ *ᵥ v)) ((mem_range_iff ρ _).2 ⟨_, rfl⟩) k
    ext i j
    have := congrFun (hv (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at this
    exact this
  have hVρ : ∀ k, V k * ρ = 0 := fun k => by
    simp only [hV, Matrix.smul_mul, hcρ k, smul_zero]
  have hρV : ∀ k, ρ * (V k)ᴴ = 0 := fun k => by
    have := congrArg Matrix.conjTranspose (hVρ k)
    rw [Matrix.conjTranspose_mul, hρH.eq] at this
    simpa using this
  have hHρ : H * ρ = ρ * H := by
    have e1 : K * ρ = Complex.I • (H * ρ) := by
      simp [hK, add_mul, Finset.sum_mul, mul_assoc, hVρ]
    have e2 : ρ * Kᴴ = (-Complex.I) • (ρ * H) := by
      rw [hKc]
      simp [mul_add, Finset.mul_sum, ← mul_assoc, hρV]
    have e3 : ∑ k, V k * ρ * (V k)ᴴ = 0 := by simp [hVρ]
    rw [e1, e2, e3] at h
    have h4 : Complex.I • (H * ρ - ρ * H) = 0 := by
      rw [smul_sub]; rw [neg_smul] at h; rw [sub_eq_add_neg]; rw [← h]
    rcases smul_eq_zero.1 h4 with h5 | h5
    · exact absurd h5 Complex.I_ne_zero
    · exact sub_eq_zero.1 h5
  have hinv : ∀ s ∈ densitySupport ρ, Matrix.toEuclideanLin H s ∈ densitySupport ρ := by
    intro s hs
    obtain ⟨w, hw⟩ := (mem_range_iff ρ s).1 hs
    refine (mem_range_iff ρ _).2 ⟨H *ᵥ w, ?_⟩
    simp [Matrix.toEuclideanLin_apply, hw, Matrix.mulVec_mulVec, hHρ]
  have hT : (Matrix.toEuclideanLin H).IsSymmetric := Matrix.isHermitian_iff_isSymmetric.1 hH
  have hT' := hT.restrict_invariant hinv
  have hbD : ∀ i, (((hT'.eigenvectorBasis rfl) i : densitySupport ρ) : EuclideanSpace ℂ (Fin d)) ∈
      darkSpace H c E := by
    intro i
    set ψ : EuclideanSpace ℂ (Fin d) := (((hT'.eigenvectorBasis rfl) i : densitySupport ρ) : EuclideanSpace ℂ (Fin d)) with hψ
    have hψS : ψ ∈ densitySupport ρ := ((hT'.eigenvectorBasis rfl) i).2
    have hc : ∀ l, act (c l) ψ = 0 := fun l => by
      ext j; simpa [act] using congrFun (hcS ψ hψS l) j
    have hH' : act H ψ = ((hT'.eigenvalues rfl i : ℝ) : ℂ) • ψ := by
      have := congrArg Subtype.val (hT'.apply_eigenvectorBasis rfl i)
      simpa [act, Matrix.toEuclideanLin_apply, hψ] using this
    have hne : ψ ≠ 0 := by
      have := (hT'.eigenvectorBasis rfl).orthonormal.ne_zero i
      intro h0; apply this; exact Subtype.ext h0
    have hE := hD ψ _ hne hc hH'
    rw [mem_dark_iff]
    refine ⟨fun l => ?_, ?_⟩
    · simpa [act] using congrArg WithLp.ofLp (hc l)
    · have := congrArg WithLp.ofLp hH'
      rw [hE] at this
      simpa [act] using this
  intro x hx
  have hsum := (hT'.eigenvectorBasis rfl).sum_repr' (⟨x, hx⟩ : densitySupport ρ)
  have hx' := congrArg Subtype.val hsum
  have hx'' : x = _ := hx'.symm
  rw [hx'']
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hbD i))

end DissipativePrep.Unique

open DissipativePrep.Unique

theorem solution {d m : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (c : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → ℝ) (hg : ∀ l, 0 < g l) (E : ℝ)
    (hD : ∀ (ψ : EuclideanSpace ℂ (Fin d)) (E' : ℝ), ψ ≠ 0 → (∀ l, act (c l) ψ = 0) →
      act H ψ = (E' : ℂ) • ψ → E' = E)
    (hS : ∀ S : Submodule ℂ (EuclideanSpace ℂ (Fin d)), lazy c S → ¬ S ≤ (darkSpace H c E)ᗮ) :
    ∀ ρ : Matrix (Fin d) (Fin d) ℂ, stationary (krausData H hH c g) ρ →
      densitySupport ρ ≤ darkSpace H c E :=
  DissipativePrep.Unique.theorem_2 H hH c g hg E hD hS
