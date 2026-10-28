-- Prove2me | solution 1 for DissipativePrep.Unique.unique_attractive_stationary
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:58:04.383984+00:00
-- url     : https://prove2.me/submissions/ed19c8ec-49ff-4292-91ca-7d0d305f5961

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


lemma lowerQ_cond {n : ℕ} (k : Fin n) (x z : Qubits n) :
    (z k = true ∧ x = Function.update z k false) ↔ (x k = false ∧ z = Function.update x k true) := by
  constructor
  · rintro ⟨h1, rfl⟩
    refine ⟨by simp, ?_⟩
    ext j
    by_cases hj : j = k
    · subst hj; simp [h1]
    · simp [hj]
  · rintro ⟨h1, rfl⟩
    refine ⟨by simp, ?_⟩
    ext j
    by_cases hj : j = k
    · subst hj; simp [h1]
    · simp [hj]

lemma lowerQ_apply' {n : ℕ} (k : Fin n) (x z : Qubits n) :
    lowerQ k x z = if (x k = false ∧ z = Function.update x k true) then 1 else 0 := by
  simp only [lowerQ, Matrix.of_apply]
  exact if_congr (lowerQ_cond k x z) rfl rfl

lemma lowerQ_mul_apply {n : ℕ} (k : Fin n) (T : Matrix (Qubits n) (Qubits n) ℂ) (x y : Qubits n) :
    (lowerQ k * T) x y = if x k = false then T (Function.update x k true) y else 0 := by
  rw [Matrix.mul_apply]
  simp only [lowerQ_apply', ite_and, ite_mul, one_mul, zero_mul]
  by_cases hx : x k = false
  · simp [hx]
  · simp [hx]

lemma star_ite_one (p : Prop) [Decidable p] : star (if p then (1 : ℂ) else 0) = if p then 1 else 0 := by
  split_ifs <;> simp

lemma mul_lowerQ_conjT_apply {n : ℕ} (k : Fin n) (T : Matrix (Qubits n) (Qubits n) ℂ) (x y : Qubits n) :
    (T * (lowerQ k)ᴴ) x y = if y k = false then T x (Function.update y k true) else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, lowerQ_apply', ite_and, mul_ite, mul_one, mul_zero,
    star_ite_one]
  by_cases hy : y k = false
  · simp [hy]
  · simp [hy]

lemma lowerQ_cond' {n : ℕ} (k : Fin n) (x z : Qubits n) :
    (z k = false ∧ x = Function.update z k true) ↔ (x k = true ∧ z = Function.update x k false) := by
  constructor
  · rintro ⟨h1, rfl⟩
    refine ⟨by simp, ?_⟩
    ext j
    by_cases hj : j = k
    · subst hj; simp [h1]
    · simp [hj]
  · rintro ⟨h1, rfl⟩
    refine ⟨by simp, ?_⟩
    ext j
    by_cases hj : j = k
    · subst hj; simp [h1]
    · simp [hj]

lemma lowerQ_conjT_mul_self {n : ℕ} (k : Fin n) :
    (lowerQ k)ᴴ * lowerQ k = Matrix.diagonal (fun x : Qubits n => if x k = true then (1 : ℂ) else 0) := by
  ext x y
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, lowerQ_apply', lowerQ_cond', star_ite_one,
    Matrix.diagonal_apply]
  by_cases hx : x k = true
  · by_cases hy : y k = true
    · have hxy : Function.update x k false = Function.update y k false ↔ x = y := by
        constructor
        · intro h
          ext j
          by_cases hj : j = k
          · subst hj; simp [hx, hy]
          · simpa [Function.update_of_ne hj] using congrFun h j
        · rintro rfl; rfl
      simp only [hx, hy, true_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_and]
      simp [hx, hy, hxy, eq_comm (a := Function.update y k false)]
    · have : ∀ z : Qubits n, (if y k = true ∧ z = Function.update y k false then (1:ℂ) else 0) = 0 := by
        intro z; simp [hy]
      simp [hx, hy, this]
      intro h; subst h; exact absurd hx hy
  · have : ∀ z : Qubits n, (if x k = true ∧ z = Function.update x k false then (1:ℂ) else 0) = 0 := by
      intro z; simp [hx]
    simp [hx, this]

lemma loc_id (g : ℝ) (p : Fin 4) (x y : Bool) :
    2 * (g : ℂ) * (if x = false ∧ y = false then localEigenoperator p true true else 0)
      - (g : ℂ) * (if x = true then 1 else 0) * localEigenoperator p x y
      - localEigenoperator p x y * ((g : ℂ) * (if y = true then 1 else 0))
    = localEigenvalue g p * localEigenoperator p x y := by
  fin_cases p <;> cases x <;> cases y <;> simp [localEigenoperator, localEigenvalue] <;> ring

def Gq {n : ℕ} (g : Fin n → ℝ) (T : Matrix (Qubits n) (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ :=
  ∑ k, ((2 * g k : ℝ) : ℂ) • (lowerQ k * T * (lowerQ k)ᴴ)
    - (∑ k, ((g k : ℝ) : ℂ) • ((lowerQ k)ᴴ * lowerQ k)) * T
    - T * (∑ k, ((g k : ℝ) : ℂ) • ((lowerQ k)ᴴ * lowerQ k))ᴴ

lemma diag_sum_eq {n : ℕ} (g : Fin n → ℝ) :
    (∑ k, ((g k : ℝ) : ℂ) • ((lowerQ k)ᴴ * lowerQ k)) =
      Matrix.diagonal (fun x : Qubits n => ∑ k, ((g k : ℝ) : ℂ) * (if x k = true then 1 else 0)) := by
  ext x y
  simp only [lowerQ_conjT_mul_self, Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply]
  by_cases h : x = y
  · subst h; simp
  · simp [h]

lemma Gq_apply {n : ℕ} (g : Fin n → ℝ) (T : Matrix (Qubits n) (Qubits n) ℂ) (x y : Qubits n) :
    Gq g T x y = (∑ k, 2 * (g k : ℂ) * (if x k = false ∧ y k = false then
        T (Function.update x k true) (Function.update y k true) else 0))
      - (∑ k, (g k : ℂ) * (if x k = true then 1 else 0)) * T x y
      - T x y * (∑ k, (g k : ℂ) * (if y k = true then 1 else 0)) := by
  unfold Gq
  rw [diag_sum_eq, Matrix.diagonal_conjTranspose]
  simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_assoc, lowerQ_mul_apply, mul_lowerQ_conjT_apply]
    by_cases h1 : x k = false <;> by_cases h2 : y k = false <;> simp [h1, h2]
  · simp only [mul_eq_mul_left_iff]
    left
    simp only [Pi.star_apply, star_sum, star_mul']
    exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp

def Tq {n : ℕ} (i : Fin n → Fin 4) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun x y => ∏ k, localEigenoperator (i k) (x k) (y k)

lemma Gq_tensor {n : ℕ} (g : Fin n → ℝ) (i : Fin n → Fin 4) :
    Gq g (Tq i) = (∑ k, localEigenvalue (g k) (i k)) • Tq i := by
  ext x y
  rw [Gq_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hT : ∀ x y : Qubits n, Tq i x y = localEigenoperator (i k) (x k) (y k) *
      ∏ j ∈ Finset.univ.erase k, localEigenoperator (i j) (x j) (y j) := by
    intro x y
    simp only [Tq, Matrix.of_apply]
    rw [Finset.mul_prod_erase Finset.univ (fun j => localEigenoperator (i j) (x j) (y j)) (Finset.mem_univ k)]
  have hU : Tq i (Function.update x k true) (Function.update y k true) =
      localEigenoperator (i k) true true *
      ∏ j ∈ Finset.univ.erase k, localEigenoperator (i j) (x j) (y j) := by
    rw [hT]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    have : j ≠ k := Finset.ne_of_mem_erase hj
    simp [Function.update_of_ne this]
  rw [hU, hT x y]
  have := loc_id (g k) (i k) (x k) (y k)
  set R := ∏ j ∈ Finset.univ.erase k, localEigenoperator (i j) (x j) (y j)
  calc _ = R * (2 * (g k : ℂ) * (if x k = false ∧ y k = false then localEigenoperator (i k) true true else 0)
      - (g k : ℂ) * (if x k = true then 1 else 0) * localEigenoperator (i k) (x k) (y k)
      - localEigenoperator (i k) (x k) (y k) * ((g k : ℂ) * (if y k = true then 1 else 0))) := by
        by_cases h1 : x k = false <;> by_cases h2 : y k = false <;> simp [h1, h2] <;> ring
    _ = _ := by rw [this]; ring

lemma sqrt_coef {g : ℝ} (hg : 0 < g) :
    ((Real.sqrt (2 * g) : ℝ) : ℂ) * star ((Real.sqrt (2 * g) : ℝ) : ℂ) = ((2 * g : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by linarith)]

lemma gksl_one_reindex {n : ℕ} (g : Fin n → ℝ) (hg : ∀ k, 0 < g k)
    (T : Matrix (Qubits n) (Qubits n) ℂ) :
    gkslGenerator (prepData 1 g 0 Matrix.isHermitian_zero) (Matrix.reindex (bitsEquivFin n) (bitsEquivFin n) T)
      = Matrix.reindex (bitsEquivFin n) (bitsEquivFin n) (Gq g T) := by
  set φ := Matrix.reindexAlgEquiv ℂ ℂ (bitsEquivFin n) with hφ
  have hφ' : ∀ M, Matrix.reindex (bitsEquivFin n) (bitsEquivFin n) M = φ M := fun M => rfl
  have hφc : ∀ M, φ Mᴴ = (φ M)ᴴ := fun M => by
    rw [← hφ', ← hφ']; exact (Matrix.conjTranspose_reindex _ _ _).symm
  rw [gksl_apply, hφ' T, hφ' (Gq g T)]
  have hdr : (prepData 1 g 0 Matrix.isHermitian_zero).drift = 0 := rfl
  have g2 : ∀ k : Fin n, (prepData 1 g 0 Matrix.isHermitian_zero).jump k =
      ((Real.sqrt (2 * g k) : ℝ) : ℂ) • φ (lowerQ k) := fun k => by
    show ((Real.sqrt (2 * g k) : ℝ) : ℂ) • (1 * lower k * (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)ᴴ) = _
    rw [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul, ← hφ']
    rfl
  have s1 : ∀ τ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ,
      ∑ k, (prepData 1 g 0 Matrix.isHermitian_zero).jump k * τ * ((prepData 1 g 0 Matrix.isHermitian_zero).jump k)ᴴ
      = ∑ k : Fin n, ((2 * g k : ℝ) : ℂ) • (φ (lowerQ k) * τ * (φ (lowerQ k))ᴴ) := fun τ =>
    Finset.sum_congr rfl fun (k : Fin n) _ => by
      rw [g2 k]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.conjTranspose_smul, smul_smul]
      rw [mul_comm, sqrt_coef (hg k)]
  have g4 : driftK (prepData 1 g 0 Matrix.isHermitian_zero) =
      ∑ k : Fin n, ((g k : ℝ) : ℂ) • ((φ (lowerQ k))ᴴ * φ (lowerQ k)) := by
    rw [driftK, hdr, smul_zero, zero_add, Finset.smul_sum]
    refine Finset.sum_congr rfl fun (k : Fin n) _ => ?_
    rw [g2 k, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
    congr 1
    have := sqrt_coef (hg k)
    rw [Complex.star_def] at this ⊢
    have h2 : ((g k : ℝ) : ℂ) = (1 / 2 : ℂ) * ((2 * g k : ℝ) : ℂ) := by push_cast; ring
    rw [h2, ← this]; ring
  rw [s1, g4]
  simp only [Gq, map_sub, map_sum, map_smul, map_mul, hφc, map_smul]

noncomputable def dualOp (q : Fin 4) (x y : Bool) : ℂ :=
  if q = 0 then (if x = y then 1 else 0)
  else if q = 1 then (if x ≠ y then 1 / 2 else 0)
  else if q = 2 then
    (if x = false ∧ y = true then Complex.I / 2
     else if x = true ∧ y = false then -(Complex.I / 2) else 0)
  else (if x = true ∧ y = true then -1 else 0)

lemma dual_pair (p q : Fin 4) :
    ∑ x : Bool, ∑ y : Bool, dualOp q x y * localEigenoperator p x y = if p = q then 1 else 0 := by
  fin_cases p <;> fin_cases q <;> simp [Fintype.sum_bool, dualOp, localEigenoperator] <;> ring_nf <;> simp

lemma prod_pair_sum {n : ℕ} (F : Fin n → Bool → Bool → ℂ) :
    ∑ x : Qubits n, ∑ y : Qubits n, ∏ k, F k (x k) (y k) = ∏ k, ∑ u : Bool, ∑ v : Bool, F k u v := by
  have h1 : ∀ k, ∑ u : Bool, ∑ v : Bool, F k u v = ∑ w : Bool × Bool, F k w.1 w.2 := fun k => by
    rw [Fintype.sum_prod_type]
  simp_rw [h1]
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Bool × Bool))) (fun k w => F k w.1 w.2),
    Fintype.piFinset_univ]
  calc ∑ x : Qubits n, ∑ y : Qubits n, ∏ k, F k (x k) (y k)
      = ∑ z : Qubits n × Qubits n, ∏ k, F k (z.1 k) (z.2 k) := (Fintype.sum_prod_type' _).symm
    _ = _ := (Equiv.sum_comp (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Bool) (fun _ => Bool))
        (fun z : Qubits n × Qubits n => ∏ k, F k (z.1 k) (z.2 k))).symm

noncomputable def dualFun {n : ℕ} (j : Fin n → Fin 4) : Matrix (Qubits n) (Qubits n) ℂ →ₗ[ℂ] ℂ where
  toFun M := ∑ x : Qubits n, ∑ y : Qubits n, (∏ k, dualOp (j k) (x k) (y k)) * M x y
  map_add' M N := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c M := by simp [Finset.mul_sum, mul_left_comm, Finset.smul_sum]

lemma dualFun_Tq {n : ℕ} (j i : Fin n → Fin 4) :
    dualFun j (Tq i) = if i = j then 1 else 0 := by
  simp only [dualFun, LinearMap.coe_mk, AddHom.coe_mk, Tq, Matrix.of_apply]
  have : ∀ x y : Qubits n, (∏ k, dualOp (j k) (x k) (y k)) * ∏ k, localEigenoperator (i k) (x k) (y k)
      = ∏ k, (dualOp (j k) (x k) (y k) * localEigenoperator (i k) (x k) (y k)) := fun x y => by
    rw [Finset.prod_mul_distrib]
  simp only [this]
  rw [prod_pair_sum (fun k u v => dualOp (j k) u v * localEigenoperator (i k) u v)]
  simp only [dual_pair]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨k, hk⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

lemma Tq_linearIndependent {n : ℕ} : LinearIndependent ℂ (Tq (n := n)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have := congrArg (dualFun i) hc
  simp only [map_sum, map_smul, dualFun_Tq, map_zero] at this
  simpa using this

lemma conj_gen {d m : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (h1 : Uᴴ * U = 1) (h2 : U * Uᴴ = 1)
    (V : Fin m → Matrix (Fin d) (Fin d) ℂ) (σ : Matrix (Fin d) (Fin d) ℂ) :
    ∑ k, (U * V k * Uᴴ) * σ * (U * V k * Uᴴ)ᴴ
      - ((1 / 2 : ℂ) • ∑ k, (U * V k * Uᴴ)ᴴ * (U * V k * Uᴴ)) * σ
      - σ * ((1 / 2 : ℂ) • ∑ k, (U * V k * Uᴴ)ᴴ * (U * V k * Uᴴ))ᴴ
    = U * (∑ k, V k * (Uᴴ * σ * U) * (V k)ᴴ
      - ((1 / 2 : ℂ) • ∑ k, (V k)ᴴ * V k) * (Uᴴ * σ * U)
      - (Uᴴ * σ * U) * ((1 / 2 : ℂ) • ∑ k, (V k)ᴴ * V k)ᴴ) * Uᴴ := by
  have hK : ∀ k, (U * V k * Uᴴ)ᴴ * (U * V k * Uᴴ) = U * ((V k)ᴴ * V k) * Uᴴ := by
    intro k
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc U * ((V k)ᴴ * Uᴴ) * (U * V k * Uᴴ) = U * (V k)ᴴ * (Uᴴ * U) * V k * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp [Matrix.mul_assoc]
  set A : Matrix (Fin d) (Fin d) ℂ := (1 / 2 : ℂ) • ∑ k, (V k)ᴴ * V k with hA
  have hKU : (1 / 2 : ℂ) • ∑ k, (U * V k * Uᴴ)ᴴ * (U * V k * Uᴴ) = U * A * Uᴴ := by
    simp only [hK, hA, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
  have e1 : ∀ X, U * X * Uᴴ * σ = U * (X * (Uᴴ * σ * U)) * Uᴴ := fun X => by
    calc U * X * Uᴴ * σ = U * X * Uᴴ * σ * (U * Uᴴ) := by rw [h2, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have e2 : ∀ X, σ * (U * X * Uᴴ) = U * ((Uᴴ * σ * U) * X) * Uᴴ := fun X => by
    calc σ * (U * X * Uᴴ) = (U * Uᴴ) * σ * (U * X * Uᴴ) := by rw [h2, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  have e3 : ∑ k, (U * V k * Uᴴ) * σ * (U * V k * Uᴴ)ᴴ
      = U * (∑ k, V k * (Uᴴ * σ * U) * (V k)ᴴ) * Uᴴ := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hAhh : (U * A * Uᴴ)ᴴ = U * Aᴴ * Uᴴ := by
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hKU, e3, e1, hAhh, e2]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

lemma gksl_prep_eq {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (g : Fin n → ℝ)
    (σ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    gkslGenerator (prepData U g 0 Matrix.isHermitian_zero) σ =
      U * gkslGenerator (prepData 1 g 0 Matrix.isHermitian_zero) (Uᴴ * σ * U) * Uᴴ := by
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have h2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  rw [gksl_apply, gksl_apply]
  have key := conj_gen U h1 h2 (fun k : Fin n => ((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) σ
  have e0 : ∀ k : Fin n, ((Real.sqrt (2 * g k) : ℝ) : ℂ) • (U * lower k * Uᴴ) =
      U * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * Uᴴ := fun k => by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have e1 : ∀ k : Fin n, ((Real.sqrt (2 * g k) : ℝ) : ℂ) • (1 * lower k * (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)ᴴ) =
      ((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k := fun k => by
    rw [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul]
  have g1 : ∀ k : Fin n, (prepData U g 0 Matrix.isHermitian_zero).jump k =
      U * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * Uᴴ := fun k => by
    show ((Real.sqrt (2 * g k) : ℝ) : ℂ) • (U * lower k * Uᴴ) = _
    exact e0 k
  have g2 : ∀ k : Fin n, (prepData 1 g 0 Matrix.isHermitian_zero).jump k =
      ((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k := fun k => by
    show ((Real.sqrt (2 * g k) : ℝ) : ℂ) • (1 * lower k * (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)ᴴ) = _
    exact e1 k
  have hdr : (prepData U g 0 Matrix.isHermitian_zero).drift = 0 := rfl
  have hdr1 : (prepData 1 g 0 Matrix.isHermitian_zero).drift = 0 := rfl
  have g3 : driftK (prepData U g 0 Matrix.isHermitian_zero) = (1 / 2 : ℂ) • ∑ k : Fin n,
      (U * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * Uᴴ)ᴴ *
        (U * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * Uᴴ) := by
    rw [driftK, hdr, smul_zero, zero_add]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [g1 k]
  have g4 : driftK (prepData 1 g 0 Matrix.isHermitian_zero) = (1 / 2 : ℂ) • ∑ k : Fin n,
      (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k)ᴴ * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) := by
    rw [driftK, hdr1, smul_zero, zero_add]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [g2 k]
  have s1 : ∀ τ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ,
      ∑ k, (prepData U g 0 Matrix.isHermitian_zero).jump k * τ * ((prepData U g 0 Matrix.isHermitian_zero).jump k)ᴴ
      = ∑ k : Fin n, (U * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * Uᴴ) * τ *
          (U * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * Uᴴ)ᴴ := fun τ =>
    Finset.sum_congr rfl fun k _ => by rw [g1 k]
  have s2 : ∀ τ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ,
      ∑ k, (prepData 1 g 0 Matrix.isHermitian_zero).jump k * τ * ((prepData 1 g 0 Matrix.isHermitian_zero).jump k)ᴴ
      = ∑ k : Fin n, (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * τ *
          (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k)ᴴ := fun τ =>
    Finset.sum_congr rfl fun k _ => by rw [g2 k]
  rw [s1, s2, g3, g4]
  exact key

lemma lev_cnt (g : ℝ) (p : Fin 4) :
    localEigenvalue g p = -((((![0, 1, 1, 2] : Fin 4 → Fin 3) p : Fin 3) : ℕ) : ℂ) * (g : ℂ) := by
  fin_cases p <;> simp [localEigenvalue]

lemma eig_tensor {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (g : Fin n → ℝ) (hg : ∀ k, 0 < g k)
    (i : Fin n → Fin 4) :
    gkslGenerator (prepData U g 0 Matrix.isHermitian_zero) (U * tensorEigenoperator i * Uᴴ) =
      (∑ k, localEigenvalue (g k) (i k)) • (U * tensorEigenoperator i * Uᴴ) := by
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have h2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  rw [gksl_prep_eq U hU g]
  have e : Uᴴ * (U * tensorEigenoperator i * Uᴴ) * U = tensorEigenoperator i := by
    calc Uᴴ * (U * tensorEigenoperator i * Uᴴ) * U = (Uᴴ * U) * tensorEigenoperator i * (Uᴴ * U) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  rw [e]
  have : gkslGenerator (prepData 1 g 0 Matrix.isHermitian_zero) (tensorEigenoperator i) =
      (∑ k, localEigenvalue (g k) (i k)) • tensorEigenoperator i := by
    have h := gksl_one_reindex g hg (Tq i)
    rw [Gq_tensor] at h
    exact h
  rw [this]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem product_spectrum {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (g : Fin n → ℝ) (hg : ∀ k, 0 < g k) :
    let G := gkslGenerator (prepData U g 0 Matrix.isHermitian_zero)
    let σ := fun i : Fin n → Fin 4 => U * tensorEigenoperator i * Uᴴ
    (∀ i, G (σ i) = (∑ k, localEigenvalue (g k) (i k)) • σ i) ∧
    LinearIndependent ℂ σ ∧
    Submodule.span ℂ (Set.range σ) = ⊤ ∧
    (∀ μ : ℂ, G.HasEigenvalue μ ↔
      ∃ m : Fin n → Fin 3, μ = -(∑ k, ((m k : ℕ) : ℂ) * (g k : ℂ))) := by
  intro G σ
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have h2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have hEig : ∀ i, G (σ i) = (∑ k, localEigenvalue (g k) (i k)) • σ i := fun i => eig_tensor U hU g hg i
  -- linear independence
  have conj_inj : ∀ A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ, U * A * Uᴴ = U * B * Uᴴ → A = B := by
    intro A B h
    have key : ∀ A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ, A = Uᴴ * (U * A * Uᴴ) * U := fun A => by
      calc A = (Uᴴ * U) * A * (Uᴴ * U) := by rw [h1]; simp
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [key A, key B, h]
  let φ := Matrix.reindexAlgEquiv ℂ ℂ (bitsEquivFin n)
  let f : Matrix (Qubits n) (Qubits n) ℂ →ₗ[ℂ] Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
    { toFun := fun X => U * φ X * Uᴴ
      map_add' := fun X Y => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by simp [Matrix.mul_smul, Matrix.smul_mul] }
  have hf : Function.Injective f := by
    intro X Y hXY
    exact φ.injective (conj_inj _ _ hXY)
  have hli : LinearIndependent ℂ σ := by
    have := Tq_linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf)
    exact this
  have hspan : Submodule.span ℂ (Set.range σ) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [Module.finrank_matrix, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      Module.finrank_self, mul_one, Fintype.card_fin, ← mul_pow]
    norm_num
  refine ⟨hEig, hli, hspan, fun μ => ?_⟩
  constructor
  · intro hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hvmem : v ∈ Submodule.span ℂ (Set.range σ) := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hvmem
    have hGv : G v = μ • v := by
      have := hv.apply_eq_smul
      exact this
    have hzero : ∑ i, (c i * (∑ k, localEigenvalue (g k) (i k)) - μ * c i) • σ i = 0 := by
      have e1 : G v = ∑ i, (c i * (∑ k, localEigenvalue (g k) (i k))) • σ i := by
        rw [← hc, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hEig, smul_smul]
      have e2 : μ • v = ∑ i, (μ * c i) • σ i := by
        rw [← hc, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]
      have e3 : ∑ i, (c i * (∑ k, localEigenvalue (g k) (i k))) • σ i = ∑ i, (μ * c i) • σ i := by
        rw [← e1, hGv, e2]
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [e3, sub_self]
    have hcz := Fintype.linearIndependent_iff.1 hli _ hzero
    have hne : ∃ i, c i ≠ 0 := by
      by_contra hall
      apply hv.2
      rw [← hc]
      have : ∀ i, c i = 0 := fun i => by
        by_contra h
        exact hall ⟨i, h⟩
      simp [this]
    obtain ⟨i, hi⟩ := hne
    have := hcz i
    have hμi : μ = ∑ k, localEigenvalue (g k) (i k) := by
      have h3 : c i * ((∑ k, localEigenvalue (g k) (i k)) - μ) = 0 := by linear_combination this
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h hi
      · exact (sub_eq_zero.1 h).symm
    refine ⟨fun k => (![0, 1, 1, 2] : Fin 4 → Fin 3) (i k), ?_⟩
    rw [hμi]
    simp only [lev_cnt]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  · rintro ⟨m, rfl⟩
    have hsurj : ∀ q : Fin 3, ∃ p : Fin 4, (![0, 1, 1, 2] : Fin 4 → Fin 3) p = q := by
      intro q; fin_cases q
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩
    choose p hp using hsurj
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := σ (fun k => p (m k))) ⟨?_, hli.ne_zero _⟩
    · rw [Module.End.mem_eigenspace_iff, hEig]
      congr 1
      simp only [lev_cnt, hp]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring

lemma bits_zero (n : ℕ) : bitsEquivFin n (fun _ => false) = 0 := by
  apply Fin.ext
  simp [bitsEquivFin, finFunctionFinEquiv, Equiv.arrowCongr]
  intro i; rfl

lemma lowerQ_mulVec {n : ℕ} (k : Fin n) (v : Qubits n → ℂ) (x : Qubits n) :
    (lowerQ k *ᵥ v) x = if x k = false then v (Function.update x k true) else 0 := by
  simp only [Matrix.mulVec, dotProduct, lowerQ_apply', ite_and, ite_mul, one_mul, zero_mul]
  by_cases hx : x k = false
  · simp [hx]
  · simp [hx]

lemma lower_mulVec {n : ℕ} (k : Fin n) (φ : Fin (2 ^ n) → ℂ) (x : Qubits n) :
    (lower k *ᵥ φ) (bitsEquivFin n x) = (lowerQ k *ᵥ (fun z => φ (bitsEquivFin n z))) x := by
  simp only [lower, Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  exact Fintype.sum_equiv (bitsEquivFin n).symm _ _ (fun j => by simp)

lemma ker_lowering {n : ℕ} (φ : Fin (2 ^ n) → ℂ) (h : ∀ k, lower k *ᵥ φ = 0) :
    ∀ j, j ≠ 0 → φ j = 0 := by
  intro j hj
  obtain ⟨z, rfl⟩ := (bitsEquivFin n).surjective j
  have : ∃ k, z k = true := by
    by_contra hall
    apply hj
    rw [← bits_zero n]
    congr 1
    funext k
    by_cases hzk : z k = true
    · exact absurd ⟨k, hzk⟩ hall
    · simpa using hzk
  obtain ⟨k, hk⟩ := this
  have h1 := lower_mulVec k φ (Function.update z k false)
  rw [h k, lowerQ_mulVec] at h1
  simp only [Pi.zero_apply, Function.update_self, Function.update_idem, if_true] at h1
  have h2 : Function.update z k true = z := by
    rw [← hk]; exact Function.update_eq_self k z
  rw [h2] at h1
  exact h1.symm

lemma vec_eq_single {n : ℕ} (φ : Fin (2 ^ n) → ℂ) (h : ∀ j, j ≠ 0 → φ j = 0) :
    φ = φ 0 • (Pi.single 0 1 : Fin (2 ^ n) → ℂ) := by
  funext j
  by_cases hj : j = 0
  · subst hj; simp
  · simp [h j hj, hj]

lemma target_ofLp {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    WithLp.ofLp (target U) = U *ᵥ (Pi.single 0 1 : Fin (2 ^ n) → ℂ) := by
  simp [target, act, ket]

lemma star_target {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    star (WithLp.ofLp (target U)) ⬝ᵥ WithLp.ofLp (target U) = 1 := by
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  rw [target_ofLp, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h1,
    Matrix.vecMul_one]
  simp

lemma dark_vec_eq {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (ψ : Fin (2 ^ n) → ℂ)
    (h : ∀ k, jumpOps U k *ᵥ ψ = 0) :
    ψ = (Uᴴ *ᵥ ψ) 0 • (U *ᵥ (Pi.single 0 1 : Fin (2 ^ n) → ℂ)) := by
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have h2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have hk : ∀ k, lower k *ᵥ (Uᴴ *ᵥ ψ) = 0 := by
    intro k
    have : Uᴴ *ᵥ (jumpOps U k *ᵥ ψ) = 0 := by rw [h k, Matrix.mulVec_zero]
    rw [Matrix.mulVec_mulVec] at this
    have e : Uᴴ * jumpOps U k = lower k * Uᴴ := by
      simp only [jumpOps]
      calc Uᴴ * (U * lower k * Uᴴ) = (Uᴴ * U) * lower k * Uᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.one_mul]
    rw [e, ← Matrix.mulVec_mulVec] at this
    exact this
  have hz := vec_eq_single _ (ker_lowering _ hk)
  have : ψ = U *ᵥ (Uᴴ *ᵥ ψ) := by rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  conv_lhs => rw [this, hz]
  rw [Matrix.mulVec_smul]

def bitWeight {n : ℕ} (y : Qubits n) : ℕ := (Finset.univ.filter (fun j => y j = true)).card

lemma bitWeight_update {n : ℕ} (y : Qubits n) (k : Fin n) (hk : y k = false) :
    bitWeight (Function.update y k true) = bitWeight y + 1 := by
  unfold bitWeight
  have : Finset.univ.filter (fun j => Function.update y k true j = true) =
      insert k (Finset.univ.filter (fun j => y j = true)) := by
    ext j
    by_cases hj : j = k
    · subst hj; simp
    · simp [hj, Function.update_of_ne hj]
  rw [this, Finset.card_insert_of_notMem]
  simp [hk]

lemma lowering_induction {n : ℕ} (P : (Qubits n → ℂ) → Prop)
    (hsm : ∀ (c : ℂ) w, P w → P (c • w)) (hlow : ∀ k w, P w → P (lowerQ k *ᵥ w)) :
    ∀ (r : ℕ) (w : Qubits n → ℂ), P w → w ≠ 0 → (∀ y, w y ≠ 0 → bitWeight y ≤ r) →
      P (Pi.single (fun _ => false) 1) := by
  intro r
  induction r with
  | zero =>
    intro w hw hne hb
    have h0 : ∀ y, y ≠ (fun _ => false) → w y = 0 := by
      intro y hy
      by_contra hwy
      have := hb y hwy
      apply hy
      funext j
      by_contra hj
      have hj' : y j = true := by simpa using hj
      have : 0 < bitWeight y := Finset.card_pos.2 ⟨j, by simp [hj']⟩
      omega
    obtain ⟨c, hcdef⟩ : ∃ c, c = w (fun _ => false) := ⟨_, rfl⟩
    have hw' : w = c • (Pi.single (fun _ => false) 1 : Qubits n → ℂ) := by
      funext y
      by_cases hy : y = (fun _ => false)
      · subst hy; simp [hcdef]
      · simp [h0 y hy, hy]
    have hc : c ≠ 0 := by
      intro h; apply hne; rw [hw', h, zero_smul]
    have := hsm c⁻¹ w hw
    rw [hw', smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    exact this
  | succ r ih =>
    intro w hw hne hb
    by_cases hall : ∀ y, w y ≠ 0 → bitWeight y ≤ r
    · exact ih w hw hne hall
    · push Not at hall
      obtain ⟨x, hx, hxr⟩ := hall
      have hxw : bitWeight x = r + 1 := le_antisymm (hb x hx) hxr
      obtain ⟨k, hk⟩ : ∃ k, x k = true := by
        by_contra hnone
        have : bitWeight x = 0 := by
          unfold bitWeight
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro j _ hj
          exact hnone ⟨j, hj⟩
        omega
      refine ih (lowerQ k *ᵥ w) (hlow k w hw) ?_ ?_
      · intro h0
        have := congrFun h0 (Function.update x k false)
        rw [lowerQ_mulVec] at this
        simp only [Function.update_self, Function.update_idem, if_true, Pi.zero_apply] at this
        have h2 : Function.update x k true = x := by
          rw [← hk]; exact Function.update_eq_self k x
        rw [h2] at this
        exact hx this
      · intro y hy
        rw [lowerQ_mulVec] at hy
        by_cases hyk : y k = false
        · rw [if_pos hyk] at hy
          have := hb _ hy
          rw [bitWeight_update y k hyk] at this
          omega
        · rw [if_neg hyk] at hy
          exact absurd rfl hy

lemma lazy_target {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin (2 ^ n)))) (hS : lazy (jumpOps U) S) :
    target U ∈ S := by
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have h2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  obtain ⟨hne, hinv⟩ := hS
  obtain ⟨v, hvS, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  let P : (Qubits n → ℂ) → Prop := fun w =>
    (WithLp.toLp 2 (U *ᵥ (fun j => w ((bitsEquivFin n).symm j))) : EuclideanSpace ℂ (Fin (2 ^ n))) ∈ S
  have hsm : ∀ (c : ℂ) (w : Qubits n → ℂ), P w → P (c • w) := by
    intro c w hw
    have := S.smul_mem c hw
    have e1 : (fun j => (c • w) ((bitsEquivFin n).symm j)) = c • (fun j => w ((bitsEquivFin n).symm j)) := rfl
    show (WithLp.toLp 2 (U *ᵥ (fun j => (c • w) ((bitsEquivFin n).symm j))) : EuclideanSpace ℂ (Fin (2 ^ n))) ∈ S
    rw [e1, Matrix.mulVec_smul]
    exact this
  have hlow : ∀ (k : Fin n) (w : Qubits n → ℂ), P w → P (lowerQ k *ᵥ w) := by
    intro k w hw
    have hact := hinv (jumpOps U k) ⟨k, rfl⟩ _ hw
    have e1 : (fun j => (lowerQ k *ᵥ w) ((bitsEquivFin n).symm j)) = lower k *ᵥ (fun j => w ((bitsEquivFin n).symm j)) := by
      funext j
      have h := lower_mulVec k (fun j => w ((bitsEquivFin n).symm j)) ((bitsEquivFin n).symm j)
      simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] at h
      exact h.symm
    have key : jumpOps U k *ᵥ (U *ᵥ (fun j => w ((bitsEquivFin n).symm j))) =
        U *ᵥ (lower k *ᵥ (fun j => w ((bitsEquivFin n).symm j))) := by
      simp only [jumpOps, Matrix.mulVec_mulVec]
      congr 1
      calc U * lower k * Uᴴ * U = U * lower k * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
        _ = U * lower k := by rw [h1, Matrix.mul_one]
    show (WithLp.toLp 2 (U *ᵥ (fun j => (lowerQ k *ᵥ w) ((bitsEquivFin n).symm j))) : EuclideanSpace ℂ (Fin (2 ^ n))) ∈ S
    rw [e1, ← key]
    exact hact
  have hw0 : P (fun z => (Uᴴ *ᵥ WithLp.ofLp v) (bitsEquivFin n z)) := by
    show (WithLp.toLp 2 (U *ᵥ (fun j => (Uᴴ *ᵥ WithLp.ofLp v) (bitsEquivFin n ((bitsEquivFin n).symm j)))) :
      EuclideanSpace ℂ (Fin (2 ^ n))) ∈ S
    simp only [Equiv.apply_symm_apply]
    rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    simpa using hvS
  have hne0 : (fun z => (Uᴴ *ᵥ WithLp.ofLp v) (bitsEquivFin n z)) ≠ 0 := by
    intro h
    apply hv0
    have hz : Uᴴ *ᵥ WithLp.ofLp v = 0 := by
      funext j
      have := congrFun h ((bitsEquivFin n).symm j)
      simpa using this
    have : WithLp.ofLp v = 0 := by
      have := congrArg (fun x => U *ᵥ x) hz
      simpa [Matrix.mulVec_mulVec, h2] using this
    exact (WithLp.ofLp_injective 2) (by simpa using this)
  have hbd : ∀ y : Qubits n, bitWeight y ≤ n := fun y => by
    unfold bitWeight
    calc _ ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = n := by simp
  have hfin := lowering_induction P hsm hlow n (fun z => (Uᴴ *ᵥ WithLp.ofLp v) (bitsEquivFin n z)) hw0 hne0 (fun y _ => hbd y)
  have hsingle : (fun j => (Pi.single (fun _ => false) 1 : Qubits n → ℂ) ((bitsEquivFin n).symm j)) =
      (Pi.single 0 1 : Fin (2 ^ n) → ℂ) := by
    funext j
    by_cases hj : j = 0
    · subst hj
      have : (bitsEquivFin n).symm 0 = (fun _ => false) := by
        rw [Equiv.symm_apply_eq, bits_zero]
      simp [this]
    · have : (bitsEquivFin n).symm j ≠ (fun _ => false) := by
        intro h
        apply hj
        rw [← bits_zero n, ← h]
        simp
      simp [hj, this]
  have : target U = WithLp.toLp 2 (U *ᵥ (fun j => (Pi.single (fun _ => false) 1 : Qubits n → ℂ) ((bitsEquivFin n).symm j))) := by
    apply (WithLp.ofLp_injective 2)
    rw [target_ofLp, hsingle]
  rw [this]
  exact hfin

lemma pureDensity_eq {ι : Type*} [Fintype ι] (ψ : EuclideanSpace ℂ ι) :
    pureDensity ψ = Matrix.vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)) := by
  ext a b
  simp [pureDensity, Matrix.vecMulVec_apply]

open scoped ComplexOrder in
lemma pure_isDensity {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) : IsDensityMatrix (pureDensity (target U)) := by
  rw [pureDensity_eq]
  refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
  rw [Matrix.trace_vecMulVec]
  rw [dotProduct_comm]
  exact star_target U hU

lemma lower_target {n : ℕ} (k : Fin n) : lower k *ᵥ (Pi.single 0 1 : Fin (2 ^ n) → ℂ) = 0 := by
  funext j
  obtain ⟨x, rfl⟩ := (bitsEquivFin n).surjective j
  rw [lower_mulVec, lowerQ_mulVec]
  simp only [Pi.zero_apply]
  split_ifs with h
  · have : (bitsEquivFin n) (Function.update x k true) ≠ 0 := by
      intro h0
      rw [← bits_zero n] at h0
      have := (bitsEquivFin n).injective h0
      have := congrFun this k
      simp at this
    simp [this]
  · rfl

lemma jump_target {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (k : Fin n) :
    jumpOps U k *ᵥ WithLp.ofLp (target U) = 0 := by
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  rw [target_ofLp, Matrix.mulVec_mulVec]
  have : jumpOps U k * U = U * lower k := by
    simp only [jumpOps]
    calc U * lower k * Uᴴ * U = U * lower k * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]
  rw [this, ← Matrix.mulVec_mulVec, lower_target, Matrix.mulVec_zero]

lemma gksl_pure {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (g : Fin n → ℝ)
    (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (hH : H.IsHermitian) (E : ℝ)
    (hHt : H *ᵥ WithLp.ofLp (target U) = (E : ℂ) • WithLp.ofLp (target U)) :
    gkslGenerator (prepData U g H hH) (pureDensity (target U)) = 0 := by
  rw [gksl_apply, pureDensity_eq]
  set t := WithLp.ofLp (target U) with ht
  set D := prepData U g H hH with hD
  have hj : ∀ k, D.jump k *ᵥ t = 0 := by
    intro k
    show (((Real.sqrt (2 * g k) : ℝ) : ℂ) • jumpOps U k) *ᵥ t = 0
    rw [Matrix.smul_mulVec, jump_target U hU k, smul_zero]
  have hK : driftK D *ᵥ t = (Complex.I * (E : ℂ)) • t := by
    rw [driftK, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.sum_mulVec]
    have : D.drift = H := rfl
    rw [this, hHt]
    simp [← Matrix.mulVec_mulVec, hj]
    ext i; simp [Complex.real_smul, mul_assoc]
  have e1 : ∀ k, D.jump k * Matrix.vecMulVec t (star t) * (D.jump k)ᴴ = 0 := by
    intro k
    rw [Matrix.mul_vecMulVec, hj, Matrix.vecMulVec_mul]
    ext i j
    simp [Matrix.vecMulVec_apply]
  have e2 : driftK D * Matrix.vecMulVec t (star t) =
      (Complex.I * (E : ℂ)) • Matrix.vecMulVec t (star t) := by
    rw [Matrix.mul_vecMulVec, hK]
    ext i j
    simp [Matrix.vecMulVec_apply, mul_assoc]
  have e3 : Matrix.vecMulVec t (star t) * (driftK D)ᴴ =
      (-(Complex.I * (E : ℂ))) • Matrix.vecMulVec t (star t) := by
    rw [Matrix.vecMulVec_mul, ← Matrix.star_mulVec, hK]
    ext i j
    simp [Matrix.vecMulVec_apply, star_mul', mul_comm, mul_left_comm]
  rw [Finset.sum_eq_zero (fun k _ => e1 k), e2, e3]
  simp

lemma target_ne_zero {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) : WithLp.ofLp (target U) ≠ 0 := by
  intro h
  have := star_target U hU
  rw [h] at this
  simp at this

lemma target_mem_dark {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (E : ℝ)
    (hHt : act H (target U) = (E : ℂ) • target U) :
    target U ∈ darkSpace H (jumpOps U) E := by
  rw [mem_dark_iff]
  refine ⟨fun l => jump_target U hU l, ?_⟩
  have := congrArg WithLp.ofLp hHt
  simpa [act] using this

lemma stat_iff {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (g : Fin n → ℝ) (hg : ∀ k, 0 < g k)
    (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (hH : H.IsHermitian) (E : ℝ)
    (hHt : act H (target U) = (E : ℂ) • target U) (ρ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    stationary (prepData U g H hH) ρ ↔ ρ = pureDensity (target U) := by
  have hHt' : H *ᵥ WithLp.ofLp (target U) = (E : ℂ) • WithLp.ofLp (target U) := by
    have := congrArg WithLp.ofLp hHt
    simpa [act] using this
  constructor
  · intro hst
    have hD : ∀ (ψ : EuclideanSpace ℂ (Fin (2 ^ n))) (E' : ℝ), ψ ≠ 0 →
        (∀ l, act (jumpOps U l) ψ = 0) → act H ψ = (E' : ℂ) • ψ → E' = E := by
      intro ψ E' hψ hc hH'
      have hvec := dark_vec_eq U hU (WithLp.ofLp ψ) (fun l => by
        have := congrArg WithLp.ofLp (hc l)
        simpa [act] using this)
      rw [← target_ofLp] at hvec
      set α := (Uᴴ *ᵥ WithLp.ofLp ψ) 0
      have hα : α ≠ 0 := by
        intro h0
        apply hψ
        apply WithLp.ofLp_injective 2
        rw [hvec, h0]; simp
      have h2 := congrArg WithLp.ofLp hH'
      simp only [act] at h2
      simp only [WithLp.ofLp_toLp, WithLp.ofLp_smul] at h2
      rw [hvec, Matrix.mulVec_smul, hHt'] at h2
      obtain ⟨i, hi⟩ : ∃ i, WithLp.ofLp (target U) i ≠ 0 := by
        by_contra hall
        push Not at hall
        exact target_ne_zero U hU (funext hall)
      have h3 := congrFun h2 i
      simp only [Pi.smul_apply, smul_eq_mul] at h3
      have h5 : ((E : ℂ) - E') * (α * WithLp.ofLp (target U) i) = 0 := by linear_combination h3
      rcases mul_eq_zero.1 h5 with h | h
      · have : (E : ℂ) = E' := sub_eq_zero.1 h
        exact_mod_cast this.symm
      · exact absurd h (mul_ne_zero hα hi)
    have hS : ∀ S : Submodule ℂ (EuclideanSpace ℂ (Fin (2 ^ n))), lazy (jumpOps U) S →
        ¬ S ≤ (darkSpace H (jumpOps U) E)ᗮ := by
      intro S hS hle
      have hmem := lazy_target U hU S hS
      have h1 := hle hmem
      rw [Submodule.mem_orthogonal] at h1
      have h2 := h1 _ (target_mem_dark U hU H E hHt)
      rw [inner_self_eq_zero] at h2
      exact target_ne_zero U hU (by rw [h2]; rfl)
    have hsupp := theorem_2 H hH (jumpOps U) g hg E hD hS ρ hst
    obtain ⟨⟨hρ, htr⟩, -⟩ := hst
    have hρH : ρ.IsHermitian := by
      open scoped ComplexOrder in exact hρ.isHermitian
    set t := WithLp.ofLp (target U) with ht
    have hst1 : star t ⬝ᵥ t = 1 := star_target U hU
    have hcol : ∀ w, ρ *ᵥ w = (star t ⬝ᵥ (ρ *ᵥ w)) • t := by
      intro w
      have hψ : (WithLp.toLp 2 (ρ *ᵥ w) : EuclideanSpace ℂ (Fin (2 ^ n))) ∈ densitySupport ρ :=
        (mem_range_iff ρ _).2 ⟨w, rfl⟩
      obtain ⟨hc, -⟩ := (mem_dark_iff H (jumpOps U) E _).1 (hsupp hψ)
      have hvec := dark_vec_eq U hU _ hc
      rw [← target_ofLp] at hvec
      simp only [WithLp.ofLp_toLp] at hvec
      set α := (Uᴴ *ᵥ (ρ *ᵥ w)) 0
      conv_lhs => rw [hvec]
      rw [hvec, dotProduct_smul, hst1, smul_eq_mul, mul_one]
    set a := star t ⬝ᵥ (ρ *ᵥ t) with ha
    have hentry : ∀ i j, ρ i j = star a * (star (t j) * t i) := by
      intro i j
      have h1 := hcol (Pi.single j 1)
      have h2 : ρ *ᵥ (Pi.single j 1 : Fin (2 ^ n) → ℂ) = fun i => ρ i j := Matrix.mulVec_single_one ρ j
      have h3 : star t ⬝ᵥ (ρ *ᵥ (Pi.single j 1 : Fin (2 ^ n) → ℂ)) = star a * star (t j) := by
        rw [Matrix.dotProduct_mulVec]
        have := Matrix.star_mulVec ρᴴ t
        rw [Matrix.conjTranspose_conjTranspose, hρH.eq, hcol t] at this
        rw [← this, dotProduct_single_one]
        simp [star_smul, ha]
      rw [h3, h2] at h1
      have := congrFun h1 i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      rw [this]; ring
    have hstar : star a = 1 := by
      have : ρ.trace = star a * (star t ⬝ᵥ t) := by
        simp only [Matrix.trace, Matrix.diag_apply, hentry, dotProduct, Pi.star_apply, ← Finset.mul_sum]
      rw [htr, hst1, mul_one] at this
      exact this.symm
    ext i j
    rw [hentry, hstar, one_mul, pureDensity_eq]
    simp [Matrix.vecMulVec_apply, mul_comm]
    rfl
  · rintro rfl
    exact ⟨pure_isDensity U hU, gksl_pure U hU g H hH E hHt'⟩

section
open scoped Matrix.Norms.L2Operator

lemma pow_apply_eigen {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ →L[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (v : Matrix (Fin d) (Fin d) ℂ) (c : ℂ) (hv : A v = c • v) (n : ℕ) : (A ^ n) v = c ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply, hv, map_smul, ih, smul_smul, pow_succ, mul_comm]

lemma semigroup_eigen {d : ℕ} (G : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (v : Matrix (Fin d) (Fin d) ℂ) (μ : ℂ) (hv : G v = μ • v) (t : ℝ) :
    semigroupEvolution G t v = Complex.exp ((t : ℂ) * μ) • v := by
  unfold semigroupEvolution
  set A : Matrix (Fin d) (Fin d) ℂ →L[ℂ] Matrix (Fin d) (Fin d) ℂ :=
    (t : ℂ) • LinearMap.toContinuousLinearMap G with hA
  have hAv : A v = ((t : ℂ) * μ) • v := by
    simp [hA, hv, smul_smul]
  have h1 : HasSum (fun n : ℕ => (((n.factorial : ℂ)⁻¹ • (A ^ n)) : Matrix (Fin d) (Fin d) ℂ →L[ℂ] Matrix (Fin d) (Fin d) ℂ) v)
      (NormedSpace.exp A v) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL (ContinuousLinearMap.apply ℂ _ v)
  have h2 := (NormedSpace.expSeries_div_hasSum_exp ((t : ℂ) * μ)).smul_const v
  have e : ∀ n : ℕ, ((n.factorial : ℂ)⁻¹ • (A ^ n)) v = (((t : ℂ) * μ) ^ n / n.factorial) • v := by
    intro n
    rw [ContinuousLinearMap.smul_apply, pow_apply_eigen A v _ hAv, smul_smul, div_eq_inv_mul]
  simp only [e] at h1
  rw [Complex.exp_eq_exp_ℂ]
  exact h1.unique h2
end

lemma local_trace (p : Fin 4) : ∑ b : Bool, localEigenoperator p b b = if p = 0 then 1 else 0 := by
  fin_cases p <;> simp [localEigenoperator, Fintype.sum_bool]

lemma trace_tensor {n : ℕ} (i : Fin n → Fin 4) :
    (tensorEigenoperator i).trace = if i = (fun _ => 0) then 1 else 0 := by
  have h1 : (tensorEigenoperator i).trace = ∑ x : Qubits n, ∏ k, localEigenoperator (i k) (x k) (x k) := by
    simp only [Matrix.trace, Matrix.diag_apply, tensorEigenoperator, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.of_apply]
    exact Fintype.sum_equiv (bitsEquivFin n).symm _ _ (fun j => by simp)
  rw [h1]
  have h2 : ∑ x : Qubits n, ∏ k, localEigenoperator (i k) (x k) (x k) =
      ∏ k, ∑ b : Bool, localEigenoperator (i k) b b := by
    rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset Bool)) (fun k b => localEigenoperator (i k) b b),
      Fintype.piFinset_univ]
  rw [h2]
  simp only [local_trace]
  by_cases h : i = fun _ => 0
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨k, hk⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

lemma trace_sigma {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (i : Fin n → Fin 4) :
    (U * tensorEigenoperator i * Uᴴ).trace = if i = (fun _ => 0) then 1 else 0 := by
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  exact trace_tensor i

lemma sigma_zero {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    U * tensorEigenoperator (fun _ => 0) * Uᴴ = pureDensity (target U) := by
  have h0 : tensorEigenoperator (fun _ => (0 : Fin 4)) =
      Matrix.vecMulVec (Pi.single 0 1 : Fin (2 ^ n) → ℂ) (star (Pi.single 0 1 : Fin (2 ^ n) → ℂ)) := by
    ext a b
    obtain ⟨x, rfl⟩ := (bitsEquivFin n).surjective a
    obtain ⟨y, rfl⟩ := (bitsEquivFin n).surjective b
    simp only [tensorEigenoperator, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.of_apply, Matrix.vecMulVec_apply]
    have hx : ∀ x : Qubits n, (bitsEquivFin n x = 0) ↔ x = fun _ => false := fun x => by
      constructor
      · intro h; rw [← bits_zero n] at h; exact (bitsEquivFin n).injective h
      · rintro rfl; exact bits_zero n
    have hloc : ∀ x y : Bool, localEigenoperator 0 x y = if x = false ∧ y = false then 1 else 0 := by
      intro x y; simp [localEigenoperator]
    simp only [hloc]
    by_cases hx' : x = fun _ => false
    · by_cases hy' : y = fun _ => false
      · subst hx'; subst hy'; simp [bits_zero]
      · have : ¬ (bitsEquivFin n y = 0) := fun h => hy' ((hx y).1 h)
        obtain ⟨k, hk⟩ : ∃ k, y k = true := by
          by_contra hall
          apply hy'; funext k
          by_cases h : y k = true
          · exact absurd ⟨k, h⟩ hall
          · simpa using h
        rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])]
        simp [this]
    · have : ¬ (bitsEquivFin n x = 0) := fun h => hx' ((hx x).1 h)
      obtain ⟨k, hk⟩ : ∃ k, x k = true := by
        by_contra hall
        apply hx'; funext k
        by_cases h : x k = true
        · exact absurd ⟨k, h⟩ hall
        · simpa using h
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])]
      simp [this]
  rw [h0, pureDensity_eq, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, target_ofLp, ← Matrix.star_mulVec]

lemma lam_real {n : ℕ} (g : Fin n → ℝ) (i : Fin n → Fin 4) :
    (∑ k, localEigenvalue (g k) (i k)) =
      ((-(∑ k, (((![0, 1, 1, 2] : Fin 4 → Fin 3) (i k) : Fin 3) : ℕ) * g k) : ℝ) : ℂ) := by
  simp only [lev_cnt]
  push_cast
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma lam_pos {n : ℕ} (g : Fin n → ℝ) (hg : ∀ k, 0 < g k) (i : Fin n → Fin 4)
    (hi : i ≠ fun _ => 0) :
    0 < ∑ k, (((![0, 1, 1, 2] : Fin 4 → Fin 3) (i k) : Fin 3) : ℕ) * g k := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hi
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (Nat.cast_nonneg _) (hg j).le
  · refine ⟨k, Finset.mem_univ k, ?_⟩
    apply mul_pos _ (hg k)
    have : 0 < (((![0, 1, 1, 2] : Fin 4 → Fin 3) (i k) : Fin 3) : ℕ) := by
      generalize i k = p at hk
      fin_cases p <;> simp_all
    exact_mod_cast this

lemma exp_tendsto_zero (r : ℝ) (hr : r < 0) :
    Filter.Tendsto (fun t : ℝ => Complex.exp ((t : ℂ) * (r : ℂ))) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun t : ℝ => t * r) Filter.atTop Filter.atBot :=
    Filter.Tendsto.atTop_mul_const_of_neg hr Filter.tendsto_id
  have h2 := Real.tendsto_exp_atBot.comp h1
  have h3 := (Complex.continuous_ofReal.tendsto 0).comp h2
  simp only [Complex.ofReal_zero] at h3
  refine h3.congr fun t => ?_
  simp [Function.comp, ← Complex.ofReal_mul, Complex.ofReal_exp]

section
open scoped Matrix.Norms.L2Operator

lemma attractive_prep {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (g : Fin n → ℝ) (hg : ∀ k, 0 < g k) :
    attractive (prepData U g 0 Matrix.isHermitian_zero) (pureDensity (target U)) := by
  obtain ⟨hEig, hli, hspan, -⟩ := product_spectrum U hU g hg
  refine ⟨(stat_iff U hU g hg 0 Matrix.isHermitian_zero 0 (by simp [act]) _).2 rfl, ?_⟩
  intro X hX
  have hXs : X ∈ Submodule.span ℂ (Set.range fun i : Fin n → Fin 4 => U * tensorEigenoperator i * Uᴴ) := by
    rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hXs
  set i0 : Fin n → Fin 4 := fun _ => 0 with hi0
  have hevo : ∀ t : ℝ, semigroupEvolution (gkslGenerator (prepData U g 0 Matrix.isHermitian_zero)) t X =
      ∑ i, (c i * Complex.exp ((t : ℂ) * (∑ k, localEigenvalue (g k) (i k)))) •
        (U * tensorEigenoperator i * Uᴴ) := by
    intro t
    rw [← hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, semigroup_eigen _ _ _ (hEig i) t, smul_smul]
  have htr : c i0 = 1 := by
    have h1 := hX.2
    rw [← hc, Matrix.trace_sum] at h1
    simp only [Matrix.trace_smul, trace_sigma U hU, smul_eq_mul] at h1
    simpa [hi0] using h1
  have hlim : ∀ i, Filter.Tendsto (fun t : ℝ => (c i * Complex.exp ((t : ℂ) * (∑ k, localEigenvalue (g k) (i k)))) •
        (U * tensorEigenoperator i * Uᴴ)) Filter.atTop
        (nhds (if i = i0 then c i • (U * tensorEigenoperator i * Uᴴ) else 0)) := by
    intro i
    by_cases hi : i = i0
    · rw [if_pos hi]
      have : (∑ k, localEigenvalue (g k) (i k)) = 0 := by
        rw [hi]; simp [hi0, localEigenvalue]
      simp only [this, mul_zero, Complex.exp_zero, mul_one]
      exact tendsto_const_nhds
    · rw [if_neg hi, lam_real]
      have hpos := lam_pos g hg i hi
      have h2 := exp_tendsto_zero (-(∑ k, (((![0, 1, 1, 2] : Fin 4 → Fin 3) (i k) : Fin 3) : ℕ) * g k)) (by linarith)
      have h3 := (h2.const_mul (c i)).smul_const (U * tensorEigenoperator i * Uᴴ)
      simpa using h3
  have hsum := tendsto_finset_sum Finset.univ (fun i _ => hlim i)
  have hval : ∑ i, (if i = i0 then c i • (U * tensorEigenoperator i * Uᴴ) else 0) = pureDensity (target U) := by
    rw [Finset.sum_ite_eq' Finset.univ i0, if_pos (Finset.mem_univ _), htr, one_smul, hi0, sigma_zero]
  rw [hval] at hsum
  exact hsum.congr (fun t => (hevo t).symm)
end

lemma relax_least {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (g : Fin n → ℝ) (hg : ∀ k, 0 < g k)
    (gmin : ℝ) (hgmin : IsLeast (Set.range g) gmin) :
    IsLeast (relaxRates (gkslGenerator (prepData U g 0 Matrix.isHermitian_zero))) gmin := by
  obtain ⟨-, -, -, hspec⟩ := product_spectrum U hU g hg
  constructor
  · obtain ⟨k0, hk0⟩ := hgmin.1
    refine ⟨-((g k0 : ℝ) : ℂ), ?_, ?_, ?_⟩
    · refine (hspec _).2 ⟨fun k => if k = k0 then 1 else 0, ?_⟩
      congr 1
      rw [Finset.sum_eq_single k0]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ _) h
    · have := hg k0
      intro h
      have h2 : ((g k0 : ℝ) : ℂ) = 0 := neg_eq_zero.1 h
      have : g k0 = 0 := by exact_mod_cast h2
      linarith [hg k0]
    · simp [hk0]
  · rintro r ⟨μ, hμ, hμ0, rfl⟩
    obtain ⟨m, hm⟩ := (hspec μ).1 hμ
    have hre : -μ.re = ∑ k, ((m k : ℕ) : ℝ) * g k := by
      rw [hm]
      simp [Complex.re_sum]
    rw [hre]
    have hex : ∃ k, (m k : ℕ) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hμ0
      rw [hm]
      simp [hall]
    obtain ⟨k, hk⟩ := hex
    have h1 : g k ≤ ((m k : ℕ) : ℝ) * g k := by
      have : (1 : ℝ) ≤ ((m k : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
      nlinarith [hg k]
    have h2 : ((m k : ℕ) : ℝ) * g k ≤ ∑ j, ((m j : ℕ) : ℝ) * g j :=
      Finset.single_le_sum (f := fun j => ((m j : ℕ) : ℝ) * g j)
        (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hg j).le) (Finset.mem_univ k)
    have h3 : gmin ≤ g k := hgmin.2 ⟨k, rfl⟩
    linarith

lemma relax_time {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (g : Fin n → ℝ) (hg : ∀ k, 0 < g k)
    (gmin : ℝ) (hgmin : IsLeast (Set.range g) gmin) :
    IsRelaxTime (gkslGenerator (prepData U g 0 Matrix.isHermitian_zero)) (1 / gmin) := by
  obtain ⟨k0, hk0⟩ := hgmin.1
  exact ⟨gmin, relax_least U hU g hg gmin hgmin, by rw [← hk0]; exact hg k0, rfl⟩

end DissipativePrep.Unique

open DissipativePrep.Unique
theorem solution {n : ℕ} (hn : 1 ≤ n)
    (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (g : Fin n → ℝ) (hg : ∀ k, 0 < g k) (gmin : ℝ) (hgmin : IsLeast (Set.range g) gmin) :
    (∀ (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (hH : H.IsHermitian) (E : ℝ),
        act H (target U) = (E : ℂ) • target U →
        ∀ ρ, stationary (prepData U g H hH) ρ ↔ ρ = pureDensity (target U)) ∧
    attractive (prepData U g 0 Matrix.isHermitian_zero) (pureDensity (target U)) ∧
    IsLeast (relaxRates (gkslGenerator (prepData U g 0 Matrix.isHermitian_zero))) gmin ∧
    IsRelaxTime (gkslGenerator (prepData U g 0 Matrix.isHermitian_zero)) (1 / gmin) :=
  ⟨fun H hH E hHt ρ => stat_iff U hU g hg H hH E hHt ρ, attractive_prep U hU g hg,
    relax_least U hU g hg gmin hgmin, relax_time U hU g hg gmin hgmin⟩

