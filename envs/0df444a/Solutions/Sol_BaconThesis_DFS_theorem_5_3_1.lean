-- Prove2me | solution 1 for BaconThesis.DFS.theorem_5_3_1
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T16:28:17.889437+00:00
-- url     : https://prove2.me/submissions/0da179d0-6742-443f-8517-771179a8b721

import Mathlib
import Definitions.Def_BaconThesis_DFS_IsDFS

open scoped Matrix Kronecker ComplexOrder

namespace BaconThesis.DFS.Sol531

open BaconThesis.DFS

section calculus

variable {T : Type} [Fintype T] [DecidableEq T]

/-- The generator `X ↦ -i [H, X]` of the evolution. -/
def gen (H X : Matrix T T ℂ) : Matrix T T ℂ := (-Complex.I) • (H * X - X * H)

private lemma evolOp_conjTranspose (H : Matrix T T ℂ) (hH : H.IsHermitian) (t : ℝ) :
    (evolOp H t)ᴴ = NormedSpace.exp (((t : ℂ) * Complex.I) • H) := by
  have hs : star (-(t : ℂ) * Complex.I) = (t : ℂ) * Complex.I := by simp
  rw [evolOp, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH.eq, hs]

private lemma evolOp_unitary (H : Matrix T T ℂ) (hH : H.IsHermitian) (t : ℝ) :
    (evolOp H t)ᴴ * evolOp H t = 1 := by
  rw [evolOp_conjTranspose H hH, evolOp, ← Matrix.exp_add_of_commute]
  · rw [← add_smul]
    simp
  · exact (Commute.refl H).smul_left _ |>.smul_right _

open scoped Matrix.Norms.Operator in
private lemma hasDerivAt_evol (H R : Matrix T T ℂ) (hH : H.IsHermitian) (t : ℝ) :
    HasDerivAt (fun t : ℝ => evolOp H t * R * (evolOp H t)ᴴ)
      (evolOp H t * gen H R * (evolOp H t)ᴴ) t := by
  have e1 : ∀ s : ℝ, evolOp H s = NormedSpace.exp (s • ((-Complex.I) • H)) := by
    intro s
    rw [evolOp]
    congr 1
    rw [← Complex.coe_smul, smul_smul]
    congr 1
    ring
  have e2 : ∀ s : ℝ, (evolOp H s)ᴴ = NormedSpace.exp (s • (Complex.I • H)) := by
    intro s
    rw [evolOp_conjTranspose H hH, ← Complex.coe_smul, smul_smul]
  simp_rw [e2, e1]
  have h1 := hasDerivAt_exp_smul_const ((-Complex.I) • H) t
  have h2 := hasDerivAt_exp_smul_const' (Complex.I • H) t
  refine ((h1.mul_const R).mul h2).congr_deriv ?_
  change NormedSpace.exp (t • -Complex.I • H) * (-Complex.I • H) * R *
      NormedSpace.exp (t • Complex.I • H) +
    NormedSpace.exp (t • -Complex.I • H) * R * (Complex.I • H * NormedSpace.exp (t • Complex.I • H)) =
    NormedSpace.exp (t • -Complex.I • H) * (-Complex.I • (H * R - R * H)) *
      NormedSpace.exp (t • Complex.I • H)
  generalize NormedSpace.exp (t • -Complex.I • H) = U
  generalize NormedSpace.exp (t • Complex.I • H) = V
  simp only [smul_mul_assoc, mul_smul_comm, mul_sub, sub_mul, smul_sub, mul_assoc]
  module

open scoped Matrix.Norms.Operator in
/-- If `X` and `Y` agree on the range of `Q` and `Y` commutes with `Q`, so do their exponentials. -/
private lemma exp_mul_eq (X Y Q : Matrix T T ℂ) (hXY : X * Q = Y * Q) (hYQ : Y * Q = Q * Y)
    (z : ℂ) : NormedSpace.exp (z • X) * Q = NormedSpace.exp (z • Y) * Q := by
  have hpow : ∀ k : ℕ, X ^ k * Q = Y ^ k * Q := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, mul_assoc, hXY, hYQ, ← mul_assoc, ih, mul_assoc, ← hYQ, ← mul_assoc,
        ← pow_succ]
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z • X)).mul_right Q
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z • Y)).mul_right Q
  have heq : ∀ k : ℕ, ((k.factorial : ℂ)⁻¹ • (z • X) ^ k) * Q =
      ((k.factorial : ℂ)⁻¹ • (z • Y) ^ k) * Q := by
    intro k
    rw [smul_pow, smul_pow, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, hpow]
  simp only [heq] at h1
  exact h1.unique h2

end calculus

section vectors

variable {n : Type} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private lemma vecMulVec_mulVec' (u v x : n → ℂ) :
    Matrix.vecMulVec u v *ᵥ x = (v ⬝ᵥ x) • u := by
  ext i
  simp [Matrix.vecMulVec_mulVec, mul_comm]

omit [DecidableEq n] in
private lemma exists_normalize (w : n → ℂ) (hw : w ≠ 0) :
    ∃ a : ℂ, a ≠ 0 ∧ star (a • w) ⬝ᵥ (a • w) = 1 := by
  have hx : star w ⬝ᵥ w ≠ 0 := mt dotProduct_star_self_eq_zero.mp hw
  have hnn : 0 ≤ star w ⬝ᵥ w := dotProduct_star_self_nonneg w
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hnn
  set r : ℝ := (star w ⬝ᵥ w).re with hr
  have hxr : star w ⬝ᵥ w = (r : ℂ) := Complex.ext rfl (by simpa using him.symm)
  have hrpos : 0 < r := lt_of_le_of_ne hre fun h => hx (by rw [hxr, ← h]; simp)
  have hs : (Real.sqrt r : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hrpos).ne'
  refine ⟨(Real.sqrt r : ℂ)⁻¹, inv_ne_zero hs, ?_⟩
  rw [star_smul, smul_dotProduct, dotProduct_smul, hxr, smul_eq_mul, smul_eq_mul]
  have h2 : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hrpos.le
  have hstar : star ((Real.sqrt r : ℂ)⁻¹) = (Real.sqrt r : ℂ)⁻¹ := by simp
  rw [hstar, ← h2]
  field_simp

/-- A matrix whose quadratic form vanishes is zero (polarization). -/
private lemma eq_zero_of_quadratic (N : Matrix n n ℂ) (h : ∀ v : n → ℂ, star v ⬝ᵥ N *ᵥ v = 0) :
    N = 0 := by
  have hB : ∀ u v : n → ℂ, star u ⬝ᵥ N *ᵥ v = 0 := by
    intro u v
    have h1 := h (u + v)
    have h2 := h (u + Complex.I • v)
    simp only [star_add, star_smul, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
      dotProduct_add, smul_dotProduct, dotProduct_smul, h u, h v, smul_eq_mul, Complex.star_def,
      Complex.conj_I] at h1 h2
    have h3 : Complex.I * (star u ⬝ᵥ N *ᵥ v - star v ⬝ᵥ N *ᵥ u) = 0 := by linear_combination h2
    have h4 : star u ⬝ᵥ N *ᵥ v - star v ⬝ᵥ N *ᵥ u = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h Complex.I_ne_zero
      · exact h
    linear_combination (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h4
  ext a b
  have := hB (Pi.single a 1) (Pi.single b 1)
  simpa using this

omit [DecidableEq n] in
/-- A matrix for which every vector of a submodule is an eigenvector is scalar on it. -/
private lemma exists_common_scalar (S : Matrix n n ℂ) (W : Submodule ℂ (n → ℂ))
    (h : ∀ w ∈ W, ∃ μ : ℂ, S *ᵥ w = μ • w) : ∃ c : ℂ, ∀ w ∈ W, S *ᵥ w = c • w := by
  by_cases hW : ∀ w ∈ W, w = 0
  · exact ⟨0, fun w hw => by rw [hW w hw]; simp⟩
  push Not at hW
  obtain ⟨w0, hw0, hne⟩ := hW
  obtain ⟨μ0, hμ0⟩ := h w0 hw0
  refine ⟨μ0, fun w hw => ?_⟩
  obtain ⟨μ, hμ⟩ := h w hw
  obtain ⟨ν, hν⟩ := h (w + w0) (W.add_mem hw hw0)
  rw [Matrix.mulVec_add, hμ, hμ0, smul_add] at hν
  have key : (μ - ν) • w = (ν - μ0) • w0 := by
    rw [sub_smul, sub_smul]
    linear_combination (exp := 1) hν
  by_cases hμν : μ = ν
  · rw [hμν, sub_self, zero_smul] at key
    have : ν - μ0 = 0 := by
      by_contra hc
      exact hne ((smul_eq_zero.mp key.symm).resolve_left hc)
    rw [hμ, hμν, sub_eq_zero.mp this]
  · have hw' : w = ((μ - ν)⁻¹ * (ν - μ0)) • w0 := by
      rw [mul_smul, ← key, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hμν), one_smul]
    rw [hw', Matrix.mulVec_smul, hμ0, smul_comm]

end vectors

section blocks

variable {s e : Type} [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]

/-- The partial trace over the environment as a linear map. -/
private def ptr : Matrix (s × e) (s × e) ℂ →ₗ[ℂ] Matrix s s ℂ where
  toFun := WildeQIT.partialTraceRight
  map_add' X Y := by ext; simp [WildeQIT.partialTraceRight, Finset.sum_add_distrib]
  map_smul' c X := by ext; simp [WildeQIT.partialTraceRight, Finset.mul_sum]

omit [Fintype s] [DecidableEq s] [DecidableEq e] in
private lemma ptr_kronecker (A : Matrix s s ℂ) (X : Matrix e e ℂ) :
    ptr (A ⊗ₖ X) = X.trace • A := by
  ext a b
  simp [ptr, WildeQIT.partialTraceRight, Matrix.trace, ← Finset.mul_sum, mul_comm]

private lemma exp_one_kronecker (Y : Matrix e e ℂ) :
    NormedSpace.exp ((1 : Matrix s s ℂ) ⊗ₖ Y) = (1 : Matrix s s ℂ) ⊗ₖ NormedSpace.exp Y := by
  let f : Matrix e e ℂ →+* Matrix (s × e) (s × e) ℂ :=
    { toFun := fun Y => (1 : Matrix s s ℂ) ⊗ₖ Y
      map_one' := Matrix.one_kronecker_one
      map_mul' := fun A B => by rw [← Matrix.mul_kronecker_mul, one_mul]
      map_zero' := Matrix.kronecker_zero _
      map_add' := fun A B => Matrix.kronecker_add _ _ _ }
  have hf : Continuous f := by
    refine continuous_matrix fun i j => ?_
    change Continuous fun Y : Matrix e e ℂ => (1 : Matrix s s ℂ) i.1 j.1 * Y i.2 j.2
    fun_prop
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp f hf Y).symm

end blocks

end BaconThesis.DFS.Sol531

open BaconThesis.DFS BaconThesis.DFS.Sol531

theorem solution {s e ι : Type} [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]
    [Fintype ι]
    (Sα : ι → Matrix s s ℂ) (Bα : ι → Matrix e e ℂ)
    (hH : (∑ α, Sα α ⊗ₖ Bα α).IsHermitian) (hB : LinearIndependent ℂ Bα)
    (W : Submodule ℂ (s → ℂ)) :
    IsDFS (∑ α, Sα α ⊗ₖ Bα α) W ↔ ∃ c : ι → ℂ, ∀ α, ∀ j ∈ W, Sα α *ᵥ j = c α • j := by
  classical
  set H := ∑ α, Sα α ⊗ₖ Bα α with hHdef
  constructor
  · intro hDFS
    -- for a unit vector of `W`, the projector commutes with every `S_α`
    have comm : ∀ j ∈ W, star j ⬝ᵥ j = 1 → ∀ α,
        Sα α * Matrix.vecMulVec j (star j) = Matrix.vecMulVec j (star j) * Sα α := by
      intro j hj hj1 α
      set P := Matrix.vecMulVec j (star j) with hP
      -- first-order condition for every environment state
      have first : ∀ ρ : Matrix e e ℂ, WildeQIT.IsDensityOperator ρ →
          ∑ β, (Bα β * ρ).trace • (Sα β * P - P * Sα β) = 0 := by
        intro ρ hρ
        have hder : ptr (gen H (P ⊗ₖ ρ)) = 0 := by
          ext x y
          let L : Matrix (s × e) (s × e) ℂ →ₗ[ℂ] ℂ :=
            (Matrix.entryLinearMap ℂ ℂ x y).comp ptr
          let Lc : Matrix (s × e) (s × e) ℂ →L[ℝ] ℂ :=
            LinearMap.toContinuousLinearMap (L.restrictScalars ℝ)
          have h0 := hasDerivAt_evol H (P ⊗ₖ ρ) hH 0
          have h1 : HasDerivAt (fun t : ℝ => osrEvolve H ρ t P x y)
              (L (evolOp H 0 * gen H (P ⊗ₖ ρ) * (evolOp H 0)ᴴ)) 0 := by
            open scoped Matrix.Norms.Operator in
            exact Lc.hasFDerivAt.comp_hasDerivAt 0 h0
          have h2 : HasDerivWithinAt (fun t : ℝ => osrEvolve H ρ t P x y) 0 (Set.Ici 0) 0 := by
            refine (hasDerivWithinAt_const (0 : ℝ) (Set.Ici 0) (P x y)).congr ?_ ?_
            · intro t ht
              rw [hDFS j hj hj1 ρ hρ t ht]
            · rw [hDFS j hj hj1 ρ hρ 0 le_rfl]
          have h3 := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ h1.hasDerivWithinAt h2
          simpa [L, evolOp] using h3
        have hgen : gen H (P ⊗ₖ ρ) = (-Complex.I) •
            ∑ β, ((Sα β * P) ⊗ₖ (Bα β * ρ) - (P * Sα β) ⊗ₖ (ρ * Bα β)) := by
          rw [gen, hHdef, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
          simp only [Matrix.mul_kronecker_mul]
        rw [hgen, map_smul, map_sum] at hder
        have hder' := (smul_eq_zero.mp hder).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)
        rw [← hder']
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [map_sub, ptr_kronecker, ptr_kronecker, Matrix.trace_mul_comm ρ, smul_sub]
      -- polarize in the environment state and use linear independence
      ext x y
      have hN : ∑ β, (Sα β * P - P * Sα β) x y • Bα β = 0 := by
        apply eq_zero_of_quadratic
        intro v
        by_cases hv : v = 0
        · simp [hv]
        obtain ⟨a, ha, hav⟩ := exists_normalize v hv
        have hρ : WildeQIT.IsDensityOperator (Matrix.vecMulVec (a • v) (star (a • v))) :=
          ⟨Matrix.posSemidef_vecMulVec_self_star _, by
            rw [Matrix.trace_vecMulVec, dotProduct_comm]; exact hav⟩
        have htr : ∀ β, (Bα β * Matrix.vecMulVec (a • v) (star (a • v))).trace =
            star (a • v) ⬝ᵥ Bα β *ᵥ (a • v) := fun β => by
          rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
        have h1 : (∑ β, (Bα β * Matrix.vecMulVec (a • v) (star (a • v))).trace •
            (Sα β * P - P * Sα β)) x y = 0 := by
          rw [first _ hρ]; rfl
        have h2 : star (a • v) ⬝ᵥ (∑ β, (Sα β * P - P * Sα β) x y • Bα β) *ᵥ (a • v) = 0 := by
          rw [← h1]
          simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul,
            Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [htr β, mul_comm]
        rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
          smul_eq_mul] at h2
        have ha' : star a ≠ 0 := star_ne_zero.mpr ha
        exact (mul_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left ha')).resolve_left ha
      have := Fintype.linearIndependent_iff.mp hB _ hN α
      simpa [sub_eq_zero] using this
    -- so every vector of `W` is an eigenvector of every `S_α`
    have eig : ∀ α, ∀ w ∈ W, ∃ μ : ℂ, Sα α *ᵥ w = μ • w := by
      intro α w hw
      by_cases hw0 : w = 0
      · exact ⟨0, by simp [hw0]⟩
      obtain ⟨a, ha, hav⟩ := exists_normalize w hw0
      obtain ⟨u, hu⟩ : ∃ u, u = a • w := ⟨_, rfl⟩
      rw [← hu] at hav
      have hc := comm u (hu ▸ W.smul_mem a hw) hav α
      have h1 : Sα α *ᵥ u = (star u ⬝ᵥ Sα α *ᵥ u) • u := by
        calc Sα α *ᵥ u = Sα α *ᵥ (Matrix.vecMulVec u (star u) *ᵥ u) := by
              rw [vecMulVec_mulVec', hav, one_smul]
          _ = (Sα α * Matrix.vecMulVec u (star u)) *ᵥ u := by rw [Matrix.mulVec_mulVec]
          _ = (Matrix.vecMulVec u (star u) * Sα α) *ᵥ u := by rw [hc]
          _ = Matrix.vecMulVec u (star u) *ᵥ (Sα α *ᵥ u) := by rw [Matrix.mulVec_mulVec]
          _ = _ := vecMulVec_mulVec' _ _ _
      refine ⟨star u ⬝ᵥ Sα α *ᵥ u, smul_right_injective _ ha ?_⟩
      change a • (Sα α *ᵥ w) = a • ((star u ⬝ᵥ Sα α *ᵥ u) • w)
      rw [← Matrix.mulVec_smul, smul_comm a, ← hu]
      exact h1
    choose c hc using fun α => exists_common_scalar (Sα α) W (eig α)
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩ j hj hj1 ρ hρ t _
    set P := Matrix.vecMulVec j (star j) with hP
    set Bc : Matrix e e ℂ := ∑ α, c α • Bα α with hBc
    set Q : Matrix (s × e) (s × e) ℂ := P ⊗ₖ (1 : Matrix e e ℂ) with hQ
    set K : Matrix (s × e) (s × e) ℂ := (1 : Matrix s s ℂ) ⊗ₖ Bc with hK
    have hPP : P * P = P := by
      rw [hP, Matrix.vecMulVec_mul_vecMulVec, hj1, one_smul]
    have hPH : Pᴴ = P := by
      rw [hP, Matrix.conjTranspose_vecMulVec]; simp
    have hKQ : K * Q = P ⊗ₖ Bc := by
      rw [hK, hQ, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
    have hQK : Q * K = P ⊗ₖ Bc := by
      rw [hK, hQ, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
    have hHQ : H * Q = K * Q := by
      rw [hKQ, hHdef, hQ, Finset.sum_mul, hBc]
      simp only [← Matrix.mul_kronecker_mul, Matrix.mul_one]
      have : ∀ α, Sα α * P = c α • P := by
        intro α
        rw [hP, Matrix.mul_vecMulVec, hc α j hj, Matrix.smul_vecMulVec]
      simp only [this]
      ext ⟨a, b⟩ ⟨a', b'⟩
      simp [Matrix.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      ring
    have hexp := exp_mul_eq H K Q hHQ (hKQ.trans hQK.symm) (-(t : ℂ) * Complex.I)
    set z : ℂ := -(t : ℂ) * Complex.I with hz
    set V : Matrix e e ℂ := NormedSpace.exp (z • Bc) with hV
    set U := evolOp H t with hU
    set R : Matrix (s × e) (s × e) ℂ := P ⊗ₖ ρ with hR
    have hUQ : U * Q = ((1 : Matrix s s ℂ) ⊗ₖ V) * Q := by
      rw [hU, evolOp, hexp, hK, ← Matrix.kronecker_smul, exp_one_kronecker]
    have hQH : Qᴴ = Q := by
      rw [hQ, Matrix.conjTranspose_kronecker, hPH, Matrix.conjTranspose_one]
    have hQRQ : Q * R * Q = R := by
      rw [hQ, hR, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hPP, hPP,
        Matrix.one_mul, Matrix.mul_one]
    have hURU : U * R * Uᴴ = P ⊗ₖ (V * ρ * Vᴴ) := by
      calc U * R * Uᴴ = (U * Q) * R * (U * Q)ᴴ := by
            rw [Matrix.conjTranspose_mul, hQH]
            nth_rewrite 1 [← hQRQ]
            simp only [Matrix.mul_assoc]
        _ = ((1 : Matrix s s ℂ) ⊗ₖ V) * (Q * R * Q) * ((1 : Matrix s s ℂ) ⊗ₖ V)ᴴ := by
            rw [hUQ, Matrix.conjTranspose_mul, hQH]
            simp only [Matrix.mul_assoc]
        _ = P ⊗ₖ (V * ρ * Vᴴ) := by
            rw [hQRQ, hR, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
              ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
              Matrix.mul_one]
    have hPtr : P.trace = 1 := by
      rw [hP, Matrix.trace_vecMulVec, dotProduct_comm]; exact hj1
    have htr : (V * ρ * Vᴴ).trace = 1 := by
      have h1 : (U * R * Uᴴ).trace = 1 := by
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, evolOp_unitary H hH, Matrix.one_mul, hR,
          Matrix.trace_kronecker, hPtr, hρ.2, one_mul]
      rw [hURU, Matrix.trace_kronecker, hPtr, one_mul] at h1
      exact h1
    change ptr (U * R * Uᴴ) = P
    rw [hURU, ptr_kronecker, htr, one_smul]
