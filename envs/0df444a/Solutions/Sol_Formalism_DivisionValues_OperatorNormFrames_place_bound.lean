-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.place_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:39.242205+00:00
-- url     : https://prove2.me/submissions/1f4809f1-ebb8-4363-a8f2-eac30eb8294f

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_cnorm_eq
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_cnorm_nonneg
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_mul_inv_mulVec
import Theorems.Thm_Formalism_DivisionValues_frobenius_norm_rational
import Theorems.Thm_Formalism_DivisionValues_operator_norm_dual
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_cnorm_sq_mulVec
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_quot_rep
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_pairC_transfer
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_opNormAt_nonneg
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_opNormAt_mulVecLin
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_map_mulVec_emb
import Theorems.Thm_Formalism_HN_PlaceOperatorNorms_cnorm_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open OperatorNormFrames
open Formalism.DivisionValues.OperatorNormFrames
namespace Formalism.DivisionValues.OperatorNormFrames
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] {n D a b : ℕ}
    (Xa : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (ha : ∀ v, IsUnit (Xa v).det)
    (Xb : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ) (hb : ∀ v, IsUnit (Xb v).det)
    (col : Matrix (Fin b) (Fin a) K)
    (H : Matrix (Fin n) (Fin n) K) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (h0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding)
    (P : Matrix (Fin D) (Fin n) K) (hP : Function.Surjective P.mulVec)
    (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hQ : IsQuotMetric P H XQ)
    (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hE : ∀ v, IsUnit (XE v).det)
    (ι : Matrix (Fin D) (Fin D) K) (hι : IsUnit ι.det)
    {Ix : Type} [Fintype Ix] (Qp : Ix → Submodule K (Fin D → K)) (hsup : (⨆ p, Qp p) = ⊤)
    (v : InfinitePlace K) (s : Ix → ℝ) (smin : ℝ) (hsmin : 0 < smin) (hs : ∀ p, smin ≤ s p)
    (hspec : ∀ p, ∀ x ∈ Qp p, ∀ y : Fin D → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XE v (ι.mulVec x) (ι.mulVec y) =
        ((s p : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XQ v x y)
    (Pt : (Fin b → K) →ₗ[K] Module.Dual K (Fin n → K))
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K))
    (hB : ∀ φ F, B φ (ι.mulVec (P.mulVec F)) = Pt (col.mulVec φ) F)
    (p k : ℝ)
    (hp : Formalism.HN.opNormAt (Pi.basisFun K (Fin b)) Xb (Pi.basisFun K (Fin n)).dualBasis
      (Formalism.HN.dualFrame X0) v Pt ≤ p)
    (hk : Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) Xa (Pi.basisFun K (Fin b)) Xb v
      (Matrix.mulVecLin col) ≤ k) :
    Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) Xa (Pi.basisFun K (Fin D)).dualBasis
      (Formalism.HN.dualFrame XE) v B ≤ p * k / Real.sqrt smin := by
  have hp0 : 0 ≤ p := (opNormAt_nonneg _ _ _ _ _ _).trans hp
  have hk0 : 0 ≤ k := (opNormAt_nonneg _ _ _ _ _ _).trans hk
  have hr : 0 < Real.sqrt smin := Real.sqrt_pos.2 hsmin
  have hc : 0 ≤ p * k / Real.sqrt smin := div_nonneg (mul_nonneg hp0 hk0) hr.le
  have hstar : ∀ r : ℝ, star (r : ℂ) = (r : ℂ) := fun r => Complex.conj_ofReal r
  have hds : ∀ (x : Fin D → ℂ) (b : Ix → Fin D → ℂ), x ⬝ᵥ ∑ q, b q = ∑ q, x ⬝ᵥ b q := by
    intro x b
    simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  have hsd : ∀ (a' : Ix → Fin D → ℂ) (y : Fin D → ℂ), (∑ q, a' q) ⬝ᵥ y = ∑ q, a' q ⬝ᵥ y := by
    intro a' y
    simp only [dotProduct, Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hsm1 : ∀ (r : ℂ) (x y : Fin D → ℂ), (r • x) ⬝ᵥ y = r * (x ⬝ᵥ y) := by
    intro r x y
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have hsm2 : ∀ (r : ℂ) (x y : Fin D → ℂ), x ⬝ᵥ (r • y) = r * (x ⬝ᵥ y) := by
    intro r x y
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmsm : ∀ (M : Matrix (Fin D) (Fin D) ℂ) (r : ℂ) (x : Fin D → ℂ), M *ᵥ (r • x) = r • (M *ᵥ x) := by
    intro M r x
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨ι', hι'def⟩ : ∃ M : Matrix (Fin D) (Fin D) ℂ, M = ι.map v.embedding := ⟨_, rfl⟩
  have hι'U : IsUnit ι'.det := by
    have h1 := RingHom.map_det v.embedding ι
    rw [RingHom.mapMatrix_apply] at h1
    rw [hι'def, ← h1, isUnit_iff_ne_zero]
    exact (map_ne_zero _).2 (isUnit_iff_ne_zero.mp hι)
  obtain ⟨GE, hGE⟩ : ∃ G : Matrix (Fin D) (Fin D) ℂ, G = ((XE v)⁻¹)ᴴ * (XE v)⁻¹ := ⟨_, rfl⟩
  obtain ⟨GQ, hGQ⟩ : ∃ G : Matrix (Fin D) (Fin D) ℂ, G = ((XQ v)⁻¹)ᴴ * (XQ v)⁻¹ := ⟨_, rfl⟩
  have hGEH : GEᴴ = GE := by
    rw [hGE, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hGQH : GQᴴ = GQ := by
    rw [hGQ, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  obtain ⟨A, hA⟩ : ∃ M : Matrix (Fin D) (Fin D) ℂ, M = ι'ᴴ * GE * ι' := ⟨_, rfl⟩
  have hAH : Aᴴ = A := by
    rw [hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hGEH, Matrix.mul_assoc]
  have hherm : ∀ M : Matrix (Fin D) (Fin D) ℂ, Mᴴ = M → ∀ a' b' : Fin D → ℂ,
      star (M *ᵥ a') ⬝ᵥ b' = star a' ⬝ᵥ M *ᵥ b' := by
    intro M hM a' b'
    rw [Matrix.star_mulVec, hM, Matrix.dotProduct_mulVec]
  have hfm : ∀ (Y : Matrix (Fin D) (Fin D) ℂ) (a' b' : Fin D → ℂ),
      fmaj Y a' b' = star a' ⬝ᵥ ((Y⁻¹)ᴴ * Y⁻¹) *ᵥ b' := by
    intro Y a' b'
    show star (Y⁻¹ *ᵥ a') ⬝ᵥ (Y⁻¹ *ᵥ b') = _
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  have hemb : ∀ x : Fin D → K,
      (fun i => v.embedding ((ι *ᵥ x) i)) = ι' *ᵥ (fun i => v.embedding (x i)) := by
    intro x
    rw [hι'def]
    exact map_mulVec_emb v ι x
  have hAform : ∀ a' b' : Fin D → ℂ, star (ι' *ᵥ a') ⬝ᵥ GE *ᵥ (ι' *ᵥ b') = star a' ⬝ᵥ A *ᵥ b' := by
    intro a' b'
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA]
  have hsj : ∀ j : Fin D, (fun i => v.embedding ((Pi.single j (1 : K) : Fin D → K) i)) = Pi.single j 1 := by
    intro j
    ext i
    by_cases h : i = j
    · subst h
      simp
    · simp [Pi.single_apply, h]
  have heig : ∀ q, ∀ x ∈ Qp q, A *ᵥ (fun i => v.embedding (x i)) =
      ((s q : ℝ) : ℂ) • (GQ *ᵥ (fun i => v.embedding (x i))) := by
    intro q x hx
    have hrow : star (fun i => v.embedding (x i)) ᵥ* A =
        ((s q : ℝ) : ℂ) • (star (fun i => v.embedding (x i)) ᵥ* GQ) := by
      ext j
      have h1 := hspec q x hx (Pi.single j 1)
      rw [← (frobenius_norm_rational K D XE v (ι *ᵥ x) (ι *ᵥ Pi.single j 1)).2.1,
        ← (frobenius_norm_rational K D XQ v x (Pi.single j 1)).2.1, hfm, hfm, ← hGE, ← hGQ, hemb, hemb,
        hAform, hsj, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec] at h1
      rw [Pi.smul_apply, smul_eq_mul]
      simpa [dotProduct, Pi.single_apply] using h1
    have h2 := congrArg star hrow
    simp only [Matrix.star_vecMul, star_star, star_smul, hAH, hGQH, hstar] at h2
    exact h2
  have hdec : ∀ z : Fin D → K, ∃ f : Ix → Fin D → K, (∀ q, f q ∈ Qp q) ∧ ∑ q, f q = z := by
    intro z
    have hz : z ∈ ⨆ q, Qp q := by
      rw [hsup]
      exact Submodule.mem_top
    classical
    refine Submodule.iSup_induction Qp
      (motive := fun z => ∃ f : Ix → Fin D → K, (∀ q, f q ∈ Qp q) ∧ ∑ q, f q = z) hz ?_ ?_ ?_
    · intro q x hx
      refine ⟨Pi.single q x, fun r => ?_, ?_⟩
      · by_cases h : r = q
        · subst h
          simpa using hx
        · rw [Pi.single_eq_of_ne h]
          exact Submodule.zero_mem _
      · rw [Finset.sum_eq_single q (fun r _ h => by simp [Pi.single_apply, h])
          (fun h => absurd (Finset.mem_univ q) h)]
        simp
    · exact ⟨0, fun q => Submodule.zero_mem _, by simp⟩
    · rintro x y ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
      exact ⟨f + g, fun q => Submodule.add_mem _ (hf q) (hg q), by simp [Finset.sum_add_distrib]⟩
  have hfQ : ∀ u : Fin D → ℂ, ((fnorm (XQ v) u ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ GQ *ᵥ u := by
    intro u
    rw [hGQ]
    exact cnorm_sq_mulVec _ _
  have hfE : ∀ u : Fin D → ℂ, ((fnorm (XE v) (ι' *ᵥ u) ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ A *ᵥ u := by
    intro u
    have e : fnorm (XE v) (ι' *ᵥ u) = Formalism.HermitianLatticesTheory.cnorm (((XE v)⁻¹ * ι') *ᵥ u) := by
      show Formalism.HermitianLatticesTheory.cnorm ((XE v)⁻¹ *ᵥ (ι' *ᵥ u)) = _
      rw [Matrix.mulVec_mulVec]
    rw [e, cnorm_sq_mulVec, hA, hGE, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have SPEC : ∀ w : Fin D → ℂ, smin * fnorm (XQ v) w ^ 2 ≤ fnorm (XE v) (ι' *ᵥ w) ^ 2 := by
    intro w
    choose f hf hfs using fun i : Fin D => hdec (Pi.single i 1)
    have hsum : ∀ i, ∑ q, (fun j => v.embedding (f i q j)) = (Pi.single i 1 : Fin D → ℂ) := by
      intro i
      ext j
      have h1 : (∑ q, f i q) j = (Pi.single i (1 : K) : Fin D → K) j := by rw [hfs i]
      rw [Finset.sum_apply] at h1
      rw [Finset.sum_apply]
      try simp only []
      rw [← map_sum v.embedding, h1]
      by_cases h : j = i
      · subst h
        simp
      · simp [Pi.single_apply, h]
    obtain ⟨W, hW⟩ : ∃ W : Ix → Fin D → ℂ,
        ∀ q, W q = ∑ i, w i • fun j => v.embedding (f i q j) := ⟨_, fun q => rfl⟩
    have hWsum : ∑ q, W q = w := by
      simp only [hW]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, hsum]
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    have hWe : ∀ q, A *ᵥ W q = ((s q : ℝ) : ℂ) • (GQ *ᵥ W q) := by
      intro q
      have heig' : ∀ i, A *ᵥ (fun j => v.embedding (f i q j)) =
          ((s q : ℝ) : ℂ) • (GQ *ᵥ (fun j => v.embedding (f i q j))) := fun i => heig q _ (hf i q)
      rw [hW]
      simp only [Matrix.mulVec_sum, hmsm, heig', Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    have hsym : ∀ q r, ((s q : ℝ) : ℂ) * (star (W q) ⬝ᵥ GQ *ᵥ W r) =
        ((s r : ℝ) : ℂ) * (star (W q) ⬝ᵥ GQ *ᵥ W r) := by
      intro q r
      have e1 : star (W q) ⬝ᵥ A *ᵥ W r = ((s r : ℝ) : ℂ) * (star (W q) ⬝ᵥ GQ *ᵥ W r) := by
        rw [hWe r, hsm2]
      have e2 : star (W q) ⬝ᵥ A *ᵥ W r = ((s q : ℝ) : ℂ) * (star (W q) ⬝ᵥ GQ *ᵥ W r) := by
        rw [← hherm A hAH, hWe q, star_smul, hsm1, hherm GQ hGQH, hstar]
      exact e2.symm.trans e1
    have hterm : ∀ q r, (((s r : ℝ) : ℂ) - (smin : ℂ)) * (star (W q) ⬝ᵥ GQ *ᵥ W r) =
        ((Real.sqrt (s q - smin) : ℝ) : ℂ) * ((Real.sqrt (s r - smin) : ℝ) : ℂ) *
          (star (W q) ⬝ᵥ GQ *ᵥ W r) := by
      intro q r
      by_cases hqr : s q = s r
      · rw [hqr, ← Complex.ofReal_mul, Real.mul_self_sqrt (sub_nonneg.2 (hs r)), Complex.ofReal_sub]
      · have hne : ((s q : ℝ) : ℂ) ≠ ((s r : ℝ) : ℂ) := by exact_mod_cast hqr
        have h0 : star (W q) ⬝ᵥ GQ *ᵥ W r = 0 := by
          have h := hsym q r
          have h' : (((s q : ℝ) : ℂ) - ((s r : ℝ) : ℂ)) * (star (W q) ⬝ᵥ GQ *ᵥ W r) = 0 := by
            rw [sub_mul, h, sub_self]
          rcases mul_eq_zero.mp h' with h'' | h''
          · exact absurd (sub_eq_zero.mp h'') hne
          · exact h''
        rw [h0, mul_zero, mul_zero]
    have hQw : star w ⬝ᵥ GQ *ᵥ w = ∑ q, ∑ r, star (W q) ⬝ᵥ GQ *ᵥ W r := by
      rw [← hWsum]
      simp only [star_sum, hsd, Matrix.mulVec_sum, hds]
    have hEw : star w ⬝ᵥ A *ᵥ w = ∑ q, ∑ r, ((s r : ℝ) : ℂ) * (star (W q) ⬝ᵥ GQ *ᵥ W r) := by
      rw [← hWsum]
      simp only [star_sum, hsd, Matrix.mulVec_sum, hds, hWe, hsm2]
    have hQz : star (∑ q, ((Real.sqrt (s q - smin) : ℝ) : ℂ) • W q) ⬝ᵥ
        GQ *ᵥ (∑ q, ((Real.sqrt (s q - smin) : ℝ) : ℂ) • W q) =
        ∑ q, ∑ r, ((Real.sqrt (s q - smin) : ℝ) : ℂ) * ((Real.sqrt (s r - smin) : ℝ) : ℂ) *
          (star (W q) ⬝ᵥ GQ *ᵥ W r) := by
      simp only [star_sum, hsd, Matrix.mulVec_sum, hds, star_smul, hsm1, hmsm, hsm2, hstar]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
      ring
    have hkey : star w ⬝ᵥ A *ᵥ w - (smin : ℂ) * (star w ⬝ᵥ GQ *ᵥ w) =
        star (∑ q, ((Real.sqrt (s q - smin) : ℝ) : ℂ) • W q) ⬝ᵥ
          GQ *ᵥ (∑ q, ((Real.sqrt (s q - smin) : ℝ) : ℂ) • W q) := by
      rw [hEw, hQw, hQz, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← hterm q r]
      ring
    rw [← hfQ, ← hfE, ← hfQ] at hkey
    have hreal : fnorm (XE v) (ι' *ᵥ w) ^ 2 - smin * fnorm (XQ v) w ^ 2 =
        fnorm (XQ v) (∑ q, ((Real.sqrt (s q - smin) : ℝ) : ℂ) • W q) ^ 2 := by
      exact_mod_cast hkey
    nlinarith [sq_nonneg (fnorm (XQ v) (∑ q, ((Real.sqrt (s q - smin) : ℝ) : ℂ) • W q))]
  rw [operator_norm_dual K a D Xa XE ha hE B v _ hc]
  intro x y
  obtain ⟨F, hF, hFn, -⟩ := quot_rep (H.map v.embedding) (X0 v) (h0 v).1 (h0 v).2
    (P.map v.embedding) (XQ v) (hQ v).1 (hQ v).2 (ι'⁻¹ *ᵥ y)
  have hy : ((ι * P).map v.embedding) *ᵥ F = y := by
    rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, hF, ← hι'def, mul_inv_mulVec _ hι'U]
  have htr := pairC_transfer v B Pt (ι * P) col
    (fun φ F' => by rw [← Matrix.mulVec_mulVec]; exact hB φ F') x F
  rw [hy] at htr
  rw [htr]
  have h3 := (operator_norm_dual K b n Xb X0 hb (fun v => (h0 v).1) Pt v p hp0).mp hp
    ((col.map v.embedding) *ᵥ x) F
  have hop : ∀ {r t : ℕ} (M : Matrix (Fin t) (Fin r) ℂ) (u : Fin r → ℂ),
      Formalism.HermitianLatticesTheory.cnorm (M *ᵥ u) ≤ nrm M * Formalism.HermitianLatticesTheory.cnorm u := by
    intro r t M u
    rw [cnorm_eq, cnorm_eq u]
    unfold nrm
    have e : WithLp.toLp 2 (M *ᵥ u) =
        LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M) (WithLp.toLp 2 u) := by
      simp [Matrix.toEuclideanLin_apply]
    rw [e]
    exact ContinuousLinearMap.le_opNorm _ _
  have h4 : fnorm (Xb v) ((col.map v.embedding) *ᵥ x) ≤ k * fnorm (Xa v) x := by
    have e : (Xb v)⁻¹ *ᵥ ((col.map v.embedding) *ᵥ x) =
        ((Xb v)⁻¹ * col.map v.embedding * Xa v) *ᵥ ((Xa v)⁻¹ *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_right _ _ (ha v)]
    have hnk : nrm ((Xb v)⁻¹ * col.map v.embedding * Xa v) ≤ k := by
      have := hk
      rwa [opNormAt_mulVecLin] at this
    show Formalism.HermitianLatticesTheory.cnorm ((Xb v)⁻¹ *ᵥ ((col.map v.embedding) *ᵥ x)) ≤
      k * Formalism.HermitianLatticesTheory.cnorm ((Xa v)⁻¹ *ᵥ x)
    rw [e]
    exact (hop _ _).trans (mul_le_mul_of_nonneg_right hnk (cnorm_nonneg _))
  have h5 : fnorm (X0 v) F ≤ fnorm (XE v) y / Real.sqrt smin := by
    rw [hFn]
    have hs1 := SPEC (ι'⁻¹ *ᵥ y)
    rw [mul_inv_mulVec _ hι'U] at hs1
    have hq0 : 0 ≤ fnorm (XQ v) (ι'⁻¹ *ᵥ y) := cnorm_nonneg _
    have he0 : 0 ≤ fnorm (XE v) y := cnorm_nonneg _
    have h6 : (fnorm (XQ v) (ι'⁻¹ *ᵥ y) * Real.sqrt smin) ^ 2 ≤ fnorm (XE v) y ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hsmin.le]
      linarith
    have h7 : fnorm (XQ v) (ι'⁻¹ *ᵥ y) * Real.sqrt smin ≤ fnorm (XE v) y := by
      have := Real.sqrt_le_sqrt h6
      rwa [Real.sqrt_sq (mul_nonneg hq0 hr.le), Real.sqrt_sq he0] at this
    first
      | exact (le_div_iff₀ hr).mpr h7
      | exact (le_div_iff hr).mpr h7
  calc ‖pairC v Pt ((col.map v.embedding) *ᵥ x) F‖
      ≤ p * fnorm (Xb v) ((col.map v.embedding) *ᵥ x) * fnorm (X0 v) F := h3
    _ ≤ p * (k * fnorm (Xa v) x) * (fnorm (XE v) y / Real.sqrt smin) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h4 hp0) h5 (cnorm_nonneg _)
          (mul_nonneg hp0 (mul_nonneg hk0 (cnorm_nonneg _)))
    _ = p * k / Real.sqrt smin * fnorm (Xa v) x * fnorm (XE v) y := by ring
end Formalism.DivisionValues.OperatorNormFrames
