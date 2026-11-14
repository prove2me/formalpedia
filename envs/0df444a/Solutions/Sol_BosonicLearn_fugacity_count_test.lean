-- Prove2me | solution 1 for BosonicLearn.fugacity_count_test
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T19:56:30.629784+00:00
-- url     : https://prove2.me/submissions/8369b8d4-7816-4092-982a-b8c91bed5e44

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Theorems.Thm_BosonicLearn_gammaFock_basic
import Theorems.Thm_BosonicLearn_gammaFock_mul
import Theorems.Thm_BosonicLearn_fugacityCoeff_isDensity

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity NuclearExpansion traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.RealRegisters (Hilbert)
open scoped Matrix ComplexOrder ENNReal

open BosonicLearn

noncomputable section

/-- The photon-number sector `N`: occupation vectors of total `N`. -/
private def sec (n N : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range (N + 1)).filter (fun w => ∑ i, w i = N)

private lemma mem_sec {n N : ℕ} (w : Fin n → ℕ) : w ∈ sec n N ↔ ∑ i, w i = N := by
  unfold sec
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun k => ?_, h⟩⟩
  rw [Finset.mem_range, ← h]
  have h2 : w k ≤ ∑ i, w i :=
    Finset.single_le_sum (f := fun i => w i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  omega

private lemma gammaFock_mul_sec {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) :
    gammaFock (A * B) u v = ∑ w ∈ sec n (∑ i, u i), gammaFock A u w * gammaFock B w v :=
  gammaFock_mul A B u v

/-- The action of `Γ(U)` on a coefficient family (a finite sum on each photon-number sector). -/
private def rot {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (g : (Fin n → ℕ) → ℂ) (w : Fin n → ℕ) : ℂ :=
  ∑ u ∈ sec n (∑ i, w i), gammaFock U w u * g u

/-- `Γ(U)† Γ(U) = 1` on each sector. -/
private lemma gamma_unitary_sec {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1)
    (u' u : Fin n → ℕ) :
    ∑ w ∈ sec n (∑ i, u' i), star (gammaFock U w u') * gammaFock U w u =
      if u' = u then 1 else 0 := by
  rw [← (gammaFock_basic (1 : Matrix (Fin n) (Fin n) ℂ) u' u).2.2, ← hU, gammaFock_mul_sec]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [(gammaFock_basic U u' w).2.1]

/-- `Γ(U)` is an isometry on each photon-number sector. -/
private lemma rot_sector_isometry {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1)
    (g : (Fin n → ℕ) → ℂ) (N : ℕ) :
    ∑ w ∈ sec n N, ‖rot U g w‖ ^ 2 = ∑ u ∈ sec n N, ‖g u‖ ^ 2 := by
  have hC : ∑ w ∈ sec n N, star (rot U g w) * rot U g w = ∑ u ∈ sec n N, star (g u) * g u := by
    have h1 : ∀ w ∈ sec n N, star (rot U g w) * rot U g w =
        ∑ u' ∈ sec n N, ∑ u ∈ sec n N,
          star (g u') * g u * (star (gammaFock U w u') * gammaFock U w u) := by
      intro w hw
      unfold rot
      rw [(mem_sec w).mp hw, star_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun u' _ => Finset.sum_congr rfl fun u _ => ?_
      rw [star_mul']
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun u' hu' => ?_
    rw [Finset.sum_comm]
    have h2 : ∀ u, ∑ w ∈ sec n N, star (g u') * g u * (star (gammaFock U w u') * gammaFock U w u) =
        star (g u') * g u * (if u' = u then 1 else 0) := by
      intro u
      rw [← Finset.mul_sum]
      have h3 := gamma_unitary_sec U hU u' u
      rw [(mem_sec u').mp hu'] at h3
      rw [h3]
    rw [Finset.sum_congr rfl fun u _ => h2 u, Finset.sum_eq_single u']
    · simp
    · intro u _ hne
      simp [hne.symm]
    · intro h
      exact absurd hu' h
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.conj_mul']
  exact hC

private lemma lp_sum_sq_le {n : ℕ} (l : Hilbert (Fin n → ℕ)) (G : Finset (Fin n → ℕ)) :
    ∑ u ∈ G, ‖l u‖ ^ 2 ≤ ‖l‖ ^ 2 := by
  have h := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) l G
  simpa using h

/-- Finite partial sums of `|Γ(U) l|²` are bounded by `‖l‖²`. -/
private lemma rot_sum_le {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1)
    (l : Hilbert (Fin n → ℕ)) (s : Finset (Fin n → ℕ)) :
    ∑ w ∈ s, ‖rot U l w‖ ^ 2 ≤ ‖l‖ ^ 2 := by
  set M := s.sup (fun u => ∑ i, u i) with hM
  have hdisj : ((Finset.range (M + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint (sec n) := by
    intro N _ N' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro u hu hu'
    exact hne (((mem_sec u).mp hu).symm.trans ((mem_sec u).mp hu'))
  have hsub : s ⊆ (Finset.range (M + 1)).biUnion (sec n) := by
    intro u hu
    rw [Finset.mem_biUnion]
    refine ⟨∑ i, u i, ?_, (mem_sec u).mpr rfl⟩
    rw [Finset.mem_range]
    have : ∑ i, u i ≤ M := Finset.le_sup (f := fun u : Fin n → ℕ => ∑ i, u i) hu
    omega
  calc ∑ w ∈ s, ‖rot U l w‖ ^ 2
      ≤ ∑ w ∈ (Finset.range (M + 1)).biUnion (sec n), ‖rot U l w‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun u _ _ => by positivity
    _ = ∑ N ∈ Finset.range (M + 1), ∑ w ∈ sec n N, ‖rot U l w‖ ^ 2 := Finset.sum_biUnion hdisj
    _ = ∑ N ∈ Finset.range (M + 1), ∑ u ∈ sec n N, ‖l u‖ ^ 2 :=
        Finset.sum_congr rfl fun N _ => rot_sector_isometry U hU l N
    _ = ∑ u ∈ (Finset.range (M + 1)).biUnion (sec n), ‖l u‖ ^ 2 := (Finset.sum_biUnion hdisj).symm
    _ ≤ ‖l‖ ^ 2 := lp_sum_sq_le l _

private lemma rot_norm_le {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1)
    (l : Hilbert (Fin n → ℕ)) (w : Fin n → ℕ) : ‖rot U l w‖ ≤ ‖l‖ := by
  have h := rot_sum_le U hU l {w}
  rw [Finset.sum_singleton] at h
  exact le_of_sq_le_sq h (norm_nonneg _)

/-- Cauchy–Schwarz for the rotated pair. -/
private lemma rot_cs {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1)
    (l r : Hilbert (Fin n → ℕ)) (s : Finset (Fin n → ℕ)) :
    ∑ w ∈ s, ‖rot U l w‖ * ‖rot U r w‖ ≤ ‖l‖ * ‖r‖ := by
  calc ∑ w ∈ s, ‖rot U l w‖ * ‖rot U r w‖
      ≤ √(∑ w ∈ s, ‖rot U l w‖ ^ 2) * √(∑ w ∈ s, ‖rot U r w‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt s _ _
    _ ≤ √(‖l‖ ^ 2) * √(‖r‖ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt (rot_sum_le U hU l s)) (Real.sqrt_le_sqrt (rot_sum_le U hU r s))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = ‖l‖ * ‖r‖ := by rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- The diagonal of `Γ(U) X Γ(U)†`. -/
private def rotDiag {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ) (w : Fin n → ℕ) : ℂ :=
  ∑ u ∈ sec n (∑ i, w i), ∑ v ∈ sec n (∑ i, w i),
    gammaFock U w u * X u v * star (gammaFock U w v)

/-- The diagonal of the rotated array is bounded in `ℓ¹` by any nuclear expansion. -/
private lemma rotDiag_bound {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1)
    (X : Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ) (e : NuclearExpansion X) (s : Finset (Fin n → ℕ)) :
    ∑ w ∈ s, ‖rotDiag U X w‖ ≤ ∑' k, ‖e.left k‖ * ‖e.right k‖ := by
  have hX : ∀ u v, HasSum (fun k => e.left k u * star (e.right k v)) (X u v) := by
    intro u v
    have hsum : Summable (fun k => e.left k u * star (e.right k v)) := by
      refine Summable.of_norm_bounded e.summable fun k => ?_
      rw [norm_mul, norm_star]
      exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) _ _)
        (lp.norm_apply_le_norm (by norm_num) _ _) (norm_nonneg _) (norm_nonneg _)
    rw [e.coefficients u v]
    exact hsum.hasSum
  have hE : ∀ w, HasSum (fun k => rot U (e.left k) w * star (rot U (e.right k) w))
      (rotDiag U X w) := by
    intro w
    have h : HasSum (fun k => ∑ u ∈ sec n (∑ i, w i), ∑ v ∈ sec n (∑ i, w i),
        gammaFock U w u * (e.left k u * star (e.right k v)) * star (gammaFock U w v))
        (rotDiag U X w) :=
      hasSum_sum fun u _ => hasSum_sum fun v _ => ((hX u v).mul_left _).mul_right _
    refine h.congr_fun fun k => ?_
    unfold rot
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [star_mul']
    ring
  have hs : ∀ w, Summable (fun k => ‖rot U (e.left k) w‖ * ‖rot U (e.right k) w‖) := by
    intro w
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) e.summable
    exact mul_le_mul (rot_norm_le U hU _ w) (rot_norm_le U hU _ w) (norm_nonneg _) (norm_nonneg _)
  calc ∑ w ∈ s, ‖rotDiag U X w‖
      ≤ ∑ w ∈ s, ∑' k, ‖rot U (e.left k) w‖ * ‖rot U (e.right k) w‖ := by
        refine Finset.sum_le_sum fun w _ => ?_
        rw [← (hE w).tsum_eq]
        refine (norm_tsum_le_tsum_norm ?_).trans_eq ?_
        · simpa using hs w
        · simp
    _ = ∑' k, ∑ w ∈ s, ‖rot U (e.left k) w‖ * ‖rot U (e.right k) w‖ :=
        (Summable.tsum_finsetSum fun w _ => hs w).symm
    _ ≤ ∑' k, ‖e.left k‖ * ‖e.right k‖ :=
        Summable.tsum_le_tsum (fun k => rot_cs U hU _ _ s) (summable_sum fun w _ => hs w) e.summable

private lemma one_sub_conj {n : ℕ} (U D : Matrix (Fin n) (Fin n) ℂ) (hU2 : U * Uᴴ = 1) :
    1 - U * D * Uᴴ = U * (1 - D) * Uᴴ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU2]

/-- The diagonal of the rotated fugacity state. -/
private lemma fugacity_rot_diag {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1)
    (R : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℕ) :
    fugacityCoeff (U * R * Uᴴ) w w = rotDiag U (fugacityCoeff R) w := by
  have hU2 : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hdet : (1 - U * R * Uᴴ).det = (1 - R).det := by
    rw [one_sub_conj U R hU2, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
      hU2, Matrix.det_one, one_mul]
  unfold fugacityCoeff rotDiag
  rw [Matrix.smul_apply, hdet, gammaFock_mul_sec, smul_eq_mul, Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [gammaFock_mul_sec, (gammaFock_basic U v w).2.1, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  ring

private lemma rotDiag_sub {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ) (w : Fin n → ℕ) :
    rotDiag U (X - Y) w = rotDiag U X w - rotDiag U Y w := by
  unfold rotDiag
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Matrix.sub_apply]
  ring

/-- Regrouping the thresholded count law. -/
private lemma regroup {n : ℕ} (A : Finset (Fin n)) (τ : ℕ) (f : (Fin n → ℕ) → ℝ)
    (hf : Summable f) :
    (∑' k : ℕ, if τ < k then (∑' w : Fin n → ℕ, if ∑ i ∈ A, w i = k then f w else 0) else 0) =
      ∑' w : Fin n → ℕ, if τ < ∑ i ∈ A, w i then f w else 0 := by
  set F : ℕ → (Fin n → ℕ) → ℝ :=
    fun k w => if τ < k then (if ∑ i ∈ A, w i = k then f w else 0) else 0 with hFdef
  have hF : Summable (Function.uncurry F) := by
    have hinj : Function.Injective
        (fun w : Fin n → ℕ => ((∑ i ∈ A, w i, w) : ℕ × (Fin n → ℕ))) :=
      fun a b h => (Prod.ext_iff.mp h).2
    refine (hinj.summable_iff ?_).mp ?_
    · rintro ⟨k, w⟩ hx
      simp only [Function.uncurry, F]
      split_ifs with h1 h2
      · exact absurd ⟨w, Prod.ext h2 rfl⟩ hx
      · rfl
      · rfl
    · have h : (Function.uncurry F ∘ fun w : Fin n → ℕ => (∑ i ∈ A, w i, w)) =
          Set.indicator {w | τ < ∑ i ∈ A, w i} f := by
        funext w
        simp [Function.uncurry, F, Set.indicator]
      rw [h]
      exact hf.indicator _
  have h := hF.tsum_comm
  calc (∑' k : ℕ, if τ < k then (∑' w : Fin n → ℕ, if ∑ i ∈ A, w i = k then f w else 0) else 0)
      = ∑' k, ∑' w, F k w := by
        refine tsum_congr fun k => ?_
        simp only [F]
        split_ifs <;> simp
    _ = ∑' w, ∑' k, F k w := h.symm
    _ = ∑' w : Fin n → ℕ, if τ < ∑ i ∈ A, w i then f w else 0 := by
        refine tsum_congr fun w => ?_
        rw [tsum_eq_single (∑ i ∈ A, w i)]
        · simp [F]
        · intro k hk
          simp [F, hk.symm]

theorem solution {n : ℕ} (R₁ R₂ : Matrix (Fin n) (Fin n) ℂ) (h₁ : R₁.PosSemidef)
    (h₁' : (1 - R₁).PosDef) (h₂ : R₂.PosSemidef) (h₂' : (1 - R₂).PosDef)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) (A : Finset (Fin n)) (τ : ℕ) :
    ENNReal.ofReal |(∑' k : ℕ, if τ < k then (∑' w : Occupation (Fin n),
          if ∑ i ∈ A, w i = k then (fugacityCoeff (U * R₂ * Uᴴ) w w).re else 0) else 0) -
        ∑' k : ℕ, if τ < k then (∑' w : Occupation (Fin n),
          if ∑ i ∈ A, w i = k then (fugacityCoeff (U * R₁ * Uᴴ) w w).re else 0) else 0| ≤
      traceSize (fugacityCoeff R₂ - fugacityCoeff R₁) := by
  have hU2 : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hsum : ∀ R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef → (1 - R).PosDef →
      Summable (fun w : Fin n → ℕ => (fugacityCoeff (U * R * Uᴴ) w w).re) := by
    intro R hR hR1
    have hpd : (1 - U * R * Uᴴ).PosDef := by
      rw [one_sub_conj U R hU2]
      have h := hR1.conjTranspose_mul_mul_same (B := Uᴴ) (Matrix.mulVec_injective_of_isUnit
        (IsUnit.of_mul_eq_one _ hU))
      rwa [Matrix.conjTranspose_conjTranspose] at h
    exact (fugacityCoeff_isDensity (U * R * Uᴴ) (hR.mul_mul_conjTranspose_same U) hpd).2.2.1
  refine le_iInf fun e => ENNReal.ofReal_le_ofReal ?_
  have hreg₁ := regroup A τ _ (hsum R₁ h₁ h₁')
  have hreg₂ := regroup A τ _ (hsum R₂ h₂ h₂')
  rw [hreg₁, hreg₂]
  have hind : ∀ R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef → (1 - R).PosDef →
      Summable (fun w : Fin n → ℕ =>
        if τ < ∑ i ∈ A, w i then (fugacityCoeff (U * R * Uᴴ) w w).re else 0) :=
    fun R hR hR1 => ((hsum R hR hR1).indicator {w | τ < ∑ i ∈ A, w i}).congr fun w => by
      simp [Set.indicator]
  rw [← Summable.tsum_sub (hind R₂ h₂ h₂') (hind R₁ h₁ h₁')]
  have hterm : ∀ w : Fin n → ℕ,
      (if τ < ∑ i ∈ A, w i then (fugacityCoeff (U * R₂ * Uᴴ) w w).re else 0) -
        (if τ < ∑ i ∈ A, w i then (fugacityCoeff (U * R₁ * Uᴴ) w w).re else 0) =
      if τ < ∑ i ∈ A, w i then (rotDiag U (fugacityCoeff R₂ - fugacityCoeff R₁) w).re else 0 := by
    intro w
    rw [rotDiag_sub, ← fugacity_rot_diag U hU, ← fugacity_rot_diag U hU, Complex.sub_re]
    split_ifs <;> simp
  rw [tsum_congr hterm]
  have hb : ∀ s : Finset (Fin n → ℕ), ∑ w ∈ s,
      |if τ < ∑ i ∈ A, w i then (rotDiag U (fugacityCoeff R₂ - fugacityCoeff R₁) w).re else 0| ≤
      ∑' k, ‖e.left k‖ * ‖e.right k‖ := by
    intro s
    refine le_trans (Finset.sum_le_sum fun w _ => ?_) (rotDiag_bound U hU _ e s)
    split_ifs
    · exact Complex.abs_re_le_norm _
    · simp
  have hsm := summable_of_sum_le (fun _ => abs_nonneg _) hb
  refine le_trans ?_ (hsm.tsum_le_of_sum_le hb)
  have h := norm_tsum_le_tsum_norm (f := fun w : Fin n → ℕ =>
    if τ < ∑ i ∈ A, w i then (rotDiag U (fugacityCoeff R₂ - fugacityCoeff R₁) w).re else 0) hsm
  simpa only [Real.norm_eq_abs] using h
