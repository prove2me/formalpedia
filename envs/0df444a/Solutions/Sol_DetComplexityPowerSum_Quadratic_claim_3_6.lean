-- Prove2me | solution 1 for DetComplexityPowerSum.Quadratic.claim_3_6
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T01:53:39.520136+00:00
-- url     : https://prove2.me/submissions/d66ed560-0ea0-4470-aa31-50058544f2db

import Mathlib
import Definitions.Def_PermanentCubic
import Definitions.Def_DetComplexityPowerSum_Quadratic_KernelNormalizers
open OAI.PermanentBorder
open MvPolynomial
open DetComplexityPowerSum.Quadratic
open Matrix

theorem dc_eval (n : ℕ) (a : Fin n → ℂ) : eval a (powerSum n) = ∑ i, a i ^ n := by
  simp [powerSum]

theorem dc_pderiv (n : ℕ) (a : Fin n → ℂ) (i : Fin n) :
    eval a (pderiv i (powerSum n)) = (n : ℂ) * a i ^ (n - 1) := by
  simp [powerSum, Derivation.leibniz_pow, pderiv_X, Pi.single_apply]

theorem dc_mem_iff (m : ℕ) (a : Fin (m + 2) → ℂ) :
    a ∈ polarSlice (m + 2) ↔
      (a (Fin.castSucc (Fin.last m)) = 1 ∧
        (∀ i : Fin m, a (Fin.castSucc (Fin.castSucc i)) ^ (m + 1) = 1) ∧
        a (Fin.last (m + 1)) ^ (m + 2) = -(1 + ∑ i : Fin m, a (Fin.castSucc (Fin.castSucc i)))) := by
  have hm : ((m + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : m + 2 ≠ 0)
  have hsub : m + 2 - 1 = m + 1 := by omega
  have hpenj : ∀ j : Fin (m + 2), IsPenultimate j → j = Fin.castSucc (Fin.last m) := by
    intro j hj
    simp only [IsPenultimate] at hj
    ext
    simp only [Fin.val_castSucc, Fin.val_last]
    omega
  have hpen0 : IsPenultimate (Fin.castSucc (Fin.last m)) := by
    simp only [IsPenultimate, Fin.val_castSucc, Fin.val_last]
  have hsplit : ∑ i : Fin (m + 2), a i ^ (m + 2) =
      ∑ i : Fin m, a (Fin.castSucc (Fin.castSucc i)) ^ (m + 2) +
        a (Fin.castSucc (Fin.last m)) ^ (m + 2) + a (Fin.last (m + 1)) ^ (m + 2) := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  unfold polarSlice
  simp only [Set.mem_ofPred_eq, dc_eval, dc_pderiv, hsub, hsplit]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hpen : a (Fin.castSucc (Fin.last m)) = 1 := h2 _ hpen0
    have hearly : ∀ i : Fin m, a (Fin.castSucc (Fin.castSucc i)) ^ (m + 1) = 1 := by
      intro i
      have := h3 (Fin.castSucc (Fin.castSucc i)) _
        (by simp only [IsEarly, Fin.val_castSucc]; omega) hpen0
      rw [hpen, one_pow] at this
      exact mul_left_cancel₀ hm this
    refine ⟨hpen, hearly, ?_⟩
    have hx : ∀ i : Fin m, a (Fin.castSucc (Fin.castSucc i)) ^ (m + 2) =
        a (Fin.castSucc (Fin.castSucc i)) := by
      intro i; rw [pow_succ, hearly i, one_mul]
    simp only [hx, hpen, one_pow] at h1
    linear_combination h1
  · rintro ⟨hpen, hearly, hlast⟩
    refine ⟨?_, ?_, ?_⟩
    · have hx : ∀ i : Fin m, a (Fin.castSucc (Fin.castSucc i)) ^ (m + 2) =
          a (Fin.castSucc (Fin.castSucc i)) := by
        intro i; rw [pow_succ, hearly i, one_mul]
      simp only [hx, hpen, one_pow, hlast]
      ring
    · intro j hj
      rw [hpenj j hj]
      exact hpen
    · intro i j hi hj
      rw [hpenj j hj, hpen, one_pow]
      have hi' : i.val < m := by simp only [IsEarly] at hi; omega
      have : i = Fin.castSucc (Fin.castSucc ⟨i.val, hi'⟩) := by ext; simp
      rw [this, hearly]

theorem dc_claim31 {n : ℕ} (hn : 2 ≤ n) :
    (polarSlice n).Finite ∧ (n - 1) ^ (n - 2) ≤ (polarSlice n).ncard := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  set R : Finset ℂ := (Polynomial.nthRoots (m + 1) (1 : ℂ)).toFinset with hR
  have hRmem : ∀ z, z ∈ R ↔ z ^ (m + 1) = 1 := by
    intro z
    rw [hR, Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)]
  have hRcard : R.card = m + 1 := by
    have prim := Complex.isPrimitiveRoot_exp (m + 1) (by omega)
    rw [hR, Multiset.toFinset_card_of_nodup (IsPrimitiveRoot.nthRoots_one_nodup prim),
      IsPrimitiveRoot.card_nthRoots_one prim]
  have hfin : (polarSlice (m + 2)).Finite := by
    let W : Finset ℂ := (Finset.univ : Finset (Fin m → R)).image
      (fun f => -(1 + ∑ i, (f i : ℂ)))
    let U : Finset ℂ := R ∪ {1} ∪ W.biUnion (fun w => (Polynomial.nthRoots (m + 2) w).toFinset)
    apply Set.Finite.subset (Set.Finite.pi (t := fun _ => (U : Set ℂ)) (fun _ => U.finite_toSet))
    intro a ha
    rw [dc_mem_iff] at ha
    obtain ⟨hpen, hearly, hlast⟩ := ha
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Finset.mem_coe]
    intro i
    induction i using Fin.lastCases with
    | last =>
      refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_,
        Finset.mem_image.2 ⟨fun i => ⟨a (Fin.castSucc (Fin.castSucc i)), (hRmem _).2 (hearly i)⟩,
          Finset.mem_univ _, rfl⟩, ?_⟩)
      rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)]
      exact hlast
    | cast i =>
      induction i using Fin.lastCases with
      | last =>
        rw [hpen]
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self 1))
      | cast i =>
        exact Finset.mem_union_left _ (Finset.mem_union_left _ ((hRmem _).2 (hearly i)))
  refine ⟨hfin, ?_⟩
  have hz : ∀ f : Fin m → R, ∃ z : ℂ, z ^ (m + 2) = -(1 + ∑ i, (f i : ℂ)) :=
    fun f => IsAlgClosed.exists_pow_nat_eq _ (by omega)
  choose z hz using hz
  let φ : (Fin m → R) → (Fin (m + 2) → ℂ) := fun f =>
    Fin.snoc (α := fun _ => ℂ) (Fin.snoc (α := fun _ => ℂ) (fun i => (f i : ℂ)) 1) (z f)
  have hφ : ∀ f, φ f ∈ polarSlice (m + 2) := by
    intro f
    rw [dc_mem_iff]
    simp only [φ, Fin.snoc_castSucc, Fin.snoc_last]
    exact ⟨trivial, fun i => (hRmem _).1 (f i).2, hz f⟩
  have hinj : Function.Injective φ := by
    intro f g hfg
    funext i
    have := congrFun hfg (Fin.castSucc (Fin.castSucc i))
    simp only [φ, Fin.snoc_castSucc] at this
    exact Subtype.ext this
  calc (m + 1) ^ m = Fintype.card (Fin m → R) := by
        simp [hRcard]
    _ = (Set.range φ).ncard := by
        rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card]
    _ ≤ (polarSlice (m + 2)).ncard :=
        Set.ncard_le_ncard (Set.range_subset_iff.2 hφ) hfin


theorem dc_eval_affine {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) (a : Fin n → ℂ) :
    eval a (affineMatrixPolynomial m M₀ M) = (pencil M₀ M a).det := by
  unfold affineMatrixPolynomial pencil
  have h0 := RingHom.map_det (eval a)
    (Matrix.of fun i j => C (M₀ i j) + ∑ v, C (M v i j) * X v)
  refine h0.trans ?_
  congr 1
  ext i j
  simp [Matrix.sum_apply, mul_comm]

theorem dc_ker_one_dim {m n : ℕ} (hn0 : n ≠ 0) (A B : Matrix (Fin m) (Fin m) ℂ)
    (hAB : ∀ t : ℂ, (A + t • B).det = (1 + t) ^ n - 1) :
    ∃ u0 v0 : Fin m → ℂ, (∀ u, u ᵥ* A = 0 → ∃ c : ℂ, u = c • u0) ∧
      (∀ v, A *ᵥ v = 0 → ∃ c : ℂ, v = c • v0) := by
  obtain ⟨L, L', D, hA⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec A
  have hP := Matrix.TransvectionStruct.det_toMatrix_prod L
  have hQ := Matrix.TransvectionStruct.det_toMatrix_prod L'
  generalize (L.map Matrix.TransvectionStruct.toMatrix).prod = P at hA hP
  generalize (L'.map Matrix.TransvectionStruct.toMatrix).prod = Q at hA hQ
  subst hA
  have hPu : IsUnit P.det := by rw [hP]; exact isUnit_one
  have hQu : IsUnit Q.det := by rw [hQ]; exact isUnit_one
  have claim : ∀ i1 i2, D i1 = 0 → D i2 = 0 → i1 = i2 := by
    intro i1 i2 h01 h02
    by_contra hne
    obtain ⟨B', hB⟩ : ∃ B', P * B' * Q = B := by
      refine ⟨P⁻¹ * B * Q⁻¹, ?_⟩
      calc P * (P⁻¹ * B * Q⁻¹) * Q = (P * P⁻¹) * B * (Q⁻¹ * Q) := by
            simp only [Matrix.mul_assoc]
        _ = B := by
            rw [Matrix.mul_nonsing_inv _ hPu, Matrix.nonsing_inv_mul _ hQu, Matrix.one_mul,
              Matrix.mul_one]
    subst hB
    have hdet : ∀ t : ℂ, (diagonal D + t • B').det = (1 + t) ^ n - 1 := by
      intro t
      rw [← hAB t]
      have h3 : P * diagonal D * Q + t • (P * B' * Q) = P * (diagonal D + t • B') * Q := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
      rw [h3, det_mul, det_mul, hP, hQ, one_mul, mul_one]
    let N : ℂ → Matrix (Fin m) (Fin m) ℂ := fun t =>
      of fun i j => if i = i1 ∨ i = i2 then B' i j else (diagonal D + t • B') i j
    have hfact : ∀ t : ℂ, (diagonal D + t • B').det = t ^ 2 * (N t).det := by
      intro t
      have hv : (∏ i : Fin m, ((if i = i1 then t else 1) * (if i = i2 then t else 1))) = t ^ 2 := by
        rw [Finset.prod_mul_distrib]; simp [sq]
      have hmat : diagonal D + t • B' =
          of fun i j => ((if i = i1 then t else 1) * (if i = i2 then t else 1)) * N t i j := by
        ext i j
        by_cases h1 : i = i1
        · rw [h1]; simp [N, hne, diagonal_apply, h01]
        · by_cases h2 : i = i2
          · rw [h2]; simp [N, Ne.symm hne, diagonal_apply, h02]
          · simp [N, h1, h2]
      conv_lhs => rw [hmat]
      rw [det_mul_column, hv]
    have hgeo : ∀ t : ℂ, t * ∑ k ∈ Finset.range n, (1 + t) ^ k = (1 + t) ^ n - 1 := by
      intro t
      have h3 := mul_geom_sum (1 + t) n
      simpa using h3
    have hNc : Continuous N := by
      refine continuous_matrix (fun i j => ?_)
      by_cases h : i = i1 ∨ i = i2
      · simp only [N, of_apply, if_pos h]; exact continuous_const
      · simp only [N, of_apply, if_neg h, Matrix.add_apply, Matrix.smul_apply]; fun_prop
    have hfun : (fun t : ℂ => ∑ k ∈ Finset.range n, (1 + t) ^ k) = fun t => t * (N t).det := by
      refine Continuous.ext_on (dense_compl_singleton (0 : ℂ)) (by fun_prop)
        (Continuous.mul continuous_id' hNc.matrix_det) ?_
      intro t ht
      have ht0 : t ≠ 0 := ht
      have h3 := (hgeo t).trans ((hdet t).symm.trans (hfact t))
      show ∑ k ∈ Finset.range n, (1 + t) ^ k = t * (N t).det
      apply mul_left_cancel₀ ht0
      rw [h3]; ring
    have h0 : (n : ℂ) = 0 := by
      have h3 := congrFun hfun 0
      simpa using h3
    exact hn0 (by exact_mod_cast h0)
  obtain ⟨z, hz⟩ : ∃ z : Fin m → ℂ, ∀ w : Fin m → ℂ, (∀ i, w i * D i = 0) →
      ∃ c : ℂ, w = c • z := by
    by_cases hex : ∃ i0, D i0 = 0
    · obtain ⟨i0, hi0⟩ := hex
      refine ⟨Pi.single i0 1, fun w hw => ⟨w i0, ?_⟩⟩
      funext i
      by_cases hi : i = i0
      · rw [hi]; simp
      · have hDi : D i ≠ 0 := fun hD => hi (claim i i0 hD hi0)
        have h3 : w i = 0 := (mul_eq_zero.mp (hw i)).resolve_right hDi
        simp [hi, h3]
    · refine ⟨0, fun w hw => ⟨0, ?_⟩⟩
      funext i
      have hDi : D i ≠ 0 := fun hD => hex ⟨i, hD⟩
      have h3 : w i = 0 := (mul_eq_zero.mp (hw i)).resolve_right hDi
      simp [h3]
  refine ⟨z ᵥ* P⁻¹, Q⁻¹ *ᵥ z, ?_, ?_⟩
  · intro u hu
    have h1 : (u ᵥ* P) ᵥ* diagonal D = 0 := by
      calc (u ᵥ* P) ᵥ* diagonal D = u ᵥ* (P * diagonal D * (Q * Q⁻¹)) := by
            rw [Matrix.mul_nonsing_inv _ hQu, Matrix.mul_one, vecMul_vecMul]
        _ = (u ᵥ* (P * diagonal D * Q)) ᵥ* Q⁻¹ := by
            rw [vecMul_vecMul, Matrix.mul_assoc (P * diagonal D)]
        _ = 0 := by rw [hu, zero_vecMul]
    obtain ⟨c, hc⟩ := hz (u ᵥ* P) (fun i => by
      have h3 := congrFun h1 i
      rw [vecMul_diagonal] at h3
      exact h3)
    refine ⟨c, ?_⟩
    calc u = (u ᵥ* P) ᵥ* P⁻¹ := by
          rw [vecMul_vecMul, Matrix.mul_nonsing_inv _ hPu, vecMul_one]
      _ = c • (z ᵥ* P⁻¹) := by rw [hc, smul_vecMul]
  · intro v hv
    have h1 : diagonal D *ᵥ (Q *ᵥ v) = 0 := by
      calc diagonal D *ᵥ (Q *ᵥ v) = ((P⁻¹ * P) * (diagonal D * Q)) *ᵥ v := by
            rw [Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul, mulVec_mulVec]
        _ = P⁻¹ *ᵥ ((P * diagonal D * Q) *ᵥ v) := by
            rw [mulVec_mulVec]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hv, mulVec_zero]
    obtain ⟨c, hc⟩ := hz (Q *ᵥ v) (fun i => by
      have h3 := congrFun h1 i
      rw [mulVec_diagonal] at h3
      rw [mul_comm]; exact h3)
    refine ⟨c, ?_⟩
    calc v = Q⁻¹ *ᵥ (Q *ᵥ v) := by
          rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hQu, one_mulVec]
      _ = c • (Q⁻¹ *ᵥ z) := by rw [hc, mulVec_smul]

theorem dc_avoid {α : Type*} {m : ℕ} (s : Finset α) (w : α → Fin m → ℂ) :
    ∃ g : Fin m → ℂ, ∀ a ∈ s, w a ≠ 0 → g ⬝ᵥ w a ≠ 0 := by
  classical
  let p : α → Polynomial ℂ := fun a =>
    ∑ i : Fin m, Polynomial.C (w a i) * Polynomial.X ^ (i : ℕ)
  have hp : ∀ a, w a ≠ 0 → p a ≠ 0 := by
    intro a ha h0
    apply ha
    funext i
    have hc : (p a).coeff (i : ℕ) = w a i := by
      simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        have h3 : (i : ℕ) ≠ (j : ℕ) := fun h => hj (Fin.ext h.symm)
        simp [h3]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [← hc, h0]; simp
  have hq : (∏ a ∈ s.filter (fun a => w a ≠ 0), p a) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun a ha => hp a (Finset.mem_filter.mp ha).2)
  obtain ⟨t, ht⟩ : ∃ t, Polynomial.eval t (∏ a ∈ s.filter (fun a => w a ≠ 0), p a) ≠ 0 := by
    by_contra h
    push Not at h
    refine hq (Polynomial.eq_zero_of_infinite_isRoot _ ?_)
    have h3 : {x | Polynomial.IsRoot (∏ a ∈ s.filter (fun a => w a ≠ 0), p a) x} = Set.univ :=
      Set.eq_univ_of_forall h
    rw [h3]; exact Set.infinite_univ
  refine ⟨fun i => t ^ (i : ℕ), fun a ha hwa => ?_⟩
  have h1 : Polynomial.eval t (p a) ≠ 0 := by
    intro h0
    apply ht
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨ha, hwa⟩) h0
  have h2 : Polynomial.eval t (p a) = (fun i : Fin m => t ^ (i : ℕ)) ⬝ᵥ w a := by
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, dotProduct]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rwa [h2] at h1

theorem solution {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) (hn : 2 ≤ n)
    (hrep : affineMatrixPolynomial m M₀ M = powerSum n) :
    ∃ g h : Fin m → ℂ, NormalizesKernels M₀ M g h := by
  have hfin : (polarSlice n).Finite := (dc_claim31 hn).1
  have hn0 : n ≠ 0 := by omega
  let j0 : Fin n := ⟨n - 2, by omega⟩
  have hj0 : IsPenultimate j0 := by
    show n - 2 + 2 = n
    omega
  have key : ∀ a : Fin n → ℂ, ∃ u0 v0 : Fin m → ℂ, a ∈ polarSlice n →
      ((∀ u, u ᵥ* pencil M₀ M a = 0 → ∃ c : ℂ, u = c • u0) ∧
        (∀ v, pencil M₀ M a *ᵥ v = 0 → ∃ c : ℂ, v = c • v0)) := by
    intro a
    by_cases ha : a ∈ polarSlice n
    · have hF : ∑ i, a i ^ n = 0 := by
        have h3 := ha.1
        rwa [dc_eval] at h3
      have haj : a j0 = 1 := ha.2.1 j0 hj0
      have hAB : ∀ t : ℂ, (pencil M₀ M a + t • M j0).det = (1 + t) ^ n - 1 := by
        intro t
        have hpen : pencil M₀ M (a + Pi.single j0 t) = pencil M₀ M a + t • M j0 := by
          unfold pencil
          simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
          rw [add_assoc]
          congr 2
          rw [Finset.sum_eq_single j0]
          · simp
          · intro i _ hi
            simp [hi]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [← hpen, ← dc_eval_affine, hrep, dc_eval]
        have hterm : ∀ i, (a + Pi.single j0 t : Fin n → ℂ) i ^ n
            = a i ^ n + (if i = j0 then (1 + t) ^ n - 1 else 0) := by
          intro i
          by_cases h : i = j0
          · rw [h]; simp [haj]
          · simp [h]
        simp only [hterm, Finset.sum_add_distrib, hF, zero_add]
        simp
      obtain ⟨u0, v0, h1, h2⟩ := dc_ker_one_dim hn0 _ _ hAB
      exact ⟨u0, v0, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, 0, fun h => absurd h ha⟩
  choose u0 v0 huv using key
  obtain ⟨g, hg⟩ := dc_avoid hfin.toFinset u0
  obtain ⟨h, hh⟩ := dc_avoid hfin.toFinset v0
  refine ⟨g, h, fun u hu => ?_, fun v hv => ?_⟩
  · obtain ⟨a, ha, hu0, hu⟩ := hu
    obtain ⟨c, hc⟩ := (huv a ha).1 u hu
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hu0 (by rw [hc, zero_smul])
    have hu0' : u0 a ≠ 0 := by
      intro h0
      exact hu0 (by rw [hc, h0, smul_zero])
    rw [hc, dotProduct_smul, smul_eq_mul]
    exact mul_ne_zero hc0 (hg a (hfin.mem_toFinset.mpr ha) hu0')
  · obtain ⟨a, ha, hv0, hv⟩ := hv
    obtain ⟨c, hc⟩ := (huv a ha).2 v hv
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hv0 (by rw [hc, zero_smul])
    have hv0' : v0 a ≠ 0 := by
      intro h0
      exact hv0 (by rw [hc, h0, smul_zero])
    rw [hc, dotProduct_smul, smul_eq_mul]
    exact mul_ne_zero hc0 (hh a (hfin.mem_toFinset.mpr ha) hv0')
