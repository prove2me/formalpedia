-- Prove2me | solution 1 for CatalyticTreeEval.Main.weight_detector_properties
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T01:47:03.427858+00:00
-- url     : https://prove2.me/submissions/9aafaea6-c172-49a2-bce4-023b82b49f61

import Definitions.Def_CatalyticTreeEval_WeightDetector

set_option autoImplicit false



namespace CatalyticTreeEval.Main

/-- An elementary symmetric polynomial on Boolean inputs counts subsets of the true positions. -/
private theorem esymm_eval_boolPoint (m H j : ℕ) (x : Fin H → Bool) :
    MvPolynomial.eval (boolPoint x) (MvPolynomial.esymm (Fin H) (ZMod m) j) =
      ((weight x).choose j : ZMod m) := by
  classical
  let ones : Finset (Fin H) := Finset.univ.filter fun i => x i
  have hweight : ones.card = weight x := by
    unfold weight
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i hi
    cases x i <;> rfl
  have hprod (T : Finset (Fin H)) :
      (∏ i ∈ T, boolPoint x i : ZMod m) = if T ⊆ ones then 1 else 0 := by
    by_cases ht : T ⊆ ones
    · rw [if_pos ht]
      apply Finset.prod_eq_one
      intro i hi
      have hx : x i = true := (Finset.mem_filter.mp (ht hi)).2
      simp [boolPoint, hx]
    · rw [if_neg ht]
      obtain ⟨i, hi, hn⟩ := Finset.not_subset.mp ht
      have hx : x i = false := by
        cases hxi : x i
        · rfl
        · exact False.elim (hn (by simp [ones, hxi]))
      apply Finset.prod_eq_zero hi
      simp [boolPoint, hx]
  unfold MvPolynomial.esymm
  simp only [map_sum, map_prod, MvPolynomial.eval_X]
  simp_rw [hprod]
  rw [Finset.sum_boole]
  have hf : ((Finset.univ : Finset (Fin H)).powersetCard j).filter (fun T => T ⊆ ones) =
      ones.powersetCard j := by
    ext T
    simp [Finset.mem_powersetCard, and_comm]
  rw [hf, Finset.card_powersetCard, hweight]

private theorem esymm_multilinear (p H j : ℕ) (hp : Nat.Prime p) :
    Multilinear (MvPolynomial.esymm (Fin H) (ZMod p) j) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  classical
  intro v hv i
  rw [MvPolynomial.support_esymm] at hv
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hv
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]
  by_cases hi : i ∈ T <;> simp [hi]

private theorem esymm_totalDegree_le (p H j : ℕ) (hp : Nat.Prime p) :
    (MvPolynomial.esymm (Fin H) (ZMod p) j).totalDegree ≤ j := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  classical
  unfold MvPolynomial.esymm
  apply MvPolynomial.totalDegree_finsetSum_le
  intro T hT
  calc
    (∏ i ∈ T, MvPolynomial.X i : Poly p H).totalDegree ≤
        ∑ i ∈ T, (MvPolynomial.X i : Poly p H).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ = T.card := by simp
    _ = j := (Finset.mem_powersetCard.mp hT).2

private theorem multilinear_sum {m H : ℕ} {ι : Type} (s : Finset ι) (f : ι → Poly m H)
    (hf : ∀ i ∈ s, Multilinear (f i)) : Multilinear (∑ i ∈ s, f i) := by
  classical
  intro v hv j
  have hv' := MvPolynomial.support_sum hv
  obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv'
  exact hf i hi v hvi j

private theorem multilinear_smul {m H : ℕ} (c : ZMod m) (f : Poly m H) (hf : Multilinear f) :
    Multilinear (c • f) := by
  intro v hv j
  exact hf v (MvPolynomial.support_smul hv) j

end CatalyticTreeEval.Main



namespace CatalyticTreeEval.Main

/-- Lucas periodicity in the range below a prime power. -/
private theorem choose_primePower_periodic (p : ℕ) (hp : Nat.Prime p) (e n k : ℕ)
    (hk : k < p ^ e) : n.choose k ≡ (n % p ^ e).choose k [MOD p] := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  induction e generalizing n k with
  | zero =>
      have : k = 0 := by simpa using hk
      subst k
      simp [Nat.ModEq]
  | succ e ih =>
      have hn := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := p)
      have hr := Choose.choose_modEq_choose_mod_mul_choose_div_nat
        (n := n % p ^ (e + 1)) (k := k) (p := p)
      have hmod : (n % p ^ (e + 1)) % p = n % p :=
        Nat.mod_mod_of_dvd n (dvd_pow_self p (by omega : e + 1 ≠ 0))
      have hdiv : (n % p ^ (e + 1)) / p = (n / p) % p ^ e := by
        rw [pow_succ']
        exact Nat.mod_mul_right_div_self n p (p ^ e)
      have hkdiv : k / p < p ^ e := by
        apply (Nat.div_lt_iff_lt_mul hp.pos).2
        simpa [pow_succ] using hk
      have hi := ih (n / p) (k / p) hkdiv
      rw [hmod, hdiv] at hr
      exact hn.trans ((Nat.ModEq.refl ((n % p).choose (k % p))).mul hi |>.trans hr.symm)

/-- The binomial interpolation system has determinant one over every residue ring. -/
private theorem binomialMatrix_det (p q : ℕ) : (binomialMatrix p q).det = 1 := by
  classical
  have htri : (binomialMatrix p q).IsLowerTriangular := by
    intro i j hij
    simp [binomialMatrix, Nat.choose_eq_zero_of_lt (show i.val < j.val from hij)]
  rw [Matrix.det_of_isLowerTriangular _ htri]
  simp [binomialMatrix]

private theorem binomialMatrix_mulVec_detectorCoefficients (p q w : ℕ) :
    (binomialMatrix p q).mulVec (detectorCoefficients p q w) =
      (fun i => if i.val = w % q then 0 else 1) := by
  classical
  unfold detectorCoefficients
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (by rw [binomialMatrix_det]; exact isUnit_one)]
  simp

/-- The detector is invariant under every permutation of its variables. -/
private theorem weightDetector_symmetric (p e w H : ℕ) : Symmetric (weightDetector p e w H) := by
  classical
  intro σ
  simp [weightDetector, MvPolynomial.rename_esymm]

private theorem weightDetector_multilinear (p e w H : ℕ) (hp : Nat.Prime p) :
    Multilinear (weightDetector p e w H) := by
  classical
  unfold weightDetector
  apply multilinear_sum
  intro j hj
  rw [MvPolynomial.C_mul']
  exact multilinear_smul _ _ (esymm_multilinear p H j.val hp)

private theorem weightDetector_totalDegree_le (p e w H : ℕ) (hp : Nat.Prime p) :
    (weightDetector p e w H).totalDegree ≤ p ^ e - 1 := by
  classical
  unfold weightDetector
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  rw [MvPolynomial.C_mul']
  exact ((MvPolynomial.totalDegree_smul_le _ _).trans (esymm_totalDegree_le p H j.val hp)).trans
    (by omega)

private theorem weightDetector_eval (p e w H : ℕ) (hp : Nat.Prime p) (x : Fin H → Bool) :
    MvPolynomial.eval (boolPoint x) (weightDetector p e w H) =
      if weight x % (p ^ e) = w % (p ^ e) then 0 else 1 := by
  classical
  have hq : 0 < p ^ e := Nat.pow_pos hp.pos
  unfold weightDetector
  simp only [map_sum, map_mul, MvPolynomial.eval_C, esymm_eval_boolPoint]
  have hperiod : ∀ j : Fin (p ^ e), ((weight x).choose j.val : ZMod p) =
      ((weight x % p ^ e).choose j.val : ZMod p) := by
    intro j
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2
      (choose_primePower_periodic p hp e (weight x) j.val j.isLt)
  simp_rw [hperiod]
  have h := congrFun (binomialMatrix_mulVec_detectorCoefficients p (p ^ e) w)
    (⟨weight x % p ^ e, Nat.mod_lt _ hq⟩ : Fin (p ^ e))
  simpa [Matrix.mulVec, dotProduct, binomialMatrix, mul_comm] using h

/-- The complete algebraic assertion of Lemma B.5; the sparse printer is a separate task. -/
private theorem prime_power_weight_detector_exists (p e w H : ℕ) (hp : Nat.Prime p) :
    ∃ f : Poly p H, Symmetric f ∧ Multilinear f ∧ f.totalDegree ≤ p ^ e - 1 ∧
      ∀ x : Fin H → Bool, MvPolynomial.eval (boolPoint x) f =
        if weight x % (p ^ e) = w % (p ^ e) then 0 else 1 := by
  exact ⟨weightDetector p e w H, weightDetector_symmetric p e w H,
    weightDetector_multilinear p e w H hp, weightDetector_totalDegree_le p e w H hp,
    weightDetector_eval p e w H hp⟩

end CatalyticTreeEval.Main


open CatalyticTreeEval.Main

theorem solution (p e w H : ℕ) (hp : Nat.Prime p) :
    Symmetric (weightDetector p e w H) ∧ Multilinear (weightDetector p e w H) ∧
      (weightDetector p e w H).totalDegree ≤ p ^ e - 1 ∧
      ∀ x : Fin H → Bool, MvPolynomial.eval (boolPoint x) (weightDetector p e w H) =
        if weight x % (p ^ e) = w % (p ^ e) then 0 else 1 := by
  exact ⟨weightDetector_symmetric p e w H, weightDetector_multilinear p e w H hp,
    weightDetector_totalDegree_le p e w H hp, weightDetector_eval p e w H hp⟩
