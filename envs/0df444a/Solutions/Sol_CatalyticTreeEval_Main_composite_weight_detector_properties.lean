-- Prove2me | solution 1 for CatalyticTreeEval.Main.composite_weight_detector_properties
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T02:05:30.27864+00:00
-- url     : https://prove2.me/submissions/fbd106a6-8a9c-45bd-85a2-225853ca4e8e

import Definitions.Def_CatalyticTreeEval_CompositeDetector

set_option autoImplicit false



namespace CatalyticTreeEval.CRT

private theorem modulus_pos {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p) :
    0 < Main.modulus p := by
  exact Finset.prod_pos (fun i _ => (hp.2.1 i).pos)

private theorem project_val {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p)
    (z : ZMod (Main.modulus p)) (i : Fin t) : project p i z = (z.val : ZMod (p i)) := by
  letI : NeZero (Main.modulus p) := ⟨(modulus_pos p hp).ne'⟩
  exact ZMod.cast_eq_val z

private theorem project_crtLift {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p)
    (y : (i : Fin t) → ZMod (p i)) (i : Fin t) :
    project p i (crtLift p hp y) = y i := by
  letI : NeZero (p i) := ⟨(hp.2.1 i).ne_zero⟩
  change project p i (((crtRepresentative p hp y).val : ℕ) : ZMod (Main.modulus p)) = y i
  rw [map_natCast]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).2
    ((crtRepresentative p hp y).property i (Finset.mem_univ i))).trans (ZMod.natCast_zmod_val (y i))

private theorem project_eq_natCast_iff {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p)
    (z : ZMod (Main.modulus p)) (i : Fin t) (n : ℕ) (hn : n < p i) :
    project p i z = (n : ZMod (p i)) ↔ z.val % p i = n := by
  rw [project_val p hp, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hn]

private theorem mem_canonical_iff {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p)
    (z : ZMod (Main.modulus p)) :
    z ∈ Main.canonical p (Main.modulus p) ↔ ∀ i, project p i z = 0 ∨ project p i z = 1 := by
  change (∀ i, z.val % p i = 0 ∨ z.val % p i = 1) ↔ _
  constructor
  · intro h i
    simpa only [← project_eq_natCast_iff p hp z i 0 (hp.2.1 i).pos,
      ← project_eq_natCast_iff p hp z i 1 (hp.2.1 i).one_lt, Nat.cast_zero, Nat.cast_one] using h i
  · intro h i
    rcases h i with hi | hi
    · exact Or.inl ((project_eq_natCast_iff p hp z i 0 (hp.2.1 i).pos).1
        (by simpa only [Nat.cast_zero] using hi))
    · exact Or.inr ((project_eq_natCast_iff p hp z i 1 (hp.2.1 i).one_lt).1
        (by simpa only [Nat.cast_one] using hi))

private theorem project_eq_zero {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p)
    (z : ZMod (Main.modulus p)) (hz : ∀ i, project p i z = 0) : z = 0 := by
  letI : NeZero (Main.modulus p) := ⟨(modulus_pos p hp).ne'⟩
  have hco : (List.finRange t).Pairwise (fun i j => Nat.Coprime (p i) (p j)) := by
    apply (List.nodup_finRange t).pairwise_of_forall_ne
    intro i hi j hj hij
    exact (Nat.coprime_primes (hp.2.1 i) (hp.2.1 j)).2 (fun h => hij (hp.2.2 h))
  have hdiv : ∀ i, p i ∣ z.val := by
    intro i
    apply (ZMod.natCast_eq_zero_iff z.val (p i)).1
    rw [← project_val p hp]
    exact hz i
  have hmod : z.val ≡ 0 [MOD Main.modulus p] := by
    have hmod' := (Nat.modEq_list_map_prod_iff hco).2
      (fun i _ => Nat.modEq_zero_iff_dvd.2 (hdiv i))
    have hprod : Main.modulus p = ((List.finRange t).map p).prod := Fin.prod_univ_def p
    exact Eq.mpr (congrArg (fun n : ℕ => Nat.ModEq n z.val 0) hprod) hmod'
  have hcast : (z.val : ZMod (Main.modulus p)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (Nat.modEq_zero_iff_dvd.1 hmod)
  simpa only [ZMod.natCast_zmod_val] using hcast

private theorem project_injective {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p)
    {a b : ZMod (Main.modulus p)} (h : ∀ i, project p i a = project p i b) : a = b := by
  apply sub_eq_zero.mp
  apply project_eq_zero p hp
  intro i
  rw [map_sub, h i, sub_self]

end CatalyticTreeEval.CRT



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



namespace CatalyticTreeEval.Main

private theorem coeff_crtPolynomial {t H : ℕ} (p : Fin t → ℕ) (hp : PrimeData p)
    (f : (i : Fin t) → Poly (p i) H) (v : Monomial H) :
    MvPolynomial.coeff v (crtPolynomial p hp f) =
      if v ∈ Finset.univ.biUnion (fun i => (f i).support) then
        CRT.crtLift p hp (fun i => MvPolynomial.coeff v (f i)) else 0 := by
  classical
  simp [crtPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]

 private theorem map_crtPolynomial {t H : ℕ} (p : Fin t → ℕ) (hp : PrimeData p)
    (f : (i : Fin t) → Poly (p i) H) (i : Fin t) :
    MvPolynomial.map (CRT.project p i) (crtPolynomial p hp f) = f i := by
  classical
  ext v
  rw [MvPolynomial.coeff_map, coeff_crtPolynomial]
  split_ifs with hv
  · exact CRT.project_crtLift p hp _ i
  · rw [map_zero]
    symm
    apply MvPolynomial.notMem_support_iff.mp
    intro hvi
    exact hv (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hvi⟩)

 private theorem support_crtPolynomial {t H : ℕ} (p : Fin t → ℕ) (hp : PrimeData p)
    (f : (i : Fin t) → Poly (p i) H) :
    (crtPolynomial p hp f).support ⊆ Finset.univ.biUnion (fun i => (f i).support) := by
  classical
  intro v hv
  by_contra h
  apply (MvPolynomial.mem_support_iff.mp hv)
  rw [coeff_crtPolynomial, if_neg h]

 private theorem crtPolynomial_multilinear {t H : ℕ} (p : Fin t → ℕ) (hp : PrimeData p)
    (f : (i : Fin t) → Poly (p i) H) (hf : ∀ i, Multilinear (f i)) :
    Multilinear (crtPolynomial p hp f) := by
  classical
  intro v hv j
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (support_crtPolynomial p hp f hv)
  exact hf i v hi j

 private theorem crtPolynomial_totalDegree_le {t H : ℕ} (p : Fin t → ℕ) (hp : PrimeData p)
    (f : (i : Fin t) → Poly (p i) H) (d : ℕ)
    (hf : ∀ i, (f i).totalDegree ≤ d) : (crtPolynomial p hp f).totalDegree ≤ d := by
  classical
  apply Finset.sup_le
  intro v hv
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (support_crtPolynomial p hp f hv)
  exact (MvPolynomial.le_totalDegree hi).trans (hf i)

 private theorem eval_crtPolynomial {t H : ℕ} (p : Fin t → ℕ) (hp : PrimeData p)
    (f : (i : Fin t) → Poly (p i) H) (x : Fin H → Bool) (i : Fin t) :
    CRT.project p i (MvPolynomial.eval (boolPoint x) (crtPolynomial p hp f)) =
      MvPolynomial.eval (boolPoint x) (f i) := by
  rw [MvPolynomial.map_eval, map_crtPolynomial]
  have hpoint : CRT.project p i ∘ boolPoint x = boolPoint x := by
    funext j
    simp [Function.comp_def, boolPoint]
  rw [hpoint]

 private theorem compositeWeightDetector_project {t : ℕ} (p e : Fin t → ℕ)
    (hp : PrimeData p) (w H : ℕ) (x : Fin H → Bool) (i : Fin t) :
    CRT.project p i (MvPolynomial.eval (boolPoint x) (compositeWeightDetector p e hp w H)) =
      if weight x % (p i) ^ e i = w % (p i) ^ e i then 0 else 1 := by
  rw [compositeWeightDetector, eval_crtPolynomial, weightDetector_eval _ _ _ _ (hp.2.1 i)]

 private theorem compositeWeightDetector_multilinear {t : ℕ} (p e : Fin t → ℕ)
    (hp : PrimeData p) (w H : ℕ) : Multilinear (compositeWeightDetector p e hp w H) :=
  crtPolynomial_multilinear p hp _ (fun i => weightDetector_multilinear _ _ _ _ (hp.2.1 i))

 private theorem compositeWeightDetector_totalDegree_le {t : ℕ} (p e : Fin t → ℕ)
    (hp : PrimeData p) (w H : ℕ) :
    (compositeWeightDetector p e hp w H).totalDegree ≤ delta p e - 1 := by
  apply crtPolynomial_totalDegree_le
  intro i
  apply (weightDetector_totalDegree_le _ _ _ _ (hp.2.1 i)).trans
  apply Nat.sub_le_sub_right
  exact Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

 private theorem compositeWeightDetector_canonical {t : ℕ} (p e : Fin t → ℕ)
    (hp : PrimeData p) (w H : ℕ) (x : Fin H → Bool) :
    MvPolynomial.eval (boolPoint x) (compositeWeightDetector p e hp w H) ∈ canonical p (modulus p) := by
  rw [CRT.mem_canonical_iff p hp]
  intro i
  rw [compositeWeightDetector_project]
  split_ifs <;> simp

 private theorem compositeWeightDetector_zero {t : ℕ} (p e : Fin t → ℕ)
    (hp : PrimeData p) (w H : ℕ) (x : Fin H → Bool) (hx : weight x = w) :
    MvPolynomial.eval (boolPoint x) (compositeWeightDetector p e hp w H) = 0 := by
  apply CRT.project_eq_zero p hp
  intro i
  rw [compositeWeightDetector_project, hx, if_pos rfl]

 private theorem crtPolynomial_symmetric {t H : ℕ} (p : Fin t → ℕ) (hp : PrimeData p)
    (f : (i : Fin t) → Poly (p i) H) (hf : ∀ i, Symmetric (f i)) :
    Symmetric (crtPolynomial p hp f) := by
  intro σ
  ext v
  apply CRT.project_injective p hp
  intro i
  rw [← MvPolynomial.coeff_map, MvPolynomial.map_rename, map_crtPolynomial,
    hf i σ, ← MvPolynomial.coeff_map, map_crtPolynomial]

 private theorem compositeWeightDetector_symmetric {t : ℕ} (p e : Fin t → ℕ)
    (hp : PrimeData p) (w H : ℕ) : Symmetric (compositeWeightDetector p e hp w H) :=
  crtPolynomial_symmetric p hp _ (fun i => weightDetector_symmetric _ _ _ _)

 private theorem compositeWeightDetector_ne_zero {t : ℕ} (p e : Fin t → ℕ)
    (hp : PrimeData p) (w H : ℕ) (hw : w < ∏ i, p i ^ e i)
    (x : Fin H → Bool) (hx : weight x < w) :
    MvPolynomial.eval (boolPoint x) (compositeWeightDetector p e hp w H) ≠ 0 := by
  intro hz
  have hlocal : ∀ i, weight x ≡ w [MOD p i ^ e i] := by
    intro i
    haveI : Fact (Nat.Prime (p i)) := ⟨hp.2.1 i⟩
    have hproj := congrArg (CRT.project p i) hz
    rw [compositeWeightDetector_project, map_zero] at hproj
    by_cases h : weight x % p i ^ e i = w % p i ^ e i
    · exact h
    · rw [if_neg h] at hproj
      exact False.elim (one_ne_zero hproj)
  have hco : (List.finRange t).Pairwise
      (fun i j => Nat.Coprime (p i ^ e i) (p j ^ e j)) := by
    apply (List.nodup_finRange t).pairwise_of_forall_ne
    intro i hi j hj hij
    exact Nat.coprime_pow_primes _ _ (hp.2.1 i) (hp.2.1 j)
      (fun h => hij (hp.2.2 h))
  have hmod : weight x ≡ w [MOD ∏ i, p i ^ e i] := by
    have hmod' := (Nat.modEq_list_map_prod_iff hco).2 (fun i _ => hlocal i)
    have hprod : (∏ i, p i ^ e i) = ((List.finRange t).map (fun i => p i ^ e i)).prod :=
      Fin.prod_univ_def _
    exact Eq.mpr (congrArg (fun n : ℕ => Nat.ModEq n (weight x) w) hprod) hmod'
  have heq : weight x = w := by
    change weight x % (∏ i, p i ^ e i) = w % (∏ i, p i ^ e i) at hmod
    simpa only [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt (hx.trans hw)] using hmod
  exact hx.ne heq

 private theorem composite_weight_detector_properties {t : ℕ} (p e : Fin t → ℕ)
    (hp : PrimeData p) (w H : ℕ) (hw : w < ∏ i, p i ^ e i) :
    Multilinear (compositeWeightDetector p e hp w H) ∧
    (compositeWeightDetector p e hp w H).totalDegree ≤ delta p e - 1 ∧
    (∀ x : Fin H → Bool, weight x ≤ w →
      (weight x = w → MvPolynomial.eval (boolPoint x) (compositeWeightDetector p e hp w H) = 0) ∧
      (weight x < w → MvPolynomial.eval (boolPoint x) (compositeWeightDetector p e hp w H) ∈
        canonical p (modulus p) ∧
        MvPolynomial.eval (boolPoint x) (compositeWeightDetector p e hp w H) ≠ 0)) := by
  refine ⟨compositeWeightDetector_multilinear p e hp w H,
    compositeWeightDetector_totalDegree_le p e hp w H, ?_⟩
  intro x hx
  exact ⟨compositeWeightDetector_zero p e hp w H x,
    fun hlt => ⟨compositeWeightDetector_canonical p e hp w H x,
      compositeWeightDetector_ne_zero p e hp w H hw x hlt⟩⟩

end CatalyticTreeEval.Main

open CatalyticTreeEval.Main

theorem solution {t : ℕ} (p e : Fin t → ℕ)
    (hp : PrimeData p) (w H : ℕ) (hw : w < ∏ i, p i ^ e i) :
    Multilinear (compositeWeightDetector p e hp w H) ∧
    (compositeWeightDetector p e hp w H).totalDegree ≤ delta p e - 1 ∧
    (∀ x : Fin H → Bool, weight x ≤ w →
      (weight x = w → MvPolynomial.eval (boolPoint x) (compositeWeightDetector p e hp w H) = 0) ∧
      (weight x < w → MvPolynomial.eval (boolPoint x) (compositeWeightDetector p e hp w H) ∈
        canonical p (modulus p) ∧
        MvPolynomial.eval (boolPoint x) (compositeWeightDetector p e hp w H) ≠ 0)) := by
  exact composite_weight_detector_properties p e hp w H hw
