-- Prove2me | solution 1 for CatalyticTreeEval.Main.canonical_indexing_matching
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T02:59:04.955384+00:00
-- url     : https://prove2.me/submissions/7c535352-12f3-456e-acc3-ceac7dfd54d4

import Definitions.Def_CatalyticTreeEval_CanonicalCoordinates
import Theorems.Thm_CatalyticTreeEval_Main_composite_weight_detector_properties

set_option autoImplicit false



namespace CatalyticTreeEval.Main

 private theorem weight_subsetPoint {H : ℕ} (T : Finset (Fin H)) : weight (subsetPoint T) = T.card := by
  classical
  unfold weight
  trans ∑ i : Fin H, if i ∈ T then 1 else 0
  · apply Finset.sum_congr rfl
    intro i hi
    by_cases ht : i ∈ T <;> simp [subsetPoint, ht]
  · simp

 private theorem support_restrictPolynomial {m H : ℕ} (T : Finset (Fin H)) (f : Poly m H) :
    (restrictPolynomial T f).support ⊆ f.support :=
  MvPolynomial.support_rename_killCompl_subset Subtype.val_injective

 private theorem restrictPolynomial_multilinear {m H : ℕ} (T : Finset (Fin H)) (f : Poly m H)
    (hf : Multilinear f) : Multilinear (restrictPolynomial T f) := by
  intro v hv i
  exact hf v (support_restrictPolynomial T f hv) i

 private theorem restrictPolynomial_totalDegree_le {m H : ℕ} (T : Finset (Fin H)) (f : Poly m H) :
    (restrictPolynomial T f).totalDegree ≤ f.totalDegree :=
  MvPolynomial.totalDegree_le_of_support_subset (support_restrictPolynomial T f)

 private theorem eval_restrictPolynomial {m H : ℕ} (T : Finset (Fin H)) (f : Poly m H)
    (x : Vec m H) :
    MvPolynomial.eval x (restrictPolynomial T f) =
      MvPolynomial.eval (fun i => if i ∈ T then x i else 0) f := by
  classical
  let inc : {j // j ∈ T} → Fin H := Subtype.val
  have hvar (i : Fin H) :
      MvPolynomial.eval (x ∘ inc)
        ((MvPolynomial.killCompl (f := inc) Subtype.val_injective) (MvPolynomial.X i)) =
      if i ∈ T then x i else 0 := by
    rw [MvPolynomial.killCompl, MvPolynomial.aeval_X]
    by_cases hi : i ∈ T
    · have hr : i ∈ Set.range inc := ⟨⟨i, hi⟩, rfl⟩
      rw [dif_pos hr, MvPolynomial.eval_X, if_pos hi]
      change x (inc ((Equiv.ofInjective inc Subtype.val_injective).symm ⟨i, hr⟩)) = x i
      exact congrArg x (Equiv.apply_ofInjective_symm Subtype.val_injective ⟨i, hr⟩)
    · have hr : i ∉ Set.range inc := by
        rintro ⟨j, rfl⟩
        exact hi j.property
      rw [dif_neg hr, map_zero, if_neg hi]
  rw [restrictPolynomial, MvPolynomial.eval_rename]
  change MvPolynomial.eval (x ∘ inc) (MvPolynomial.killCompl Subtype.val_injective f) = _
  induction f using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.killCompl_C]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf => rw [map_mul, map_mul, map_mul, hf, hvar, MvPolynomial.eval_X]

 private theorem eval_subset_restriction {m H : ℕ} (T U : Finset (Fin H)) (f : Poly m H) :
    MvPolynomial.eval (boolPoint (subsetPoint U)) (restrictPolynomial T f) =
      MvPolynomial.eval (boolPoint (subsetPoint (T ∩ U))) f := by
  classical
  rw [eval_restrictPolynomial]
  have hpoint : (fun i => if i ∈ T then boolPoint (m := m) (subsetPoint U) i else 0) =
      boolPoint (m := m) (subsetPoint (T ∩ U)) := by
    funext i
    by_cases ht : i ∈ T <;> by_cases hu : i ∈ U <;>
      simp [boolPoint, subsetPoint, ht, hu]
  rw [hpoint]

 private theorem inter_card_lt_of_same_card_ne {α : Type*} [DecidableEq α]
    (T U : Finset α) (w : ℕ) (hT : T.card = w) (hU : U.card = w) (hne : T ≠ U) :
    (T ∩ U).card < w := by
  have hle : (T ∩ U).card ≤ w := (Finset.card_le_card Finset.inter_subset_left).trans_eq hT
  apply lt_of_le_of_ne hle
  intro heq
  have hsub : T ⊆ U := by
    have heq' : T ∩ U = T := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by omega)
    intro a ha
    have hmem : a ∈ T ∩ U := heq'.symm ▸ ha
    exact (Finset.mem_inter.mp hmem).2
  exact hne (Finset.eq_of_subset_of_card_le hsub (by omega))

 private theorem detector_subset_polynomial_matching {m H w N : ℕ} (S : Set (ZMod m))
    (f : Poly m H) (T : Fin N → Finset (Fin H))
    (hT : ∀ i, (T i).card = w) (hinj : Function.Injective T)
    (hzero : 0 ∉ S)
    (heval : ∀ x : Fin H → Bool, weight x ≤ w →
      (weight x = w → MvPolynomial.eval (boolPoint x) f = 0) ∧
      (weight x < w → MvPolynomial.eval (boolPoint x) f ∈ S)) :
    PolyMatching S (fun i => restrictPolynomial (T i) f)
      (fun i => boolPoint (subsetPoint (T i))) := by
  refine ⟨hzero, ?_, ?_⟩
  · intro i
    rw [eval_subset_restriction, Finset.inter_self]
    exact (heval _ (by rw [weight_subsetPoint, hT])).1 (by rw [weight_subsetPoint, hT])
  · intro i j hij
    rw [eval_subset_restriction]
    have hlt : weight (subsetPoint (T j ∩ T i)) < w := by
      rw [weight_subsetPoint]
      exact inter_card_lt_of_same_card_ne _ _ _ (hT j) (hT i)
        (fun h => hij (hinj h).symm)
    exact (heval _ hlt.le).2 hlt

end CatalyticTreeEval.Main



namespace CatalyticTreeEval.Main

 private theorem squarefreeMonomial_apply {H : ℕ} (T : Finset (Fin H)) (i : Fin H) :
    squarefreeMonomial T i = if i ∈ T then 1 else 0 := by
  classical
  simp only [squarefreeMonomial, Finsupp.finsetSum_apply, Finsupp.single_apply]
  by_cases hi : i ∈ T <;> simp [hi]

 private theorem squarefreeMonomial_injective {H : ℕ} :
    Function.Injective (squarefreeMonomial (H := H)) := by
  intro T U h
  ext i
  have hi := congrArg (fun v : Monomial H => v i) h
  simp only [squarefreeMonomial_apply] at hi
  by_cases ht : i ∈ T <;> by_cases hu : i ∈ U <;> simp_all

 private theorem squarefreeMonomial_support {H : ℕ} (T : Finset (Fin H)) :
    (squarefreeMonomial T).support = T := by
  classical
  ext i
  simp [Finsupp.mem_support_iff, squarefreeMonomial_apply]

 private theorem squarefreeMonomial_degree {H : ℕ} (T : Finset (Fin H)) :
    (squarefreeMonomial T).sum (fun _ e => e) = T.card := by
  classical
  rw [Finsupp.sum, squarefreeMonomial_support]
  simp [squarefreeMonomial_apply]

 private theorem multilinear_monomial_eq_squarefree {H : ℕ} (v : Monomial H)
    (hv : ∀ i, v i ≤ 1) : v = squarefreeMonomial v.support := by
  classical
  ext i
  rw [squarefreeMonomial_apply]
  by_cases hi : i ∈ v.support
  · rw [if_pos hi]
    have := Finsupp.mem_support_iff.mp hi
    have := hv i
    omega
  · rw [if_neg hi]
    exact Finsupp.notMem_support_iff.mp hi

 private theorem card_smallSubset (H δ : ℕ) : Fintype.card (SmallSubset H δ) = binomialDimension H δ := by
  classical
  simp only [SmallSubset, Fintype.card_sigma, Fintype.card_finset_len, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (n := δ) (fun j : ℕ => H.choose j)

 private theorem smallSubsetMonomial_injective (H δ : ℕ) :
    Function.Injective (fun a : SmallSubset H δ => squarefreeMonomial a.2.val) := by
  intro a b h
  have hT := squarefreeMonomial_injective h
  apply Sigma.subtype_ext
  · apply Fin.ext
    exact a.2.property.symm.trans (congrArg Finset.card hT) |>.trans b.2.property
  · exact hT

 private theorem multilinear_monomials_enumeration (H δ : ℕ) :
    ∃ ms : List (Monomial H), ms.length = binomialDimension H δ ∧ ms.Nodup ∧
      ∀ v : Monomial H, (∀ i, v i ≤ 1) → v.sum (fun _ e => e) < δ → v ∈ ms := by
  classical
  let E : Fin (binomialDimension H δ) ≃ SmallSubset H δ :=
    (Fintype.equivFinOfCardEq (card_smallSubset H δ)).symm
  refine ⟨List.ofFn (fun i => squarefreeMonomial (E i).2.val), List.length_ofFn, ?_, ?_⟩
  · exact List.nodup_ofFn.mpr ((smallSubsetMonomial_injective H δ).comp E.injective)
  · intro v hv hd
    have heq := multilinear_monomial_eq_squarefree v hv
    have hcard : v.support.card < δ := by
      rw [heq, squarefreeMonomial_degree] at hd
      exact hd
    let a : SmallSubset H δ := ⟨⟨v.support.card, hcard⟩, ⟨v.support, rfl⟩⟩
    apply List.mem_ofFn.mpr
    refine ⟨E.symm a, ?_⟩
    rw [E.apply_symm_apply]
    exact heq.symm

 private theorem multilinear_support_enumeration {m H δ : ℕ} (f : Poly m H)
    (hf : Multilinear f) (hd : f.totalDegree < δ) :
    ∃ ms : List (Monomial H), ms.length = binomialDimension H δ ∧ ms.Nodup ∧
      ∀ v ∈ f.support, v ∈ ms := by
  obtain ⟨ms, hlen, hn, hm⟩ := multilinear_monomials_enumeration H δ
  exact ⟨ms, hlen, hn, fun v hv => hm v (hf v hv) ((MvPolynomial.le_totalDegree hv).trans_lt hd)⟩

end CatalyticTreeEval.Main



namespace CatalyticTreeEval.Main

/-- Evaluation can be summed over any finite support cover, setting unused coefficients to zero. -/
private theorem eval_eq_sum_cover {m H : ℕ} (f : Poly m H) (x : Vec m H)
    (s : Finset (Monomial H)) (hcover : f.support ⊆ s) :
    MvPolynomial.eval x f = ∑ v ∈ s, MvPolynomial.coeff v f * monomialValue x v := by
  classical
  rw [MvPolynomial.eval_eq']
  apply Finset.sum_subset hcover
  intro v hv hn
  have hc : MvPolynomial.coeff v f = 0 := by
    simpa using hn
  simp [hc]

/-- The algebraic conversion in Lemma B.4. This does not assume a printer. -/
private theorem coefficient_dot_evaluation {m H : ℕ} (f : Poly m H) (x : Vec m H)
    (ms : List (Monomial H)) (hnodup : ms.Nodup)
    (hcover : ∀ v ∈ f.support, v ∈ ms) :
    coefficientCoordinates f ms ⬝ᵥ evaluationCoordinates x ms = MvPolynomial.eval x f := by
  classical
  rw [eval_eq_sum_cover f x ms.toFinset (by
    intro v hv
    exact List.mem_toFinset.mpr (hcover v hv))]
  change (∑ j : Fin ms.length, MvPolynomial.coeff (ms.get j) f * monomialValue x (ms.get j)) = _
  rw [List.sum_toFinset _ hnodup]
  exact Fin.sum_univ_fun_getElem ms (fun v => MvPolynomial.coeff v f * monomialValue x v)

/-- A polynomial matching family yields matching vectors in any nonduplicated support-covering
monomial order. Uniform access remains a separate computational obligation of Lemma B.4. -/
private theorem polynomial_matching_coordinates {m H N : ℕ} (S₀ : Set (ZMod m))
    (f : Fin N → Poly m H) (x : Fin N → Vec m H) (ms : List (Monomial H))
    (hmatching : PolyMatching S₀ f x) (hnodup : ms.Nodup)
    (hcover : ∀ i, ∀ v ∈ (f i).support, v ∈ ms) :
    SMatching (S₀ ∪ {0})
      (fun i => coefficientCoordinates (f i) ms)
      (fun i => evaluationCoordinates (x i) ms) := by
  classical
  refine ⟨by simp, ⟨?_, ?_⟩, ?_⟩
  · intro i
    rw [coefficient_dot_evaluation (f i) (x i) ms hnodup (hcover i)]
    exact hmatching.2.1 i
  · intro i j hij
    rw [coefficient_dot_evaluation (f i) (x j) ms hnodup (hcover i)]
    intro hzero
    exact hmatching.1 (hzero ▸ hmatching.2.2 j i hij.symm)
  · intro i j hij
    rw [coefficient_dot_evaluation (f i) (x j) ms hnodup (hcover i)]
    exact Or.inl (hmatching.2.2 j i hij.symm)

end CatalyticTreeEval.Main



namespace CatalyticTreeEval.Main

 private theorem coefficient_dot_evaluation_indexed {m H d : ℕ} (f : Poly m H) (x : Vec m H)
    (a : Fin d → Monomial H) (ha : Function.Injective a)
    (hcover : ∀ v ∈ f.support, ∃ j, a j = v) :
    (fun j => MvPolynomial.coeff (a j) f) ⬝ᵥ (fun j => monomialValue x (a j)) =
      MvPolynomial.eval x f := by
  classical
  rw [eval_eq_sum_cover f x (Finset.univ.image a) (by
    intro v hv
    obtain ⟨j, rfl⟩ := hcover v hv
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)]
  rw [Finset.sum_image (fun i _ j _ h => ha h)]
  rfl

 private theorem multilinear_monomials_indexing (H δ : ℕ) :
    ∃ a : Fin (binomialDimension H δ) → Monomial H, Function.Injective a ∧
      ∀ v : Monomial H, (∀ i, v i ≤ 1) → v.sum (fun _ e => e) < δ → ∃ j, a j = v := by
  classical
  let E : Fin (binomialDimension H δ) ≃ SmallSubset H δ :=
    (Fintype.equivFinOfCardEq (card_smallSubset H δ)).symm
  refine ⟨fun i => squarefreeMonomial (E i).2.val,
    (smallSubsetMonomial_injective H δ).comp E.injective, ?_⟩
  intro v hv hd
  have heq := multilinear_monomial_eq_squarefree v hv
  have hcard : v.support.card < δ := by
    rw [heq, squarefreeMonomial_degree] at hd
    exact hd
  let b : SmallSubset H δ := ⟨⟨v.support.card, hcard⟩, ⟨v.support, rfl⟩⟩
  refine ⟨E.symm b, ?_⟩
  change squarefreeMonomial (E (E.symm b)).2.val = v
  rw [E.apply_symm_apply]
  exact heq.symm

 private theorem delta_pos {t : ℕ} (p e : Fin t → ℕ) (hp : PrimeData p) : 0 < delta p e := by
  let i : Fin t := ⟨0, hp.1⟩
  exact (pow_pos (hp.2.1 i).pos _).trans_le
    (Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

 private theorem detector_matching_coordinates {t H w N d : ℕ} (p e : Fin t → ℕ)
    (hp : PrimeData p) (hw : w < ∏ i, p i ^ e i)
    (T : Fin N → Finset (Fin H)) (hT : ∀ i, (T i).card = w)
    (hTi : Function.Injective T) (a : Fin d → Monomial H) (ha : Function.Injective a)
    (hcover : ∀ v : Monomial H, (∀ i, v i ≤ 1) →
      v.sum (fun _ e => e) < delta p e → ∃ j, a j = v) :
    SMatching (canonical p (modulus p))
      (fun i j => MvPolynomial.coeff (a j) (restrictPolynomial (T i)
        (compositeWeightDetector p e hp w H)))
      (fun i j => monomialValue (boolPoint (subsetPoint (T i))) (a j)) := by
  let f := compositeWeightDetector p e hp w H
  have hproperties := composite_weight_detector_properties p e hp w H hw
  have hf : Multilinear f := hproperties.1
  have hd : f.totalDegree < delta p e :=
    hproperties.2.1.trans_lt
      (Nat.sub_lt (delta_pos p e hp) (by decide))
  have hpoly : PolyMatching (canonical p (modulus p) \ {0})
      (fun i => restrictPolynomial (T i) f) (fun i => boolPoint (subsetPoint (T i))) := by
    apply detector_subset_polynomial_matching _ _ T hT hTi
    · simp
    · intro x hx
      exact hproperties.2.2 x hx
  have hdot (i j : Fin N) :
      (fun k => MvPolynomial.coeff (a k) (restrictPolynomial (T i) f)) ⬝ᵥ
        (fun k => monomialValue (boolPoint (subsetPoint (T j))) (a k)) =
      MvPolynomial.eval (boolPoint (subsetPoint (T j))) (restrictPolynomial (T i) f) := by
    apply coefficient_dot_evaluation_indexed _ _ a ha
    intro v hv
    have hmem := support_restrictPolynomial (T i) f hv
    exact hcover v (hf v hmem) ((MvPolynomial.le_totalDegree hmem).trans_lt hd)
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · intro i
    simp
  · intro i
    exact (hdot i i).trans (hpoly.2.1 i)
  · intro i j hij
    rw [hdot]
    exact (hpoly.2.2 j i hij.symm).2
  · intro i j hij
    rw [hdot]
    exact (hpoly.2.2 j i hij.symm).1

 private theorem canonical_matching_algebra {t : ℕ} (p e : Fin t → ℕ) (hp : PrimeData p)
    (w H : ℕ) (hw : w < ∏ i, p i ^ e i) :
    ∃ U V : Fin (H.choose w) → Vec (modulus p) (binomialDimension H (delta p e)),
      SMatching (canonical p (modulus p)) U V := by
  classical
  let E : Fin (H.choose w) ≃ {T : Finset (Fin H) // T.card = w} :=
    (Fintype.equivFinOfCardEq (by simp)).symm
  obtain ⟨a, ha, hcover⟩ := multilinear_monomials_indexing H (delta p e)
  exact ⟨_, _, detector_matching_coordinates p e hp hw (fun i => (E i).val)
    (fun i => (E i).property) (Subtype.val_injective.comp E.injective) a ha hcover⟩

end CatalyticTreeEval.Main



namespace CatalyticTreeEval.Main

private theorem canonical_indexing_matching {t : ℕ} (p e : Fin t → ℕ) (hp : PrimeData p)
    (w H : ℕ) (hw : w < ∏ i, p i ^ e i) (I : CanonicalIndexing H w (delta p e)) :
    SMatching (canonical p (modulus p))
      (canonicalCoefficientVectors p e hp w H I) (canonicalEvaluationVectors p e w H I) :=
  detector_matching_coordinates p e hp hw I.subset I.subset_card I.subset_injective
    I.monomial I.monomial_injective I.monomial_cover

end CatalyticTreeEval.Main

open CatalyticTreeEval.Main

theorem solution {t : ℕ} (p e : Fin t → ℕ) (hp : PrimeData p)
    (w H : ℕ) (hw : w < ∏ i, p i ^ e i) (I : CanonicalIndexing H w (delta p e)) :
    SMatching (canonical p (modulus p))
      (canonicalCoefficientVectors p e hp w H I) (canonicalEvaluationVectors p e w H I) :=
  canonical_indexing_matching p e hp w H hw I
