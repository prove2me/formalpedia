-- Prove2me | solution 1 for BhangaleHypergraph.Main.outer_soundness
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:36:12.922777+00:00
-- url     : https://prove2.me/submissions/bb797da9-5eb1-4687-a5d3-aa8f3aba2d88

import Definitions.Def_BhangaleHypergraph_Main_Base

open BhangaleHypergraph.Main

private lemma inBall_mono (B : BaseCover) {r s : ℕ} {a : Fin B.A} {v : BaseVertex B}
    (h : InBall B r a v) (hrs : r ≤ s) : InBall B s a v := by
  obtain ⟨k, hkr, walk, hzero, hlast, hadj⟩ := h
  exact ⟨k, hkr.trans hrs, walk, hzero, hlast, hadj⟩

private lemma inBall_center (B : BaseCover) (r : ℕ) (a : Fin B.A) :
    InBall B r a (.inl a) := by
  refine ⟨0, Nat.zero_le _, fun _ => .inl a, rfl, rfl, ?_⟩
  intro j
  exact Fin.elim0 j

private lemma inBall_right (B : BaseCover) {r : ℕ} (hr : 1 ≤ r) (e : Fin B.E) :
    InBall B r (B.left e) (.inr (B.right e)) := by
  refine ⟨1, hr, Fin.cons (.inl (B.left e)) (fun _ => .inr (B.right e)), rfl, rfl, ?_⟩
  intro j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact ⟨e, Or.inl ⟨rfl, rfl⟩⟩

private lemma inBall_prepend_two (B : BaseCover) {r : ℕ} {c a : Fin B.A}
    (u v : BaseVertex B) (h : InBall B r a v)
    (hcu : BaseAdjacent B (.inl c) u) (hua : BaseAdjacent B u (.inl a)) :
    InBall B (r + 2) c v := by
  obtain ⟨k, hkr, walk, hzero, hlast, hadj⟩ := h
  refine ⟨k + 2, by omega, Fin.cons (.inl c) (Fin.cons u walk), ?_, ?_, ?_⟩
  · simp
  · simpa using hlast
  · intro j
    refine Fin.cases ?_ (fun q => ?_) j
    · simpa using hcu
    · refine Fin.cases ?_ (fun p => ?_) q
      · have h1 : (1 : Fin (k + 3)) = (0 : Fin (k + 2)).succ := by
          ext
          simp
        have h2 : (2 : Fin (k + 3)) = (1 : Fin (k + 2)).succ := by
          ext
          simp
        have h1' : (1 : Fin (k + 2)) = (0 : Fin (k + 1)).succ := by
          ext
          simp
        simp only [h1, h2, Fin.cons_succ, Fin.cons_zero, h1', hzero]
        exact hua
      · simpa using hadj p

private lemma radius_add_two_le {ell : ℕ} {i j : Fin ell} (hij : i < j) :
    Radius ell j + 2 ≤ Radius ell i := by
  unfold Radius
  omega

private lemma inBall_source (B : BaseCover) {ell : ℕ} {i j : Fin ell}
    (hij : i < j) (e e' : Fin B.E) (hrr : B.right e = B.right e')
    {v : BaseVertex B} (hv : InBall B (Radius ell j) (B.left e') v) :
    InBall B (Radius ell i) (B.left e) v := by
  apply inBall_mono B (hrs := radius_add_two_le hij)
  apply inBall_prepend_two B (.inr (B.right e)) v hv
  · exact ⟨e, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨e', Or.inr ⟨rfl, congrArg Sum.inr hrr⟩⟩

private lemma projected_centers_eq (B : BaseCover) {ell : ℕ}
    (σ : NeighborhoodLabeling B ell) {i j : Fin ell} (hij : i < j)
    (e e' : Fin B.E) (hrr : B.right e = B.right e')
    (hrest : RestrictionSatisfied B σ i j e e') :
    B.proj e ((σ i (B.left e)).val (.inl (B.left e))) =
      B.proj e' ((σ j (B.left e')).val (.inl (B.left e'))) := by
  have htwo := radius_add_two_le hij
  have hri : 1 ≤ Radius ell i := by omega
  have heL : InBall B (Radius ell i) (B.left e) (.inl (B.left e)) :=
    inBall_center B _ _
  have heR : InBall B (Radius ell i) (B.left e) (.inr (B.right e)) :=
    inBall_right B hri e
  have he'L0 : InBall B (Radius ell j) (B.left e') (.inl (B.left e')) :=
    inBall_center B _ _
  have he'L := inBall_source B hij e e' hrr he'L0
  have he'R : InBall B (Radius ell i) (B.left e) (.inr (B.right e')) := by
    rw [← hrr]
    exact heR
  have he := (σ i (B.left e)).property.2 e heL heR
  have he' := (σ i (B.left e)).property.2 e' he'L he'R
  have hcenter := hrest (.inl (B.left e')) he'L0
  have hright : (σ i (B.left e)).val (.inr (B.right e)) =
      (σ i (B.left e)).val (.inr (B.right e')) := by rw [hrr]
  exact he.trans (hright.trans (he'.symm.trans (congrArg (B.proj e') hcenter)))

private lemma baseFraction_le_baseValue (B : BaseCover) (τ : BaseAssignment B) :
    BaseFraction B τ ≤ BaseValue B := by
  apply le_csSup
  · exact (Set.finite_range (BaseFraction B)).bddAbove
  · exact ⟨τ, rfl⟩

private lemma sum_functions_apply_fin {n d : ℕ} (a : Fin n) (F : Fin d → ℝ) :
    (∑ p : Fin n → Fin d, F (p a)) = (d : ℝ) ^ (n - 1) * (∑ x : Fin d, F x) := by
  rw [Fintype.sum_equiv (Equiv.funSplitAt a (Fin d)) _ (fun z => F z.1) (by intro p; rfl)]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]
  congr 1
  simp [Fintype.card_fin, Fintype.card_subtype_compl]

theorem solution (B : BaseCover) (ell : ℕ) (hell : 2 ≤ ell)
    (hproduced : NeighborhoodProduced B ell) (σ : NeighborhoodLabeling B ell) (i j : Fin ell) (hij : i < j) :
    NeighborhoodPairValue B σ i j ≤ BaseValue B := by
  classical
  have hEpos : 0 < B.E := hproduced.1
  have hE : B.E ≠ 0 := Nat.ne_of_gt hEpos
  let e0 : Fin B.E := ⟨0, hEpos⟩
  have hdeg : 0 < B.degreeB := by
    rw [← B.regularB (B.right e0)]
    apply Finset.card_pos.mpr
    exact ⟨e0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hcardI (b : Fin B.B) :
      Fintype.card {e : Fin B.E // B.right e = b} = B.degreeB := by
    rw [Fintype.card_subtype]
    exact B.regularB b
  let inc (b : Fin B.B) (x : Fin B.degreeB) : Fin B.E :=
    ((Fintype.equivFinOfCardEq (hcardI b)).symm x : Fin B.E)
  have hinc (b : Fin B.B) (x : Fin B.degreeB) : B.right (inc b x) = b :=
    ((Fintype.equivFinOfCardEq (hcardI b)).symm x).property
  let τ (p : Fin B.B → Fin B.degreeB) : BaseAssignment B := fun v =>
    match v with
    | .inl a => (σ i a).val (.inl a)
    | .inr b => B.proj (inc b (p b)) ((σ j (B.left (inc b (p b)))).val
        (.inl (B.left (inc b (p b)))))
  let S (p : Fin B.B → Fin B.degreeB) : Finset (Fin B.E) := Finset.univ.filter fun e =>
    B.proj e (τ p (.inl (B.left e))) = τ p (.inr (B.right e))
  let T (p : Fin B.B → Fin B.degreeB) (b : Fin B.B) : Finset (Fin B.E) :=
    (S p).filter fun e => B.right e = b
  let A (b : Fin B.B) (e' : Fin B.E) : Finset (Fin B.E) := Finset.univ.filter fun e =>
    B.right e = b ∧ B.right e' = b ∧ RestrictionSatisfied B σ i j e e'
  have hA_sub (p : Fin B.B → Fin B.degreeB) (b : Fin B.B) :
      A b (inc b (p b)) ⊆ T p b := by
    intro e he
    obtain ⟨_, he, _, hrest⟩ := Finset.mem_filter.mp he
    apply Finset.mem_filter.mpr
    refine ⟨?_, he⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hrr : B.right e = B.right (inc b (p b)) := he.trans (hinc b (p b)).symm
    have hproj := projected_centers_eq B σ hij e (inc b (p b)) hrr hrest
    change B.proj e ((σ i (B.left e)).val (.inl (B.left e))) = τ p (.inr (B.right e))
    rw [he]
    simpa [τ] using hproj
  have hScard (p : Fin B.B → Fin B.degreeB) :
      (S p).card = ∑ b : Fin B.B, (T p b).card := by
    exact Finset.card_eq_sum_card_fiberwise
      (s := S p) (t := (Finset.univ : Finset (Fin B.B)))
      (f := fun e => B.right e) (by intro e he; simp)
  have hlayer_inc (b : Fin B.B) :
      (∑ e : Fin B.E, ∑ e' : Fin B.E,
        if B.right e = b ∧ B.right e' = b ∧ RestrictionSatisfied B σ i j e e'
        then (1 : ℝ) else 0) = ∑ x : Fin B.degreeB, ((A b (inc b x)).card : ℝ) := by
    rw [Finset.sum_comm]
    calc
      (∑ e' : Fin B.E, ∑ e : Fin B.E,
        if B.right e = b ∧ B.right e' = b ∧ RestrictionSatisfied B σ i j e e'
        then (1 : ℝ) else 0) = ∑ e' : Fin B.E, ((A b e').card : ℝ) := by
          apply Finset.sum_congr rfl
          intro e' _
          simp [A]
      _ = ∑ e' ∈ Finset.univ.filter (fun e' : Fin B.E => B.right e' = b),
          ((A b e').card : ℝ) := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro e' _ hn
          have hne : B.right e' ≠ b := by simpa using hn
          simp [A, hne]
      _ = ∑ e' : {e' : Fin B.E // B.right e' = b}, ((A b e').card : ℝ) := by
          apply Finset.sum_subtype
          intro x
          simp
      _ = ∑ x : Fin B.degreeB, ((A b (inc b x)).card : ℝ) := by
          apply Fintype.sum_equiv (Fintype.equivFinOfCardEq (hcardI b))
          intro e'
          simp [inc]
  have hAvg (b : Fin B.B) :
      (B.degreeB : ℝ) ^ (B.B - 1) *
          (∑ e : Fin B.E, ∑ e' : Fin B.E,
            if B.right e = b ∧ B.right e' = b ∧ RestrictionSatisfied B σ i j e e'
            then (1 : ℝ) else 0) ≤ ∑ p : Fin B.B → Fin B.degreeB, ((T p b).card : ℝ) := by
    rw [hlayer_inc, ← sum_functions_apply_fin]
    apply Finset.sum_le_sum
    intro p _
    exact_mod_cast Finset.card_le_card (hA_sub p b)
  have hAvgTotal :
      (B.degreeB : ℝ) ^ (B.B - 1) *
          (∑ b : Fin B.B, ∑ e : Fin B.E, ∑ e' : Fin B.E,
            if B.right e = b ∧ B.right e' = b ∧ RestrictionSatisfied B σ i j e e'
            then (1 : ℝ) else 0) ≤
        ∑ p : Fin B.B → Fin B.degreeB, ((S p).card : ℝ) := by
    rw [Finset.mul_sum]
    calc
      (∑ b : Fin B.B, (B.degreeB : ℝ) ^ (B.B - 1) *
        (∑ e : Fin B.E, ∑ e' : Fin B.E,
          if B.right e = b ∧ B.right e' = b ∧ RestrictionSatisfied B σ i j e e'
          then (1 : ℝ) else 0)) ≤
          ∑ b : Fin B.B, ∑ p : Fin B.B → Fin B.degreeB, ((T p b).card : ℝ) := by
            exact Finset.sum_le_sum fun b _ => hAvg b
      _ = ∑ p : Fin B.B → Fin B.degreeB, ∑ b : Fin B.B, ((T p b).card : ℝ) :=
        Finset.sum_comm
      _ = ∑ p : Fin B.B → Fin B.degreeB, ((S p).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro p _
        exact_mod_cast (hScard p).symm
  have hfrac (p : Fin B.B → Fin B.degreeB) :
      BaseFraction B (τ p) = ((S p).card : ℝ) / (B.E : ℝ) := by
    simp [BaseFraction, hE, S]
    congr 1
    ext e
    simp
  have hval (p : Fin B.B → Fin B.degreeB) :
      ((S p).card : ℝ) ≤ BaseValue B * (B.E : ℝ) := by
    apply (div_le_iff₀ (by exact_mod_cast hEpos : (0 : ℝ) < B.E)).mp
    rw [← hfrac]
    exact baseFraction_le_baseValue B (τ p)
  have hsumval : (∑ p : Fin B.B → Fin B.degreeB, ((S p).card : ℝ)) ≤
      (B.degreeB : ℝ) ^ B.B * (BaseValue B * (B.E : ℝ)) := by
    calc
      _ ≤ ∑ _p : Fin B.B → Fin B.degreeB, BaseValue B * (B.E : ℝ) := by
        exact Finset.sum_le_sum fun p _ => hval p
      _ = (B.degreeB : ℝ) ^ B.B * (BaseValue B * (B.E : ℝ)) := by
        simp [Fintype.card_fun]
  have hpow : (B.degreeB : ℝ) ^ B.B =
      (B.degreeB : ℝ) ^ (B.B - 1) * B.degreeB := by
    rw [← pow_succ, Nat.sub_add_cancel B.posB]
  have hpowpos : 0 < (B.degreeB : ℝ) ^ (B.B - 1) := by positivity
  have hcancel :
      (∑ b : Fin B.B, ∑ e : Fin B.E, ∑ e' : Fin B.E,
        if B.right e = b ∧ B.right e' = b ∧ RestrictionSatisfied B σ i j e e'
        then (1 : ℝ) else 0) ≤
        (B.degreeB : ℝ) * (BaseValue B * (B.E : ℝ)) := by
    apply le_of_mul_le_mul_left (a := (B.degreeB : ℝ) ^ (B.B - 1)) ?_ hpowpos
    exact hAvgTotal.trans (hsumval.trans_eq (by rw [hpow]; ring))
  have hEcard : B.E = B.B * B.degreeB := by
    have hsum := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin B.E)))
      (t := (Finset.univ : Finset (Fin B.B)))
      (f := fun e => B.right e) (by intro e he; simp)
    simp only [Finset.card_univ, Fintype.card_fin] at hsum
    calc
      B.E = ∑ b : Fin B.B, (Finset.univ.filter fun e => B.right e = b).card := hsum
      _ = ∑ _b : Fin B.B, B.degreeB := by simp [B.regularB]
      _ = B.B * B.degreeB := by simp
  have hEreal : (B.E : ℝ) = (B.B : ℝ) * (B.degreeB : ℝ) := by
    exact_mod_cast hEcard
  have hdenpos : 0 < (B.B : ℝ) * (B.degreeB : ℝ) ^ 2 := by
    apply mul_pos
    · exact_mod_cast B.posB
    · positivity
  rw [NeighborhoodPairValue, if_neg hE]
  apply (div_le_iff₀ hdenpos).2
  calc
    (∑ b : Fin B.B, ∑ e : Fin B.E, ∑ e' : Fin B.E,
      if B.right e = b ∧ B.right e' = b ∧ RestrictionSatisfied B σ i j e e'
      then (1 : ℝ) else 0) ≤
        (B.degreeB : ℝ) * (BaseValue B * (B.E : ℝ)) := hcancel
    _ = BaseValue B * ((B.B : ℝ) * (B.degreeB : ℝ) ^ 2) := by rw [hEreal]; ring
