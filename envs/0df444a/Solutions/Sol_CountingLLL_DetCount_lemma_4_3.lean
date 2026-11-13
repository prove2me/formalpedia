-- Prove2me | solution 1 for CountingLLL.DetCount.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:30:38.484533+00:00
-- url     : https://prove2.me/submissions/f964ca62-af58-4a1d-abb1-b19885989c40

import Theorems.Thm_CountingLLL_DetCount_corollary_2_6
import Theorems.Thm_CountingLLL_DetCount_lemma_3_6
import Theorems.Thm_CountingLLL_DetCount_lemma_3_1
import Theorems.Thm_CountingLLL_DetCount_lemma_3_5

set_option autoImplicit false
open CountingLLL.DetCount
open CountingLLL.DetCount.CSP
open scoped Classical

private theorem nbr_card_bound (Φ : CSP) (E : Finset (Fin Φ.m)) (v : Fin Φ.m) :
    (Φ.nbr E v).card ≤ Φ.Dmax := by
  classical
  have hs : Φ.nbr E v ⊆ Φ.nbr Finset.univ v := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'.2⟩
  apply (Finset.card_le_card hs).trans
  unfold CSP.Dmax CSP.Dsub
  exact Finset.le_sup (f := fun c => (Φ.nbr Finset.univ c).card) (Finset.mem_univ v)

private theorem depGraph_degree_bound (Φ : CSP) (E : Finset (Fin Φ.m)) (v : Fin Φ.m) :
    (Φ.depGraph E).degree v ≤ Φ.Dmax := by
  classical
  by_cases hv : v ∈ E
  · have h : (Φ.depGraph E).neighborFinset v = Φ.nbr E v := by
      ext w
      rw [SimpleGraph.mem_neighborFinset]
      change (v ∈ E ∧ w ∈ E ∧ v ≠ w ∧ Φ.Overlap v w) ↔ w ∈ Φ.nbr E v
      simp only [CSP.nbr, Finset.mem_filter, hv, true_and]
      constructor
      · rintro ⟨hw, hne, hov⟩
        exact ⟨hw, hne.symm, hov⟩
      · rintro ⟨hw, hne, hov⟩
        exact ⟨hw, hne.symm, hov⟩
    change ((Φ.depGraph E).neighborFinset v).card ≤ Φ.Dmax
    rw [h]
    exact nbr_card_bound Φ E v
  · have h : (Φ.depGraph E).neighborFinset v = ∅ := by
      ext w
      rw [SimpleGraph.mem_neighborFinset]
      change (v ∈ E ∧ w ∈ E ∧ v ≠ w ∧ Φ.Overlap v w) ↔ w ∈ (∅ : Finset (Fin Φ.m))
      simp [hv]
    change ((Φ.depGraph E).neighborFinset v).card ≤ Φ.Dmax
    rw [h]
    simp

/-- Source Corollary 2.6 specialized to subfamilies and parent degree. -/
theorem num_trees_of_size (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (k : ℕ) :
    (((Φ.twoTrees E r).filter (fun T => T.card = k)).card : ℝ) ≤
      (Real.exp 1 * (Φ.Dmax : ℝ)^2)^(k-1) := by
  classical
  let H : Set (Finset (Fin Φ.m)) := {T | r ∈ T ∧ T.card = k ∧ IsTwoTree (Φ.depGraph E) T}
  have hcor := corollary_2_6 (Φ.depGraph E) Φ.Dmax (depGraph_degree_bound Φ E) r k
  have hsubset : (↑((Φ.twoTrees E r).filter (fun T => T.card = k)) : Set _) ⊆ H := by
    intro T hT
    have hh := Finset.mem_filter.mp hT
    have hi := Finset.mem_filter.mp hh.1
    exact ⟨hi.2.1, hh.2, hi.2.2⟩
  have hcard := Set.ncard_le_ncard hsubset hcor.1
  rw [Set.ncard_coe_finset] at hcard
  have hcast : (((Φ.twoTrees E r).filter (fun T => T.card = k)).card : ℝ) ≤ (H.ncard : ℝ) := by
    exact_mod_cast hcard
  exact hcast.trans hcor.2

/-- Summing the two-tree counting bound yields the uniform geometric estimate. -/
theorem tree_power_sum (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (b : ℝ)
    (hb : 0 ≤ b) (hq : Real.exp 1 * (Φ.Dmax : ℝ)^2 * b < 1) :
    (∑ T ∈ Φ.twoTrees E r, b^T.card) ≤
      b / (1 - Real.exp 1 * (Φ.Dmax : ℝ)^2 * b) := by
  classical
  let A : ℝ := Real.exp 1 * (Φ.Dmax : ℝ)^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hq0 : 0 ≤ A*b := mul_nonneg hA hb
  have hq1 : A*b < 1 := hq
  have hm : ∀ T ∈ Φ.twoTrees E r, T.card < E.card + 1 := by
    intro T hT
    have hTE : T ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    have hh := Finset.card_le_card hTE
    omega
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (s := Φ.twoTrees E r) (t := Finset.range (E.card+1)) (g := Finset.card)
    (fun T hT => Finset.mem_range.mpr (hm T hT)) (fun T => b^T.card)
  have hcount0 : ((Φ.twoTrees E r).filter (fun T => T.card = 0)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro T hT
    have hh := Finset.mem_filter.mp hT
    have hrT := (Finset.mem_filter.mp hh.1).2.1
    have hp : 0 < T.card := Finset.card_pos.mpr ⟨r, hrT⟩
    omega
  have hgroup' : (∑ T ∈ Φ.twoTrees E r, b^T.card) =
      ∑ k ∈ Finset.range (E.card+1),
        (((Φ.twoTrees E r).filter (fun T => T.card = k)).card : ℝ) * b^k := by
    rw [← hgroup]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      _ = ∑ _T ∈ (Φ.twoTrees E r).filter (fun T => T.card = k), b^k := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [(Finset.mem_filter.mp hT).2]
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  rw [hgroup', Finset.sum_range_succ']
  simp only [hcount0, Nat.cast_zero, zero_mul, add_zero]
  calc
    _ ≤ ∑ k ∈ Finset.range E.card, b * (A*b)^k := by
      apply Finset.sum_le_sum
      intro k hk
      have hc := num_trees_of_size Φ E r (k+1)
      have hc' : (((Φ.twoTrees E r).filter (fun T => T.card = k+1)).card : ℝ) ≤ A^k := by
        simpa [A] using hc
      have hh := mul_le_mul_of_nonneg_right hc' (pow_nonneg hb (k+1))
      calc
        _ ≤ A^k * b^(k+1) := hh
        _ = b * (A*b)^k := by rw [pow_succ, mul_pow]; ring
    _ = b * ∑ k ∈ Finset.range E.card, (A*b)^k := by rw [Finset.mul_sum]
    _ ≤ b * (1 / (1-A*b)) := by
      apply mul_le_mul_of_nonneg_left _ hb
      have hg := geom_sum_Ico_le_of_lt_one (m := 0) (n := E.card) hq0 hq1
      simpa [Nat.Ico_zero_eq_range] using hg
    _ = _ := by simp [A, div_eq_mul_inv]


/-- Uniform constants for the proof of Lemma 4.3. The factor 1.25 replaces
an overly sharp source bound 1.22 and remains valid when D = 0. -/
theorem estimator_constants (p : ℝ) (D : ℕ) (hp : 0 ≤ p)
    (hcondition : 4 * Real.exp 1 * p * ((D : ℝ) + 1)^2 ≤ 1) :
    let β : ℝ := p / (1 - 2*p)^((D+1)^2)
    let α : ℝ := 2.1*((D : ℝ)+1)^2
    0 ≤ β ∧ β ≤ 1.25*p ∧ Real.exp 1 * (D : ℝ)^2 * β ≤ 0.32 ∧ α*β ≤ 0.25 := by
  dsimp only
  let A : ℝ := ((D : ℝ)+1)^2
  have hA : 1 ≤ A := by
    dsimp [A]
    have hd : 0 ≤ (D : ℝ) := Nat.cast_nonneg _
    nlinarith [sq_nonneg (D : ℝ)]
  have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hpa : 0 ≤ p*A := mul_nonneg hp (by linarith)
  have hbound : 2 * p * A ≤ 1/5 := by
    have hh : 0 ≤ (4 * Real.exp 1 - 10) * (p*A) := mul_nonneg (by linarith) hpa
    change 4 * Real.exp 1 * p * A ≤ 1 at hcondition
    nlinarith
  have hpA : p ≤ p*A := by nlinarith [mul_nonneg hp (show 0 ≤ A-1 by linarith)]
  have hq : 0 < 1-2*p := by nlinarith
  have hbernoulli := one_add_mul_sub_le_pow (a := (1-2*p : ℝ)) (by linarith) ((D+1)^2)
  have hqpow : (4/5 : ℝ) ≤ (1-2*p)^((D+1)^2) := by
    push_cast at hbernoulli
    change 1 + A * ((1 - 2*p) - 1) ≤ _ at hbernoulli
    nlinarith
  have hqpow_pos : 0 < (1-2*p)^((D+1)^2) := by positivity
  have hβnonneg : 0 ≤ p / (1-2*p)^((D+1)^2) := div_nonneg hp (le_of_lt hqpow_pos)
  have hβupper : p / (1-2*p)^((D+1)^2) ≤ 1.25*p := by
    apply (div_le_iff₀ hqpow_pos).2
    nlinarith [mul_nonneg hp (show 0 ≤ (1-2*p)^((D+1)^2) - 4/5 by linarith)]
  have hrealD : 0 ≤ (D : ℝ) := Nat.cast_nonneg _
  have hDsquare : (D : ℝ)^2 ≤ A := by dsimp [A]; nlinarith
  have hE : 0 < Real.exp 1 := Real.exp_pos _
  have hratio : Real.exp 1 * (D : ℝ)^2 * (p / (1-2*p)^((D+1)^2)) ≤ 0.32 := by
    have hh := mul_le_mul_of_nonneg_left hβupper (show 0 ≤ Real.exp 1 * (D : ℝ)^2 by positivity)
    have hm := mul_nonneg (show 0 ≤ A - (D : ℝ)^2 by linarith) (mul_nonneg hE.le hp)
    change 4 * Real.exp 1 * p * A ≤ 1 at hcondition
    nlinarith
  have halpha : 2.1 * A * (p / (1-2*p)^((D+1)^2)) ≤ 0.25 := by
    have hh := mul_le_mul_of_nonneg_left hβupper (show 0 ≤ 2.1*A by linarith)
    have hm := mul_nonneg (show 0 ≤ 4*Real.exp 1 - 10.8 by linarith) hpa
    change 4 * Real.exp 1 * p * A ≤ 1 at hcondition
    nlinarith
  exact ⟨hβnonneg, hβupper, hratio, halpha⟩
theorem condition11_box_radius (Φ : CSP) (hΦ : Φ.Condition11) :
    0 ≤ 2 * Φ.pmax ∧ 2 * Φ.pmax < 1 := by
  have hp : 0 ≤ Φ.pmax := NNReal.coe_nonneg _
  have he : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    linarith
  have hd : (0 : ℝ) ≤ Φ.Dmax := Nat.cast_nonneg _
  have hsq : 1 ≤ ((Φ.Dmax : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg (Φ.Dmax : ℝ)]
  have hmul : 2 < 4 * Real.exp 1 * ((Φ.Dmax : ℝ) + 1) ^ 2 := by
    have ht := mul_nonneg (show 0 ≤ Real.exp 1 - 2 by linarith) (show 0 ≤ ((Φ.Dmax : ℝ) + 1)^2 - 1 by linarith)
    nlinarith
  constructor
  · linarith
  · by_cases hz : Φ.pmax = 0
    · simp [hz]
    · have hp' : 0 < Φ.pmax := lt_of_le_of_ne hp (Ne.symm hz)
      have hm : 0 < Φ.pmax * (4 * Real.exp 1 * ((Φ.Dmax : ℝ) + 1)^2 - 2) := by positivity
      unfold CSP.Condition11 at hΦ
      nlinarith



private noncomputable def recursive_vector (Φ : CSP) (en : Φ.EnumChoice)
    (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (L : ℕ)
    (T : Finset (Fin Φ.m)) (i : ℕ) : ℝ :=
  if T.card ≤ L then
    if hi : i < Φ.ell E r T then
      Φ.rhatWith en (L - T.card) (Φ.prefixFam (Φ.free E r T) (en E r T) ⟨i, hi⟩)
        (en E r T ⟨i, hi⟩)
    else 0
  else 0

private theorem prefix_contains_current (Φ : CSP) {n : ℕ} (E : Finset (Fin Φ.m))
    (e : Fin n → Fin Φ.m) (i : Fin n) : e i ∈ Φ.prefixFam E e i := by
  classical
  simp only [CSP.prefixFam, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inr ⟨i, le_refl _, rfl⟩

/-- If all smaller-budget estimates stay in the box, the next estimate does too.
The bound is uniform over all subfamilies and all enumeration choices. -/
theorem estimator_range_step (Φ : CSP) (hΦ : Φ.Condition11) (en : Φ.EnumChoice)
    (L : ℕ)
    (ih : ∀ k ≤ L, ∀ (E : Finset (Fin Φ.m)) (r : Fin Φ.m), r ∈ E →
      -2*Φ.pmax ≤ Φ.rhatWith en k E r ∧ Φ.rhatWith en k E r ≤ 2*Φ.pmax)
    (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (hr : r ∈ E) :
    -2*Φ.pmax ≤ Φ.rhatWith en (L+1) E r ∧ Φ.rhatWith en (L+1) E r ≤ 2*Φ.pmax := by
  classical
  let β : ℝ := Φ.pmax / (1-2*Φ.pmax)^((Φ.Dmax+1)^2)
  let A : ℝ := Real.exp 1 * (Φ.Dmax : ℝ)^2
  let v := recursive_vector Φ en E r (L+1)
  have hp : 0 ≤ Φ.pmax := NNReal.coe_nonneg _
  have hc := estimator_constants Φ.pmax Φ.Dmax hp hΦ
  have hsmall := condition11_box_radius Φ hΦ
  have hv : ∀ T ∈ Φ.twoTrees E r, ∀ i < Φ.ell E r T,
      -2*Φ.pmax ≤ v T i ∧ v T i ≤ 2*Φ.pmax := by
    intro T hT i hi
    have hrT : r ∈ T := (Finset.mem_filter.mp hT).2.1
    have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨r, hrT⟩
    by_cases ht : T.card ≤ L+1
    · have hbudget : L+1-T.card ≤ L := by omega
      have hprefix := prefix_contains_current Φ (Φ.free E r T) (en E r T) ⟨i, hi⟩
      have hh := ih (L+1-T.card) hbudget _ _ hprefix
      simpa [v, recursive_vector, ht, hi] using hh
    · simp [v, recursive_vector, ht, hp]
  have hrewrite : Φ.rhatWith en (L+1) E r =
      ∑ T ∈ (Φ.twoTrees E r).filter (fun T => T.card ≤ L+1),
        (-1 : ℝ)^(T.card-1) * Φ.treeCoeff E r T *
          ∏ i ∈ Finset.range (Φ.ell E r T), 1/(1-v T i) := by
    rw [CSP.rhatWith]
    apply Finset.sum_congr rfl
    intro T hTf
    have hh := Finset.mem_filter.mp hTf
    have hrT : r ∈ T := (Finset.mem_filter.mp hh.1).2.1
    have ht : 0 < T.card := Finset.card_pos.mpr ⟨r, hrT⟩
    congr 1
    calc
      _ = ∏ j : Fin (Φ.ell E r T), 1/(1-v T j.val) := by
        apply Finset.prod_congr rfl
        intro j hj
        simp [v, recursive_vector, hh.2, j.isLt, ht]
      _ = _ := Fin.prod_univ_eq_prod_range (fun i => 1/(1-v T i)) _
  have hsum : |Φ.rhatWith en (L+1) E r| ≤
      ∑ T ∈ Φ.twoTrees E r, β^T.card := by
    rw [hrewrite]
    calc
      _ ≤ ∑ T ∈ (Φ.twoTrees E r).filter (fun T => T.card ≤ L+1),
          |(-1 : ℝ)^(T.card-1) * Φ.treeCoeff E r T *
            ∏ i ∈ Finset.range (Φ.ell E r T), 1/(1-v T i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ T ∈ (Φ.twoTrees E r).filter (fun T => T.card ≤ L+1), β^T.card := by
        apply Finset.sum_le_sum
        intro T hTf
        have hT := (Finset.mem_filter.mp hTf).1
        have hterm := (lemma_3_6 Φ hΦ E r hr).1 T hT v hv
        have hnonneg : 0 ≤ Φ.treeCoeff E r T *
            ∏ i ∈ Finset.range (Φ.ell E r T), 1/(1-v T i) := by
          have hcoeff : 0 ≤ Φ.treeCoeff E r T := by
            unfold CSP.treeCoeff CSP.condProb CSP.prob
            positivity
          apply mul_nonneg hcoeff
          apply Finset.prod_nonneg
          intro i hi
          have hvi := hv T hT i (Finset.mem_range.mp hi)
          have : 0 < 1-v T i := by linarith [hsmall.2]
          positivity
        calc
          _ = Φ.treeCoeff E r T * ∏ i ∈ Finset.range (Φ.ell E r T), 1/(1-v T i) := by
            rw [mul_assoc, abs_mul, abs_pow, abs_of_nonneg hnonneg]
            norm_num
          _ ≤ _ := hterm
      _ ≤ ∑ T ∈ Φ.twoTrees E r, β^T.card := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro T hT hnot
        exact pow_nonneg hc.1 _
  have hq : A*β < 1 := by dsimp [A, β] at *; linarith [hc.2.2.1]
  have hgeom := tree_power_sum Φ E r β hc.1 hq
  have hfinal : β / (1-A*β) ≤ 2*Φ.pmax := by
    apply (div_le_iff₀ (by linarith : 0 < 1-A*β)).2
    have hqle : A*β ≤ 0.32 := hc.2.2.1
    have hβle : β ≤ 1.25*Φ.pmax := hc.2.1
    nlinarith [mul_nonneg hp (show 0 ≤ 0.32-A*β by linarith)]
  have habs := hsum.trans (hgeom.trans hfinal)
  constructor <;> nlinarith [(abs_le.mp habs).1, (abs_le.mp habs).2]

/-- Every truncated estimate lies in the stability box. -/
theorem estimator_range_all (Φ : CSP) (hΦ : Φ.Condition11) (en : Φ.EnumChoice)
    (L : ℕ) (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (hr : r ∈ E) :
    -2*Φ.pmax ≤ Φ.rhatWith en L E r ∧ Φ.rhatWith en L E r ≤ 2*Φ.pmax := by
  have hp : 0 ≤ Φ.pmax := NNReal.coe_nonneg _
  suffices h : ∀ n, ∀ E : Finset (Fin Φ.m), ∀ r, r ∈ E →
      -2*Φ.pmax ≤ Φ.rhatWith en n E r ∧ Φ.rhatWith en n E r ≤ 2*Φ.pmax from h L E r hr
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E r hr
    cases n with
    | zero => simpa [CSP.rhatWith] using hp
    | succ n =>
      apply estimator_range_step Φ hΦ en n
      · intro k hk E' r' hr'
        exact ih k (by omega) E' r' hr'
      · exact hr

/-- The omitted tree terms after truncating at L have a geometric tail. -/
theorem tree_power_tail (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (b : ℝ) (L : ℕ)
    (hb : 0 ≤ b) (hq : Real.exp 1 * (Φ.Dmax : ℝ)^2 * b < 1) :
    (∑ T ∈ (Φ.twoTrees E r).filter (fun T => L < T.card), b^T.card) ≤
      b * (Real.exp 1 * (Φ.Dmax : ℝ)^2 * b)^L /
        (1 - Real.exp 1 * (Φ.Dmax : ℝ)^2 * b) := by
  classical
  let A : ℝ := Real.exp 1 * (Φ.Dmax : ℝ)^2
  let F := (Φ.twoTrees E r).filter (fun T => L < T.card)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hq0 : 0 ≤ A*b := mul_nonneg hA hb
  have hq1 : A*b < 1 := hq
  have hm : ∀ T ∈ F, T.card < E.card + 1 := by
    intro T hT
    have hTT := (Finset.mem_filter.mp hT).1
    have hTE : T ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hTT).1
    have hh := Finset.card_le_card hTE
    omega
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (s := F) (t := Finset.range (E.card+1)) (g := Finset.card)
    (fun T hT => Finset.mem_range.mpr (hm T hT)) (fun T => b^T.card)
  have hcount0 : (F.filter (fun T => T.card = 0)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro T hT
    have hh := Finset.mem_filter.mp hT
    have hp := (Finset.mem_filter.mp hh.1).2
    omega
  have hgroup' : (∑ T ∈ F, b^T.card) =
      ∑ k ∈ Finset.range (E.card+1), ((F.filter (fun T => T.card = k)).card : ℝ) * b^k := by
    rw [← hgroup]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      _ = ∑ _T ∈ F.filter (fun T => T.card = k), b^k := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [(Finset.mem_filter.mp hT).2]
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  change (∑ T ∈ F, b^T.card) ≤ _
  rw [hgroup', Finset.sum_range_succ']
  simp only [hcount0, Nat.cast_zero, zero_mul, add_zero]
  have hcompare : (∑ k ∈ Finset.range E.card,
      ((F.filter (fun T => T.card = k+1)).card : ℝ) * b^(k+1)) ≤
      ∑ k ∈ (Finset.range E.card).filter (fun k => L ≤ k), b*(A*b)^k := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro k hk
    by_cases hkL : L ≤ k
    · rw [if_pos hkL]
      have hsub : F.filter (fun T => T.card = k+1) ⊆
          (Φ.twoTrees E r).filter (fun T => T.card = k+1) := by
        intro T hT
        have hh := Finset.mem_filter.mp hT
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hh.1).1, hh.2⟩
      have hcount : ((F.filter (fun T => T.card = k+1)).card : ℝ) ≤ A^k := by
        have hc : ((F.filter (fun T => T.card = k+1)).card : ℝ) ≤
            (((Φ.twoTrees E r).filter (fun T => T.card = k+1)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
        exact hc.trans (by simpa [A] using num_trees_of_size Φ E r (k+1))
      have hh := mul_le_mul_of_nonneg_right hcount (pow_nonneg hb (k+1))
      calc
        _ ≤ A^k * b^(k+1) := hh
        _ = b*(A*b)^k := by rw [pow_succ, mul_pow]; ring
    · rw [if_neg hkL]
      have hz : F.filter (fun T => T.card = k+1) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro T hT
        have hh := Finset.mem_filter.mp hT
        have ht := (Finset.mem_filter.mp hh.1).2
        omega
      simp [hz]
  apply hcompare.trans
  have heq : (Finset.range E.card).filter (fun k => L ≤ k) = Finset.Ico L E.card := by
    ext k
    simp [Finset.mem_Ico, and_comm]
  rw [heq, ← Finset.mul_sum]
  have hgeom := geom_sum_Ico_le_of_lt_one (m := L) (n := E.card) hq0 hq1
  have hh := mul_le_mul_of_nonneg_left hgeom hb
  convert hh using 1 <;> dsimp [A] <;> ring

/-- Size grouping for the retained error terms in Lemma 4.3. -/
theorem tree_weighted_error_sum (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (b : ℝ) (N : ℕ) (hb : 0 ≤ b) :
    (∑ T ∈ (Φ.twoTrees E r).filter (fun T => T.card ≤ N),
      b^T.card * (4*(0.9 : ℝ)^(N-T.card))) ≤
      4*b * ∑ k ∈ Finset.range N,
        (Real.exp 1 * (Φ.Dmax : ℝ)^2 * b)^k * (0.9 : ℝ)^(N-1-k) := by
  classical
  let A : ℝ := Real.exp 1 * (Φ.Dmax : ℝ)^2
  let F := (Φ.twoTrees E r).filter (fun T => T.card ≤ N)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hm : ∀ T ∈ F, T.card < N + 1 := by
    intro T hT
    have hh := (Finset.mem_filter.mp hT).2
    omega
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (s := F) (t := Finset.range (N+1)) (g := Finset.card)
    (fun T hT => Finset.mem_range.mpr (hm T hT))
    (fun T => b^T.card * (4*(0.9 : ℝ)^(N-T.card)))
  have hcount0 : (F.filter (fun T => T.card = 0)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro T hT
    have hh := Finset.mem_filter.mp hT
    have hrT := (Finset.mem_filter.mp (Finset.mem_filter.mp hh.1).1).2.1
    have hp : 0 < T.card := Finset.card_pos.mpr ⟨r, hrT⟩
    omega
  have hgroup' : (∑ T ∈ F, b^T.card * (4*(0.9 : ℝ)^(N-T.card))) =
      ∑ k ∈ Finset.range (N+1), ((F.filter (fun T => T.card = k)).card : ℝ) *
        (b^k * (4*(0.9 : ℝ)^(N-k))) := by
    rw [← hgroup]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      _ = ∑ _T ∈ F.filter (fun T => T.card = k), b^k * (4*(0.9 : ℝ)^(N-k)) := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [(Finset.mem_filter.mp hT).2]
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  change (∑ T ∈ F, _) ≤ _
  rw [hgroup', Finset.sum_range_succ']
  simp only [hcount0, Nat.cast_zero, zero_mul, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hsub : F.filter (fun T => T.card = k+1) ⊆
      (Φ.twoTrees E r).filter (fun T => T.card = k+1) := by
    intro T hT
    have hh := Finset.mem_filter.mp hT
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hh.1).1, hh.2⟩
  have hcount : ((F.filter (fun T => T.card = k+1)).card : ℝ) ≤ A^k := by
    have hc : ((F.filter (fun T => T.card = k+1)).card : ℝ) ≤
        (((Φ.twoTrees E r).filter (fun T => T.card = k+1)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    exact hc.trans (by simpa [A] using num_trees_of_size Φ E r (k+1))
  have hpos : 0 ≤ b^(k+1) * (4*(0.9 : ℝ)^(N-(k+1))) := by positivity
  have hh := mul_le_mul_of_nonneg_right hcount hpos
  calc
    _ ≤ A^k * (b^(k+1) * (4*(0.9 : ℝ)^(N-(k+1)))) := hh
    _ = _ := by
      have hindex : N-(k+1) = N-1-k := by omega
      rw [hindex, pow_succ, mul_pow]
      ring

/-- A finite weighted convolution used in the strong-induction error estimate. -/
theorem error_convolution_bound (L : ℕ) (hL : 1 ≤ L) :
    (∑ k ∈ Finset.range L, (0.4 : ℝ)^k * (0.9 : ℝ)^(L-1-k)) ≤
      1.8 * (0.9 : ℝ)^(L-1) := by
  have hfactor : ∀ k ∈ Finset.range L,
      (0.4 : ℝ)^k * (0.9 : ℝ)^(L-1-k) =
      (0.9 : ℝ)^(L-1) * ((0.4 : ℝ)/0.9)^k := by
    intro k hk
    have hkn : k ≤ L-1 := by have := Finset.mem_range.mp hk; omega
    rw [div_pow]
    have hpow : (0.9 : ℝ)^(L-1) = 0.9^k * 0.9^(L-1-k) := by
      rw [← pow_add, Nat.add_sub_of_le hkn]
    rw [hpow]
    have hn : (0.9 : ℝ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  have hsum : (∑ k ∈ Finset.range L, (0.4 : ℝ)^k * (0.9 : ℝ)^(L-1-k)) =
      (0.9 : ℝ)^(L-1) * ∑ k ∈ Finset.range L, ((0.4 : ℝ)/0.9)^k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hfactor
  rw [hsum]
  have hg := geom_sum_Ico_le_of_lt_one (m := 0) (n := L)
    (show (0 : ℝ) ≤ 0.4/0.9 by norm_num) (show (0.4 : ℝ)/0.9 < 1 by norm_num)
  have hg' : (∑ k ∈ Finset.range L, ((0.4 : ℝ)/0.9)^k) ≤ 1.8 := by
    have hg'' : (∑ k ∈ Finset.range L, ((0.4 : ℝ)/0.9)^k) ≤
        (1 : ℝ) / (1 - (0.4 : ℝ)/0.9) := by simpa [Nat.Ico_zero_eq_range] using hg
    norm_num at hg'' ⊢
    exact hg''
  have := mul_le_mul_of_nonneg_left hg' (pow_nonneg (by norm_num : (0 : ℝ) ≤ 0.9) (L-1))
  nlinarith

/-- The geometric-tail plus contraction recurrence closes with the target rate. -/
theorem estimator_error_recurrence_numeric (β q a : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (hβ : 0 ≤ β ∧ β ≤ 0.125) (hq : 0 ≤ q ∧ q ≤ 0.32)
    (ha : 0 ≤ a ∧ a ≤ 0.25) :
    β*q^L/(1-q) + (1.2*a*4) *
      (∑ k ∈ Finset.range L, (1.2*q)^k * (0.9 : ℝ)^(L-1-k)) ≤
        4*(0.9 : ℝ)^L := by
  have hqpos : 0 < 1-q := by linarith
  have hqpow : q^L ≤ (0.9 : ℝ)^L := pow_le_pow_left₀ hq.1 (by linarith) _
  have hA : 0 ≤ (0.9 : ℝ)^L := by positivity
  have htail : β*q^L/(1-q) ≤ 0.2*(0.9 : ℝ)^L := by
    apply (div_le_iff₀ hqpos).2
    have hp1 : 0 ≤ β * ((0.9 : ℝ)^L - q^L) := mul_nonneg hβ.1 (by linarith)
    have hp2 : 0 ≤ (0.2*(1-q)-0.125) * (0.9 : ℝ)^L := mul_nonneg (by linarith) hA
    have hp3 : 0 ≤ (0.125-β) * (0.9 : ℝ)^L := mul_nonneg (by linarith) hA
    nlinarith
  have hconv : (∑ k ∈ Finset.range L, (1.2*q)^k * (0.9 : ℝ)^(L-1-k)) ≤
      1.8*(0.9 : ℝ)^(L-1) := by
    apply le_trans _ (error_convolution_bound L hL)
    apply Finset.sum_le_sum
    intro k hk
    apply mul_le_mul_of_nonneg_right
    · exact pow_le_pow_left₀ (by nlinarith : 0 ≤ 1.2*q) (by nlinarith : 1.2*q ≤ 0.4) _
    · positivity
  have hcoef : 0 ≤ 1.2*a*4 := by nlinarith [ha.1]
  have hconv' := mul_le_mul_of_nonneg_left hconv hcoef
  have ha1 : 0 ≤ (0.9 : ℝ)^(L-1) := by positivity
  have hdec : (0.9 : ℝ)^L = 0.9 * 0.9^(L-1) := by
    have h : L = (L-1)+1 := by omega
    conv_lhs => rw [h, pow_succ]
    ring
  have hgap : 0 ≤ (1.2 - 1.2*a*4) * (1.8*(0.9 : ℝ)^(L-1)) := by
    apply mul_nonneg <;> nlinarith
  nlinarith [hconv', htail, hgap]

private noncomputable def mask
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → ℕ → ℝ) (T : ι) (i : ℕ) : ℝ :=
  if T ∈ S then x T i else 0

/-- Lemma 3.6 applies to an arbitrary retained subfamily of trees, as used in
Lemma 4.3: mask out omitted coordinates in both vectors before applying it. -/
theorem retained_tree_contraction (Φ : CSP) (hΦ : Φ.Condition11)
    (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (hr : r ∈ E)
    (S : Finset (Finset (Fin Φ.m)))
    (x y : Finset (Fin Φ.m) → ℕ → ℝ)
    (hx : ∀ T ∈ Φ.twoTrees E r, ∀ i < Φ.ell E r T, -2*Φ.pmax ≤ x T i ∧ x T i ≤ 2*Φ.pmax)
    (hy : ∀ T ∈ Φ.twoTrees E r, ∀ i < Φ.ell E r T, -2*Φ.pmax ≤ y T i ∧ y T i ≤ 2*Φ.pmax) :
    let α : ℝ := 2.1*((Φ.Dmax : ℝ)+1)^2
    let β : ℝ := Φ.pmax / (1-2*Φ.pmax)^((Φ.Dmax+1)^2)
    |(∑ T ∈ (Φ.twoTrees E r).filter (· ∈ S),
      (-1 : ℝ)^(T.card-1) * Φ.treeCoeff E r T *
        ∏ i ∈ Finset.range (Φ.ell E r T), 1/(1-x T i)) -
     (∑ T ∈ (Φ.twoTrees E r).filter (· ∈ S),
      (-1 : ℝ)^(T.card-1) * Φ.treeCoeff E r T *
        ∏ i ∈ Finset.range (Φ.ell E r T), 1/(1-y T i))| ≤
      α * ∑ T ∈ (Φ.twoTrees E r).filter (· ∈ S), (1.2*β)^T.card *
        (((Finset.range (Φ.ell E r T)).sup (fun i => ‖x T i-y T i‖₊) : NNReal) : ℝ) := by
  classical
  dsimp only
  have hp : 0 ≤ Φ.pmax := NNReal.coe_nonneg _
  have hm : ∀ (z : Finset (Fin Φ.m) → ℕ → ℝ),
      (∀ T ∈ Φ.twoTrees E r, ∀ i < Φ.ell E r T, -2*Φ.pmax ≤ z T i ∧ z T i ≤ 2*Φ.pmax) →
      ∀ T ∈ Φ.twoTrees E r, ∀ i < Φ.ell E r T,
        -2*Φ.pmax ≤ mask S z T i ∧ mask S z T i ≤ 2*Φ.pmax := by
    intro z hz T hT i hi
    by_cases hS : T ∈ S
    · simpa [mask, hS] using hz T hT i hi
    · simp [mask, hS, hp]
  have hfull := (lemma_3_6 Φ hΦ E r hr).2 (mask S x) (mask S y) (hm x hx) (hm y hy)
  have hleft : Φ.fvec E r (mask S x) - Φ.fvec E r (mask S y) =
      (∑ T ∈ (Φ.twoTrees E r).filter (· ∈ S),
        (-1 : ℝ)^(T.card-1) * Φ.treeCoeff E r T *
          ∏ i ∈ Finset.range (Φ.ell E r T), 1/(1-x T i)) -
      (∑ T ∈ (Φ.twoTrees E r).filter (· ∈ S),
        (-1 : ℝ)^(T.card-1) * Φ.treeCoeff E r T *
          ∏ i ∈ Finset.range (Φ.ell E r T), 1/(1-y T i)) := by
    unfold CSP.fvec
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro T hT
    by_cases hS : T ∈ S <;> simp [mask, hS]
  have hright : (∑ T ∈ Φ.twoTrees E r,
      (1.2*(Φ.pmax/(1-2*Φ.pmax)^((Φ.Dmax+1)^2)))^T.card *
      (((Finset.range (Φ.ell E r T)).sup (fun i => ‖mask S x T i-mask S y T i‖₊) : NNReal) : ℝ)) =
      ∑ T ∈ (Φ.twoTrees E r).filter (· ∈ S),
      (1.2*(Φ.pmax/(1-2*Φ.pmax)^((Φ.Dmax+1)^2)))^T.card *
      (((Finset.range (Φ.ell E r T)).sup (fun i => ‖x T i-y T i‖₊) : NNReal) : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro T hT
    by_cases hS : T ∈ S <;> simp [mask, hS]
  rw [hleft, hright] at hfull
  exact hfull

private noncomputable def actual_vector (Φ : CSP) (en : Φ.EnumChoice)
    (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (T : Finset (Fin Φ.m)) (i : ℕ) : ℝ :=
  if hi : i < Φ.ell E r T then
    Φ.r (Φ.prefixFam (Φ.free E r T) (en E r T) ⟨i, hi⟩) (en E r T ⟨i, hi⟩)
  else 0

private theorem pmax_small (Φ : CSP) (hΦ : Φ.Condition11) : Φ.pmax ≤ 0.1 := by
  have hp : 0 ≤ Φ.pmax := NNReal.coe_nonneg _
  have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hd : (0 : ℝ) ≤ Φ.Dmax := Nat.cast_nonneg _
  have hA : 1 ≤ ((Φ.Dmax : ℝ)+1)^2 := by nlinarith [sq_nonneg (Φ.Dmax : ℝ)]
  have hpA : Φ.pmax ≤ Φ.pmax * ((Φ.Dmax : ℝ)+1)^2 := by
    nlinarith [mul_nonneg hp (show 0 ≤ ((Φ.Dmax : ℝ)+1)^2 - 1 by linarith)]
  unfold CSP.Condition11 at hΦ
  nlinarith [mul_nonneg (show 0 ≤ 4*Real.exp 1 - 10 by linarith) hp]

private theorem actual_box (Φ : CSP) (hΦ : Φ.Condition11) (en : Φ.EnumChoice)
    (E : Finset (Fin Φ.m)) (r : Fin Φ.m) :
    ∀ T ∈ Φ.twoTrees E r, ∀ i < Φ.ell E r T,
      -2*Φ.pmax ≤ actual_vector Φ en E r T i ∧ actual_vector Φ en E r T i ≤ 2*Φ.pmax := by
  classical
  have hp : 0 ≤ Φ.pmax := NNReal.coe_nonneg _
  intro T hT i hi
  have he := prefix_contains_current Φ (Φ.free E r T) (en E r T) ⟨i, hi⟩
  have h := lemma_3_1 Φ hΦ _ _ he
  simp only [actual_vector, dif_pos hi]
  constructor <;> nlinarith [h.1, h.2]

private theorem recursive_box (Φ : CSP) (hΦ : Φ.Condition11) (en : Φ.EnumChoice)
    (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (N : ℕ) :
    ∀ T ∈ Φ.twoTrees E r, ∀ i < Φ.ell E r T,
      -2*Φ.pmax ≤ recursive_vector Φ en E r N T i ∧ recursive_vector Φ en E r N T i ≤ 2*Φ.pmax := by
  classical
  have hp : 0 ≤ Φ.pmax := NNReal.coe_nonneg _
  intro T hT i hi
  by_cases ht : T.card ≤ N
  · have hprefix := prefix_contains_current Φ (Φ.free E r T) (en E r T) ⟨i, hi⟩
    have hh := estimator_range_all Φ hΦ en (N-T.card) _ _ hprefix
    simpa [recursive_vector, ht, hi] using hh
  · simp [recursive_vector, ht, hp]

private noncomputable def tree_term (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (x : Finset (Fin Φ.m) → ℕ → ℝ) (T : Finset (Fin Φ.m)) : ℝ :=
    (-1 : ℝ)^(T.card-1) * Φ.treeCoeff E r T *
      ∏ i ∈ Finset.range (Φ.ell E r T), 1/(1-x T i)

private theorem exact_expansion (Φ : CSP) (hΦ : Φ.Condition11) (en : Φ.EnumChoice)
    (hen : Φ.ValidEnum en) (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (hr : r ∈ E) :
    Φ.r E r = ∑ T ∈ Φ.twoTrees E r, tree_term Φ E r (actual_vector Φ en E r) T := by
  classical
  rw [lemma_3_5 Φ hΦ E r hr (en E r) (hen E r)]
  apply Finset.sum_congr rfl
  intro T hT
  unfold tree_term
  congr 1
  calc
    _ = ∏ j : Fin (Φ.ell E r T), 1/(1-actual_vector Φ en E r T j.val) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [actual_vector, j.isLt]
    _ = _ := Fin.prod_univ_eq_prod_range (fun i => 1/(1-actual_vector Φ en E r T i)) _

private theorem truncated_expansion (Φ : CSP) (en : Φ.EnumChoice)
    (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (L : ℕ) :
    Φ.rhatWith en (L+1) E r = ∑ T ∈ (Φ.twoTrees E r).filter (fun T => T.card ≤ L+1),
      tree_term Φ E r (recursive_vector Φ en E r (L+1)) T := by
  classical
  rw [CSP.rhatWith]
  apply Finset.sum_congr rfl
  intro T hTf
  have hh := Finset.mem_filter.mp hTf
  have hrT : r ∈ T := (Finset.mem_filter.mp hh.1).2.1
  have ht : 0 < T.card := Finset.card_pos.mpr ⟨r, hrT⟩
  unfold tree_term
  congr 1
  calc
    _ = ∏ j : Fin (Φ.ell E r T), 1/(1-recursive_vector Φ en E r (L+1) T j.val) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [recursive_vector, hh.2, j.isLt, ht]
    _ = _ := Fin.prod_univ_eq_prod_range (fun i => 1/(1-recursive_vector Φ en E r (L+1) T i)) _

private theorem recursive_error_sup (Φ : CSP) (en : Φ.EnumChoice) (E : Finset (Fin Φ.m))
    (r : Fin Φ.m) (L : ℕ)
    (ih : ∀ k ≤ L, ∀ (E : Finset (Fin Φ.m)) (r : Fin Φ.m), r ∈ E →
      |Φ.rhatWith en k E r - Φ.r E r| ≤ 4*(0.9 : ℝ)^k)
    (T : Finset (Fin Φ.m)) (hT : T ∈ (Φ.twoTrees E r).filter (fun T => T.card ≤ L+1)) :
    (((Finset.range (Φ.ell E r T)).sup
      (fun i => ‖recursive_vector Φ en E r (L+1) T i - actual_vector Φ en E r T i‖₊) : NNReal) : ℝ) ≤
      4*(0.9 : ℝ)^(L+1-T.card) := by
  classical
  have hh := Finset.mem_filter.mp hT
  have hrT : r ∈ T := (Finset.mem_filter.mp hh.1).2.1
  have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨r, hrT⟩
  have hbudget : L+1-T.card ≤ L := by omega
  let B : NNReal := ⟨4*(0.9 : ℝ)^(L+1-T.card), by positivity⟩
  change (((Finset.range (Φ.ell E r T)).sup
      (fun i => ‖recursive_vector Φ en E r (L+1) T i - actual_vector Φ en E r T i‖₊) : NNReal) : ℝ) ≤ B
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hprefix := prefix_contains_current Φ (Φ.free E r T) (en E r T) ⟨i, hi'⟩
  have he := ih (L+1-T.card) hbudget _ _ hprefix
  apply NNReal.coe_le_coe.mp
  change |recursive_vector Φ en E r (L+1) T i - actual_vector Φ en E r T i| ≤ 4*(0.9 : ℝ)^(L+1-T.card)
  simpa only [recursive_vector, actual_vector, if_pos hh.2, dif_pos hi', B, NNReal.coe_mk] using he

private theorem retained_error_bound (Φ : CSP) (hΦ : Φ.Condition11) (en : Φ.EnumChoice)
    (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (hr : r ∈ E) (L : ℕ)
    (ih : ∀ k ≤ L, ∀ (E : Finset (Fin Φ.m)) (r : Fin Φ.m), r ∈ E →
      |Φ.rhatWith en k E r - Φ.r E r| ≤ 4*(0.9 : ℝ)^k) :
    let α : ℝ := 2.1*((Φ.Dmax : ℝ)+1)^2
    let β : ℝ := Φ.pmax / (1-2*Φ.pmax)^((Φ.Dmax+1)^2)
    |(∑ T ∈ (Φ.twoTrees E r).filter (fun T => T.card ≤ L+1),
      tree_term Φ E r (recursive_vector Φ en E r (L+1)) T) -
     (∑ T ∈ (Φ.twoTrees E r).filter (fun T => T.card ≤ L+1),
      tree_term Φ E r (actual_vector Φ en E r) T)| ≤
      α * (4*(1.2*β) * ∑ k ∈ Finset.range (L+1),
        (Real.exp 1 * (Φ.Dmax : ℝ)^2 * (1.2*β))^k * (0.9 : ℝ)^(L-k)) := by
  classical
  dsimp only
  let S : Finset (Finset (Fin Φ.m)) := Finset.univ.filter (fun T => T.card ≤ L+1)
  let β : ℝ := Φ.pmax / (1-2*Φ.pmax)^((Φ.Dmax+1)^2)
  let α : ℝ := 2.1*((Φ.Dmax : ℝ)+1)^2
  have hp : 0 ≤ Φ.pmax := NNReal.coe_nonneg _
  have hc := estimator_constants Φ.pmax Φ.Dmax hp hΦ
  have hb : 0 ≤ (1.2*β) := by dsimp [β] at *; nlinarith [hc.1]
  have ha : 0 ≤ α := by dsimp [α]; positivity
  have hfilter : (Φ.twoTrees E r).filter (· ∈ S) =
      (Φ.twoTrees E r).filter (fun T => T.card ≤ L+1) := by ext T; simp [S]
  have hcon := retained_tree_contraction Φ hΦ E r hr S
    (recursive_vector Φ en E r (L+1)) (actual_vector Φ en E r)
    (recursive_box Φ hΦ en E r (L+1)) (actual_box Φ hΦ en E r)
  rw [hfilter] at hcon
  change |(∑ T ∈ (Φ.twoTrees E r).filter (fun T => T.card ≤ L+1),
      tree_term Φ E r (recursive_vector Φ en E r (L+1)) T) -
     (∑ T ∈ (Φ.twoTrees E r).filter (fun T => T.card ≤ L+1),
      tree_term Φ E r (actual_vector Φ en E r) T)| ≤
      α * ∑ T ∈ (Φ.twoTrees E r).filter (fun T => T.card ≤ L+1), (1.2*β)^T.card *
        (((Finset.range (Φ.ell E r T)).sup (fun i =>
          ‖recursive_vector Φ en E r (L+1) T i-actual_vector Φ en E r T i‖₊) : NNReal) : ℝ) at hcon
  apply hcon.trans
  apply mul_le_mul_of_nonneg_left _ ha
  calc
    _ ≤ ∑ T ∈ (Φ.twoTrees E r).filter (fun T => T.card ≤ L+1),
        (1.2*β)^T.card * (4*(0.9 : ℝ)^(L+1-T.card)) := by
          apply Finset.sum_le_sum
          intro T hT
          exact mul_le_mul_of_nonneg_left (recursive_error_sup Φ en E r L ih T hT) (pow_nonneg hb _)
    _ ≤ 4*(1.2*β) * ∑ k ∈ Finset.range (L+1),
        (Real.exp 1 * (Φ.Dmax : ℝ)^2 * (1.2*β))^k * (0.9 : ℝ)^((L+1)-1-k) :=
          tree_weighted_error_sum Φ E r (1.2*β) (L+1) hb
    _ = _ := by simp [β]

private theorem omitted_error_bound (Φ : CSP) (hΦ : Φ.Condition11) (en : Φ.EnumChoice)
    (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (hr : r ∈ E) (N : ℕ) :
    let β : ℝ := Φ.pmax / (1-2*Φ.pmax)^((Φ.Dmax+1)^2)
    |∑ T ∈ (Φ.twoTrees E r).filter (fun T => N < T.card),
      tree_term Φ E r (actual_vector Φ en E r) T| ≤
      β * (Real.exp 1 * (Φ.Dmax : ℝ)^2 * β)^N /
        (1-Real.exp 1 * (Φ.Dmax : ℝ)^2 * β) := by
  classical
  dsimp only
  let β : ℝ := Φ.pmax / (1-2*Φ.pmax)^((Φ.Dmax+1)^2)
  let A : ℝ := Real.exp 1 * (Φ.Dmax : ℝ)^2
  have hp : 0 ≤ Φ.pmax := NNReal.coe_nonneg _
  have hc := estimator_constants Φ.pmax Φ.Dmax hp hΦ
  have hq : A*β < 1 := by dsimp [A, β] at *; linarith [hc.2.2.1]
  have hsmall := condition11_box_radius Φ hΦ
  have hv := actual_box Φ hΦ en E r
  calc
    _ ≤ ∑ T ∈ (Φ.twoTrees E r).filter (fun T => N < T.card),
        |tree_term Φ E r (actual_vector Φ en E r) T| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ (Φ.twoTrees E r).filter (fun T => N < T.card), β^T.card := by
      apply Finset.sum_le_sum
      intro T hTf
      have hT := (Finset.mem_filter.mp hTf).1
      have hterm := (lemma_3_6 Φ hΦ E r hr).1 T hT (actual_vector Φ en E r) hv
      have hnonneg : 0 ≤ Φ.treeCoeff E r T *
          ∏ i ∈ Finset.range (Φ.ell E r T), 1/(1-actual_vector Φ en E r T i) := by
        have hcoeff : 0 ≤ Φ.treeCoeff E r T := by
          unfold CSP.treeCoeff CSP.condProb CSP.prob
          positivity
        apply mul_nonneg hcoeff
        apply Finset.prod_nonneg
        intro i hi
        have hvi := hv T hT i (Finset.mem_range.mp hi)
        have : 0 < 1-actual_vector Φ en E r T i := by linarith [hsmall.2]
        positivity
      unfold tree_term
      calc
        _ = Φ.treeCoeff E r T * ∏ i ∈ Finset.range (Φ.ell E r T),
            1/(1-actual_vector Φ en E r T i) := by
          rw [mul_assoc, abs_mul, abs_pow, abs_of_nonneg hnonneg]
          norm_num
        _ ≤ _ := hterm
    _ ≤ β * (A*β)^N / (1-A*β) := tree_power_tail Φ E r β N hc.1 hq
    _ = _ := by rfl

private theorem estimator_error_step (Φ : CSP) (hΦ : Φ.Condition11) (en : Φ.EnumChoice)
    (hen : Φ.ValidEnum en) (L : ℕ)
    (ih : ∀ k ≤ L, ∀ (E : Finset (Fin Φ.m)) (r : Fin Φ.m), r ∈ E →
      |Φ.rhatWith en k E r - Φ.r E r| ≤ 4*(0.9 : ℝ)^k)
    (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (hr : r ∈ E) :
    |Φ.rhatWith en (L+1) E r - Φ.r E r| ≤ 4*(0.9 : ℝ)^(L+1) := by
  classical
  let β : ℝ := Φ.pmax / (1-2*Φ.pmax)^((Φ.Dmax+1)^2)
  let A : ℝ := Real.exp 1 * (Φ.Dmax : ℝ)^2
  let α : ℝ := 2.1*((Φ.Dmax : ℝ)+1)^2
  let X := recursive_vector Φ en E r (L+1)
  let Y := actual_vector Φ en E r
  let R := (Φ.twoTrees E r).filter (fun T => T.card ≤ L+1)
  let U := (Φ.twoTrees E r).filter (fun T => L+1 < T.card)
  have hp : 0 ≤ Φ.pmax := NNReal.coe_nonneg _
  have hc := estimator_constants Φ.pmax Φ.Dmax hp hΦ
  have hp' := pmax_small Φ hΦ
  have hβ : 0 ≤ β ∧ β ≤ 0.125 := by dsimp [β] at *; constructor <;> nlinarith [hc.1, hc.2.1]
  have hq : 0 ≤ A*β ∧ A*β ≤ 0.32 := by
    constructor
    · exact mul_nonneg (by dsimp [A]; positivity) hβ.1
    · exact hc.2.2.1
  have ha : 0 ≤ α*β ∧ α*β ≤ 0.25 := by
    constructor
    · exact mul_nonneg (by dsimp [α]; positivity) hβ.1
    · exact hc.2.2.2
  have hsplit : (∑ T ∈ R, tree_term Φ E r Y T) + (∑ T ∈ U, tree_term Φ E r Y T) =
      ∑ T ∈ Φ.twoTrees E r, tree_term Φ E r Y T := by
    simpa only [R, U, Nat.not_le] using
      (Finset.sum_filter_add_sum_filter_not (Φ.twoTrees E r) (fun T => T.card ≤ L+1) (tree_term Φ E r Y))
  have hret := retained_error_bound Φ hΦ en E r hr L ih
  have htail := omitted_error_bound Φ hΦ en E r hr (L+1)
  have hnum := estimator_error_recurrence_numeric β (A*β) (α*β) (L+1) (by omega) hβ hq ha
  have hret' : |(∑ T ∈ R, tree_term Φ E r X T) - (∑ T ∈ R, tree_term Φ E r Y T)| ≤
      (1.2*(α*β)*4) * ∑ k ∈ Finset.range (L+1), (1.2*(A*β))^k * (0.9 : ℝ)^(L-k) := by
    apply hret.trans_eq
    change α * (4*(1.2*β) * ∑ k ∈ Finset.range (L+1), (A*(1.2*β))^k * (0.9 : ℝ)^(L-k)) =
      (1.2*(α*β)*4) * ∑ k ∈ Finset.range (L+1), (1.2*(A*β))^k * (0.9 : ℝ)^(L-k)
    have heq : A*(1.2*β) = 1.2*(A*β) := by ring
    rw [heq]
    ring
  have htail' : |∑ T ∈ U, tree_term Φ E r Y T| ≤ β*(A*β)^(L+1)/(1-A*β) := htail
  rw [truncated_expansion, exact_expansion Φ hΦ en hen E r hr, ← hsplit]
  calc
    _ ≤ |(∑ T ∈ R, tree_term Φ E r X T) - (∑ T ∈ R, tree_term Φ E r Y T)| +
        |∑ T ∈ U, tree_term Φ E r Y T| := by
          have h := abs_sub_le (∑ T ∈ R, tree_term Φ E r X T)
            (∑ T ∈ R, tree_term Φ E r Y T)
            ((∑ T ∈ R, tree_term Φ E r Y T) + (∑ T ∈ U, tree_term Φ E r Y T))
          have heq : (∑ T ∈ R, tree_term Φ E r Y T) -
              ((∑ T ∈ R, tree_term Φ E r Y T) + (∑ T ∈ U, tree_term Φ E r Y T)) =
              -(∑ T ∈ U, tree_term Φ E r Y T) := by ring
          rw [heq, abs_neg] at h
          exact h
    _ ≤ (1.2*(α*β)*4) * ∑ k ∈ Finset.range (L+1), (1.2*(A*β))^k * (0.9 : ℝ)^(L-k) +
        β*(A*β)^(L+1)/(1-A*β) := add_le_add hret' htail'
    _ ≤ _ := by
      have hindex : ∀ k, (L+1)-1-k = L-k := by intro k; omega
      simp only [hindex] at hnum
      linarith

/-- Uniform quantitative accuracy of the truncated estimator. -/
theorem estimator_error_all (Φ : CSP) (hΦ : Φ.Condition11) (en : Φ.EnumChoice)
    (hen : Φ.ValidEnum en) (L : ℕ) (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (hr : r ∈ E) :
    |Φ.rhatWith en L E r - Φ.r E r| ≤ 4*(0.9 : ℝ)^L := by
  suffices h : ∀ n, ∀ E : Finset (Fin Φ.m), ∀ r, r ∈ E →
      |Φ.rhatWith en n E r - Φ.r E r| ≤ 4*(0.9 : ℝ)^n from h L E r hr
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E r hr
    cases n with
    | zero =>
      have hrange := lemma_3_1 Φ hΦ E r hr
      have hp := pmax_small Φ hΦ
      simp only [CSP.rhatWith, pow_zero, mul_one, zero_sub, abs_neg]
      rw [abs_of_nonneg hrange.1]
      nlinarith [hrange.2]
    | succ n =>
      apply estimator_error_step Φ hΦ en hen n
      · intro k hk E' r' hr'
        exact ih k (by omega) E' r' hr'
      · exact hr

/-- Lemma 4.3: all truncated estimates stay in range and converge geometrically. -/
theorem solution (Φ : CSP) (hΦ : Φ.Condition11) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (hc₀ : c₀ ∈ E) (L : ℕ) (en : Φ.EnumChoice) (hen : Φ.ValidEnum en) :
    -2 * Φ.pmax ≤ Φ.rhatWith en L E c₀ ∧ Φ.rhatWith en L E c₀ ≤ 2 * Φ.pmax ∧
      |Φ.rhatWith en L E c₀ - Φ.r E c₀| ≤ 4 * (0.9 : ℝ) ^ L := by
  exact ⟨(estimator_range_all Φ hΦ en L E c₀ hc₀).1,
    (estimator_range_all Φ hΦ en L E c₀ hc₀).2,
    estimator_error_all Φ hΦ en hen L E c₀ hc₀⟩
