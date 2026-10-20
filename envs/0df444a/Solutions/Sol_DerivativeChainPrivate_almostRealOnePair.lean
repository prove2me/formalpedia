-- Prove2me | solution 1 for DerivativeChainPrivate.almostRealOnePair
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T03:16:18.951197+00:00
-- url     : https://prove2.me/submissions/e86530d5-8dec-4937-a493-27b3fe5e8dae

import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_almost_real_row_count
import Theorems.Thm_DerivativeChainPrivate_row_natDegree
import Theorems.Thm_DerivativeChainPrivate_nonreal_roots_of_real_polynomial
import Theorems.Thm_DerivativeChainPrivate_real_root_defect_iterate
import Theorems.Thm_DerivativeChainPrivate_exists_chain_cost_le_sqrt
import Theorems.Thm_DerivativeChainPrivate_root_slot_nonreal_count



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate

theorem card_real_roots_interval_le_derivative (p : Polynomial ℝ) (A B : ℝ) :
    (p.roots.filter (fun x => A ≤ x ∧ x ≤ B)).card ≤
      (p.derivative.roots.filter (fun x => A ≤ x ∧ x ≤ B)).card + 1 := by
  classical
  rcases eq_or_ne p.derivative 0 with hd | hd
  · rw [Polynomial.eq_C_of_derivative_eq_zero hd]
    simp
  have hp : p ≠ 0 := ne_of_apply_ne Polynomial.derivative (by rwa [Polynomial.derivative_zero])
  let s := p.roots.filter (fun x => A ≤ x ∧ x ≤ B)
  let t := p.derivative.roots.filter (fun x => A ≤ x ∧ x ≤ B)
  have hs (x : ℝ) (hx : x ∈ s.toFinset) : x ∈ p.roots ∧ (A ≤ x ∧ x ≤ B) := by
    simpa only [s, Multiset.mem_toFinset, Multiset.mem_filter] using hx
  have ht (x : ℝ) (hx : x ∈ t.toFinset) : x ∈ p.derivative.roots ∧ (A ≤ x ∧ x ≤ B) := by
    simpa only [t, Multiset.mem_toFinset, Multiset.mem_filter] using hx
  have hcard : s.toFinset.card ≤ (t.toFinset \ s.toFinset).card + 1 := by
    refine Finset.card_le_sdiff_of_interleaved ?_
    intro x hx y hy hxy _
    obtain ⟨z, hz, hzero⟩ := exists_deriv_eq_zero hxy p.continuousOn
      (((Polynomial.mem_roots hp).mp (hs x hx).1).trans
        ((Polynomial.mem_roots hp).mp (hs y hy).1).symm)
    refine ⟨z, ?_, hz⟩
    rw [Multiset.mem_toFinset, Multiset.mem_filter]
    refine ⟨?_, (hs x hx).2.1.trans hz.1.le, hz.2.le.trans (hs y hy).2.2⟩
    rwa [Polynomial.mem_roots hd, Polynomial.IsRoot, ← p.deriv]
  have hscount (x : ℝ) (hx : x ∈ s.toFinset) :
      s.count x = p.rootMultiplicity x := by
    dsimp [s]
    rw [Multiset.count_filter_of_pos (p := fun y : ℝ => A ≤ y ∧ y ≤ B)
      (a := x) (hs x hx).2, Polynomial.count_roots]
  have htcount (x : ℝ) (hx : x ∈ s.toFinset) :
      t.count x = p.derivative.rootMultiplicity x := by
    dsimp [t]
    rw [Multiset.count_filter_of_pos (p := fun y : ℝ => A ≤ y ∧ y ≤ B)
      (a := x) (hs x hx).2, Polynomial.count_roots]
  change s.card ≤ t.card + 1
  calc
    s.card = ∑ x ∈ s.toFinset, s.count x := (Multiset.toFinset_sum_count_eq _).symm
    _ = ∑ x ∈ s.toFinset, (s.count x - 1 + 1) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (Nat.sub_add_cancel (Nat.succ_le_iff.mpr
        (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hx)))).symm
    _ = (∑ x ∈ s.toFinset, (p.rootMultiplicity x - 1)) + s.toFinset.card := by
      simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones]
      congr 1
      exact Finset.sum_congr rfl (fun x hx => by rw [hscount x hx])
    _ ≤ (∑ x ∈ s.toFinset, t.count x) + ((t.toFinset \ s.toFinset).card + 1) := by
      apply add_le_add _ hcard
      apply Finset.sum_le_sum
      intro x hx
      rw [htcount x hx]
      exact Polynomial.rootMultiplicity_sub_one_le_derivative_rootMultiplicity p x
    _ ≤ (∑ x ∈ s.toFinset, t.count x) +
        ((∑ x ∈ t.toFinset \ s.toFinset, t.count x) + 1) := by
      gcongr
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_le_sum
      intro x hx
      exact Nat.succ_le_iff.mpr (Multiset.count_pos.mpr
        (Multiset.mem_toFinset.mp (Finset.mem_sdiff.mp hx).1))
    _ = t.card + 1 := by
      rw [← add_assoc, ← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_self_eq_union, ← Multiset.toFinset_sum_count_eq,
        ← Finset.sum_subset Finset.subset_union_right]
      intro x _ hx
      simpa only [Multiset.mem_toFinset, Multiset.count_eq_zero] using hx

theorem real_derivative_roots_interval_of_count_eq (p : Polynomial ℝ) (A B : ℝ)
    (hparent : ∀ x ∈ p.roots, A ≤ x ∧ x ≤ B)
    (hcount : p.roots.card = p.derivative.roots.card + 1) :
    ∀ x ∈ p.derivative.roots, A ≤ x ∧ x ≤ B := by
  classical
  have h := card_real_roots_interval_le_derivative p A B
  rw [Multiset.filter_eq_self.mpr hparent, hcount] at h
  have heq : p.derivative.roots.filter (fun x => A ≤ x ∧ x ≤ B) = p.derivative.roots := by
    apply Multiset.eq_of_le_of_card_le (Multiset.filter_le _ _)
    omega
  exact Multiset.filter_eq_self.mp heq

end DerivativeChainPrivate



set_option autoImplicit false

namespace DerivativeChainPrivate

theorem real_root_defect_zero_or_two (p : Polynomial ℝ)
    (h : p.natDegree - p.roots.card ≤ 2) :
    p.natDegree - p.roots.card = 0 ∨ p.natDegree - p.roots.card = 2 := by
  obtain ⟨q, _, hdegree, hroots⟩ := p.exists_prod_multiset_X_sub_C_mul
  have hq : q.natDegree ≤ 2 := by omega
  have hnot : q.natDegree ≠ 1 := by
    intro hone
    have hcard := (Polynomial.Splits.of_natDegree_eq_one hone).natDegree_eq_card_roots
    rw [hroots] at hcard
    simp only [Multiset.card_zero] at hcard
    omega
  omega

theorem real_one_pair_factorization (p : Polynomial ℝ) (hp : p ≠ 0)
    (hc : p.natDegree - p.roots.card ≤ 2) (z : ℂ)
    (hz : (p.map Complex.ofRealHom).eval z = 0) (hzi : z.im ≠ 0) :
    ∃ q : Polynomial ℝ,
      p = (Polynomial.X ^ 2 - Polynomial.C (2 * z.re) * Polynomial.X +
        Polynomial.C (‖z‖ ^ 2)) * q ∧ q.Splits := by
  let B : Polynomial ℝ := Polynomial.X ^ 2 - Polynomial.C (2 * z.re) * Polynomial.X +
    Polynomial.C (‖z‖ ^ 2)
  have hBdegree : B.natDegree = 2 := by
    convert (Polynomial.natDegree_quadratic (a := (1 : ℝ)) (b := -(2 * z.re))
      (c := ‖z‖ ^ 2) (by norm_num)) using 1 <;> simp [B, sub_eq_add_neg]
  have hB : B ≠ 0 := by
    intro h
    simp [h] at hBdegree
  have hpositive (x : ℝ) : 0 < B.eval x := by
    have him := sq_pos_of_ne_zero hzi
    have hnorm := Complex.sq_norm_sub_sq_re z
    simp only [B, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
    nlinarith [sq_nonneg (x - z.re)]
  have hBroots : B.roots = 0 := by
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    intro x hx
    exact (ne_of_gt (hpositive x)) ((Polynomial.mem_roots hB).mp hx)
  have hdiv : B ∣ p := p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero
    (by
      have hf : (algebraMap ℝ ℂ) = Complex.ofRealHom := by ext x; rfl
      simpa only [Polynomial.eval_map, Polynomial.aeval_def, hf] using hz) hzi
  obtain ⟨q, heq⟩ := hdiv
  have hq : q ≠ 0 := by
    intro h
    apply hp
    simp [heq, h]
  have hdegree : p.natDegree = 2 + q.natDegree := by
    rw [heq, Polynomial.natDegree_mul hB hq, hBdegree]
  have hroots : p.roots = q.roots := by
    rw [heq, Polynomial.roots_mul (mul_ne_zero hB hq), hBroots, zero_add]
  have hqcard : q.roots.card = q.natDegree := by
    have hle := Polynomial.card_roots' q
    rw [hdegree, hroots] at hc
    omega
  exact ⟨q, heq, Polynomial.splits_iff_card_roots.mpr hqcard⟩

theorem real_one_pair_nonreal_realPart (p : Polynomial ℝ) (hp : p ≠ 0)
    (hc : p.natDegree - p.roots.card ≤ 2) :
    ∃ b : ℝ, ∀ z : ℂ, (p.map Complex.ofRealHom).eval z = 0 → z.im ≠ 0 → z.re = b := by
  classical
  by_cases hex : ∃ z : ℂ, (p.map Complex.ofRealHom).eval z = 0 ∧ z.im ≠ 0
  · obtain ⟨z, hz, hzi⟩ := hex
    obtain ⟨q, hq, hsplit⟩ := real_one_pair_factorization p hp hc z hz hzi
    refine ⟨z.re, ?_⟩
    intro w hw hwi
    have hfactor : (Polynomial.map Complex.ofRealHom p) =
        ((Polynomial.X - Polynomial.C (starRingEnd ℂ z)) *
          (Polynomial.X - Polynomial.C z)) * q.map Complex.ofRealHom := by
      rw [hq, Polynomial.map_mul]
      congr 1
      simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_mul, Polynomial.map_C]
      change Polynomial.X ^ 2 - Polynomial.C ((2 * z.re : ℝ) : ℂ) * Polynomial.X +
        Polynomial.C ((‖z‖ ^ 2 : ℝ) : ℂ) = _
      rw [← Complex.add_conj, map_add, Complex.ofReal_pow, ← Complex.mul_conj', map_mul]
      ring
    rw [hfactor, Polynomial.eval_mul, Polynomial.eval_mul] at hw
    rcases mul_eq_zero.mp hw with h | h
    · rcases mul_eq_zero.mp h with h | h
      · have heq : w = (starRingEnd ℂ) z := sub_eq_zero.mp (by simpa using h)
        rw [heq]
        rfl
      · have heq : w = z := sub_eq_zero.mp (by simpa using h)
        rw [heq]
    · have hqne : q ≠ 0 := by
        intro hzero
        apply hp
        simp [hq, hzero]
      have hm : w ∈ (q.map Complex.ofRealHom).roots :=
        (Polynomial.mem_roots ((Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr hqne)).mpr h
      rw [← Polynomial.roots_map_of_injective_of_card_eq_natDegree
        (f := Complex.ofRealHom) Complex.ofReal_injective hsplit.natDegree_eq_card_roots.symm] at hm
      obtain ⟨x, _, hx⟩ := Multiset.mem_map.mp hm
      exact False.elim (hwi (by rw [← hx]; simp))
  · refine ⟨0, ?_⟩
    intro z hz hzi
    exact False.elim (hex ⟨z, hz, hzi⟩)

end DerivativeChainPrivate



set_option autoImplicit false

namespace DerivativeChainPrivate

theorem derivative_root_norm_le {P : Polynomial ℂ} (hP : 0 < P.degree)
    (R : ℝ) (hR : ∀ w ∈ P.roots, ‖w‖ ≤ R) {z : ℂ}
    (hz : P.derivative.eval z = 0) : ‖z‖ ≤ R := by
  have hp : P ≠ 0 := by rintro rfl; simp at hP
  have hd : P.derivative ≠ 0 := Polynomial.derivative_eq_zero.not.mpr
    (Nat.ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mpr hP))
  have hm : z ∈ P.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
    exact ⟨hd, hz⟩
  have hs : P.rootSet ℂ ⊆ Metric.closedBall (0 : ℂ) R := by
    intro w hw
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval] at hw
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hR w ((Polynomial.mem_roots hp).mpr hw.2)
  have hmem := (convexHull_min hs (convex_closedBall (0 : ℂ) R))
    (P.rootSet_derivative_subset_convexHull_rootSet hP hm)
  simpa only [Metric.mem_closedBall, dist_zero_right] using hmem

theorem derivative_root_re_le {P : Polynomial ℂ} (hP : 0 < P.degree)
    (R : ℝ) (hR : ∀ w ∈ P.roots, w.re ≤ R) {z : ℂ}
    (hz : P.derivative.eval z = 0) : z.re ≤ R := by
  have hp : P ≠ 0 := by rintro rfl; simp at hP
  have hd : P.derivative ≠ 0 := by
    intro h
    have hzero := Polynomial.derivative_eq_zero.mp h
    have := Polynomial.natDegree_pos_iff_degree_pos.mpr hP
    omega
  have hm : z ∈ P.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
    exact ⟨hd, hz⟩
  have hs : P.rootSet ℂ ⊆ Complex.reLm ⁻¹' Set.Iic R := by
    intro w hw
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval] at hw
    exact hR w ((Polynomial.mem_roots hp).mpr hw.2)
  exact (convexHull_min hs ((convex_Iic R).linear_preimage Complex.reLm))
    (P.rootSet_derivative_subset_convexHull_rootSet hP hm)

theorem derivative_root_re_ge {P : Polynomial ℂ} (hP : 0 < P.degree)
    (L : ℝ) (hL : ∀ w ∈ P.roots, L ≤ w.re) {z : ℂ}
    (hz : P.derivative.eval z = 0) : L ≤ z.re := by
  have hp : P ≠ 0 := by rintro rfl; simp at hP
  have hd : P.derivative ≠ 0 := by
    intro h
    have hzero := Polynomial.derivative_eq_zero.mp h
    have := Polynomial.natDegree_pos_iff_degree_pos.mpr hP
    omega
  have hm : z ∈ P.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
    exact ⟨hd, hz⟩
  have hs : P.rootSet ℂ ⊆ Complex.reLm ⁻¹' Set.Ici L := by
    intro w hw
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval] at hw
    exact hL w ((Polynomial.mem_roots hp).mpr hw.2)
  exact (convexHull_min hs ((convex_Ici L).linear_preimage Complex.reLm))
    (P.rootSet_derivative_subset_convexHull_rootSet hP hm)

theorem real_one_pair_derivative_side (p : Polynomial ℝ) (hp : 0 < p.natDegree)
    (hc : p.natDegree - p.roots.card ≤ 2) (L R : ℝ) (hLR : L ≤ R)
    (hroots : ∀ x ∈ p.roots, L ≤ x ∧ x ≤ R) :
    (∀ x : ℝ, p.derivative.eval x = 0 → L ≤ x) ∨
      (∀ x : ℝ, p.derivative.eval x = 0 → x ≤ R) := by
  have hpne : p ≠ 0 := by intro h; simp [h] at hp
  obtain ⟨b, hb⟩ := real_one_pair_nonreal_realPart p hpne hc
  have hP : 0 < (p.map Complex.ofRealHom).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, Polynomial.natDegree_map]
    exact hp
  have hreal (w : ℂ) (hw : (p.map Complex.ofRealHom).eval w = 0) (hi : w.im = 0) :
      L ≤ w.re ∧ w.re ≤ R := by
    have hcast : Complex.ofRealHom w.re = w := by apply Complex.ext <;> simp [hi]
    have hroot : (p.map Complex.ofRealHom).IsRoot (Complex.ofRealHom w.re) := by
      rw [hcast]
      exact hw
    exact hroots w.re ((Polynomial.mem_roots hpne).mpr
      (hroot.of_map Complex.ofReal_injective))
  have hcritical (x : ℝ) (hx : p.derivative.eval x = 0) :
      (p.map Complex.ofRealHom).derivative.eval (Complex.ofRealHom x) = 0 := by
    rw [Polynomial.derivative_map, Polynomial.eval_map_apply, hx, map_zero]
  by_cases hRb : b ≤ R
  · right
    intro x hx
    have hbound : ∀ w ∈ (p.map Complex.ofRealHom).roots, w.re ≤ R := by
      intro w hw
      have heval := (Polynomial.mem_roots
        ((Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr hpne)).mp hw
      by_cases hi : w.im = 0
      · exact (hreal w heval hi).2
      · rw [hb w heval hi]
        exact hRb
    exact derivative_root_re_le hP R hbound (hcritical x hx)
  · left
    intro x hx
    have hbound : ∀ w ∈ (p.map Complex.ofRealHom).roots, L ≤ w.re := by
      intro w hw
      have heval := (Polynomial.mem_roots
        ((Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr hpne)).mp hw
      by_cases hi : w.im = 0
      · exact (hreal w heval hi).1
      · rw [hb w heval hi]
        linarith
    exact derivative_root_re_ge hP L hbound (hcritical x hx)

end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate

theorem one_exception_global_side (lo hi : ℕ → ℝ) (D : ℕ → ℕ) (n : ℕ)
    (hD : ∀ i ≤ n, D i = 0 ∨ D i = 2)
    (hmono : ∀ i j, i ≤ j → j ≤ n → D i ≤ D j)
    (hequal : ∀ i < n, D i = D (i + 1) → lo (i + 1) ≤ lo i ∧ hi i ≤ hi (i + 1))
    (hside : ∀ i < n, lo (i + 1) ≤ lo i ∨ hi i ≤ hi (i + 1)) :
    (∀ i < n, lo (i + 1) ≤ lo i) ∨ (∀ i < n, hi i ≤ hi (i + 1)) := by
  by_cases hleft : ∀ i < n, lo (i + 1) ≤ lo i
  · exact Or.inl hleft
  push Not at hleft
  obtain ⟨i, hin, hifail⟩ := hleft
  right
  intro j hjn
  by_contra hjfail
  have hdi : D i ≠ D (i + 1) := by
    intro heq
    exact (not_le_of_gt hifail) (hequal i hin heq).1
  have hdj : D j ≠ D (j + 1) := by
    intro heq
    exact hjfail (hequal j hjn heq).2
  have hDi := hD i (by omega)
  have hDi' := hD (i + 1) (by omega)
  have hDj := hD j (by omega)
  have hDj' := hD (j + 1) (by omega)
  have hmi := hmono i (i + 1) (by omega) (by omega)
  have hmj := hmono j (j + 1) (by omega) (by omega)
  have hij : i = j := by
    by_cases hij : i < j
    · have h := hmono (i + 1) j (by omega) (by omega)
      omega
    · by_cases hji : j < i
      · have h := hmono (j + 1) i (by omega) (by omega)
        omega
      · omega
  subst j
  exact (hside i hin).elim (not_le_of_gt hifail) hjfail

theorem chainCost_of_real_nondecreasing {n : ℕ} (x : ℕ → ℝ)
    (hmono : ∀ i < n - 1, x i ≤ x (i + 1)) :
    chainCost (fun i : Fin n => (x i.val : ℂ)) = x (n - 1) - x 0 := by
  unfold chainCost
  calc
    (∑ i : Fin (n - 1), ‖(x (i.val + 1) : ℂ) - (x i.val : ℂ)‖) =
        ∑ i : Fin (n - 1), (x (i.val + 1) - x i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (hmono i.val i.isLt))]
    _ = x (n - 1) - x 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun i => x (i + 1) - x i), Finset.sum_range_sub]

theorem chainCost_of_real_nonincreasing {n : ℕ} (x : ℕ → ℝ)
    (hmono : ∀ i < n - 1, x (i + 1) ≤ x i) :
    chainCost (fun i : Fin n => (x i.val : ℂ)) = x 0 - x (n - 1) := by
  unfold chainCost
  calc
    (∑ i : Fin (n - 1), ‖(x (i.val + 1) : ℂ) - (x i.val : ℂ)‖) =
        ∑ i : Fin (n - 1), (x i.val - x (i.val + 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr (hmono i.val i.isLt))]
      ring
    _ = x 0 - x (n - 1) := by
      rw [Fin.sum_univ_eq_sum_range (fun i => x i - x (i + 1)), Finset.sum_range_sub']

theorem chainCost_eq_sum_range {n : ℕ} (f : ℕ → ℂ) :
    chainCost (fun i : Fin n => f i.val) =
      ∑ i ∈ Finset.range (n - 1), ‖f (i + 1) - f i‖ := by
  unfold chainCost
  exact Fin.sum_univ_eq_sum_range (fun i => ‖f (i + 1) - f i‖) (n - 1)

theorem chainCost_prepend_two (n : ℕ) (hn : 3 ≤ n) (u w : ℂ) (f : ℕ → ℂ) :
    chainCost (fun i : Fin n => if i.val = 0 then u else if i.val = 1 then w else f (i.val - 2)) =
      ‖w - u‖ + ‖f 0 - w‖ + chainCost (fun i : Fin (n - 2) => f i.val) := by
  let z (i : ℕ) := if i = 0 then u else if i = 1 then w else f (i - 2)
  have hz0 : z 0 = u := by simp [z]
  have hz1 : z 1 = w := by simp [z]
  have hztail (i : ℕ) : z (i + 2) = f i := by
    simp [z, show i + 2 ≠ 0 by omega, show i + 2 ≠ 1 by omega]
  change chainCost (fun i : Fin n => z i.val) = _
  rw [chainCost_eq_sum_range, show n - 1 = 2 + (n - 3) by omega, Finset.sum_range_add]
  have hfirst : (∑ i ∈ Finset.range 2, ‖z (i + 1) - z i‖) = ‖w - u‖ + ‖f 0 - w‖ := by
    simp [Finset.sum_range_succ, hz0, hz1, hztail]
  rw [hfirst, chainCost_eq_sum_range, show n - 2 - 1 = n - 3 by omega]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show 2 + i + 1 = (i + 1) + 2 by omega, hztail,
    show 2 + i = i + 2 by omega, hztail]

theorem chainCost_translate {n : ℕ} (z : Fin n → ℂ) (u : ℂ) :
    chainCost (fun i => z i + u) = chainCost z := by
  simp only [chainCost, add_sub_add_right_eq_sub]

end DerivativeChainPrivate



set_option autoImplicit false

namespace DerivativeChainPrivate

theorem real_tower_monotone_chain {n : ℕ} (hn : 0 < n) (F : ℕ → Polynomial ℝ)
    (hdegree : ∀ i < n, (F i).natDegree = i + 1)
    (hderiv : ∀ i < n - 1, (F (i + 1)).derivative = F i)
    (hc : ∀ i < n, (F i).natDegree - (F i).roots.card ≤ 2)
    (hreal : ∀ i < n, (F i).roots ≠ 0)
    (hdisk : ∀ i < n, ∀ x ∈ (F i).roots, -1 ≤ x ∧ x ≤ 1) :
    ∃ x : ℕ → ℝ, (∀ i < n, (F i).eval (x i) = 0) ∧
      ((∀ i < n - 1, x i ≤ x (i + 1)) ∨ (∀ i < n - 1, x (i + 1) ≤ x i)) ∧
      chainCost (fun i : Fin n => (x i.val : ℂ)) ≤ 2 := by
  classical
  let lo (i : ℕ) := if h : i < n then
    (F i).roots.toFinset.min' (Multiset.toFinset_nonempty.mpr (hreal i h)) else 0
  let hi (i : ℕ) := if h : i < n then
    (F i).roots.toFinset.max' (Multiset.toFinset_nonempty.mpr (hreal i h)) else 0
  have hlomem (i : ℕ) (hin : i < n) : lo i ∈ (F i).roots := by
    simpa only [lo, dif_pos hin, Multiset.mem_toFinset] using
      Finset.min'_mem (F i).roots.toFinset (Multiset.toFinset_nonempty.mpr (hreal i hin))
  have hhimem (i : ℕ) (hin : i < n) : hi i ∈ (F i).roots := by
    simpa only [hi, dif_pos hin, Multiset.mem_toFinset] using
      Finset.max'_mem (F i).roots.toFinset (Multiset.toFinset_nonempty.mpr (hreal i hin))
  have hlole (i : ℕ) (hin : i < n) (x : ℝ) (hx : x ∈ (F i).roots) : lo i ≤ x := by
    simpa only [lo, dif_pos hin] using
      Finset.min'_le (F i).roots.toFinset x (Multiset.mem_toFinset.mpr hx)
  have hlehi (i : ℕ) (hin : i < n) (x : ℝ) (hx : x ∈ (F i).roots) : x ≤ hi i := by
    simpa only [hi, dif_pos hin] using
      Finset.le_max' (F i).roots.toFinset x (Multiset.mem_toFinset.mpr hx)
  let D (i : ℕ) := (F i).natDegree - (F i).roots.card
  have hD (i : ℕ) (hin : i ≤ n - 1) : D i = 0 ∨ D i = 2 :=
    real_root_defect_zero_or_two (F i) (hc i (by omega))
  have hDstep (i : ℕ) (hin : i < n - 1) : D i ≤ D (i + 1) := by
    have hR := (F (i + 1)).card_roots_le_derivative
    rw [hderiv i hin] at hR
    have hp := hdegree (i + 1) (by omega)
    have hq := hdegree i (by omega)
    have hRp := Polynomial.card_roots' (F (i + 1))
    have hRq := Polynomial.card_roots' (F i)
    dsimp only [D]
    omega
  have hDmono (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n - 1) : D i ≤ D j := by
    revert hjn
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hij ih =>
      intro hjn
      exact (ih (by omega)).trans (hDstep j (by omega))
  have hequal (i : ℕ) (hin : i < n - 1) (heq : D i = D (i + 1)) :
      lo (i + 1) ≤ lo i ∧ hi i ≤ hi (i + 1) := by
    have hi1 : i + 1 < n := by omega
    have hi0 : i < n := by omega
    have hp := hdegree (i + 1) hi1
    have hq := hdegree i hi0
    have hRp := Polynomial.card_roots' (F (i + 1))
    have hRq := Polynomial.card_roots' (F i)
    have hcount : (F (i + 1)).roots.card = ((F (i + 1)).derivative).roots.card + 1 := by
      rw [hderiv i hin]
      dsimp only [D] at heq
      omega
    have hinterval := real_derivative_roots_interval_of_count_eq (F (i + 1))
      (lo (i + 1)) (hi (i + 1))
      (fun x hx => ⟨hlole _ hi1 x hx, hlehi _ hi1 x hx⟩) hcount
    rw [hderiv i hin] at hinterval
    exact ⟨(hinterval (lo i) (hlomem i hi0)).1,
      (hinterval (hi i) (hhimem i hi0)).2⟩
  have hside (i : ℕ) (hin : i < n - 1) :
      lo (i + 1) ≤ lo i ∨ hi i ≤ hi (i + 1) := by
    have hi1 : i + 1 < n := by omega
    have hi0 : i < n := by omega
    have hp : 0 < (F (i + 1)).natDegree := by rw [hdegree _ hi1]; omega
    have h := real_one_pair_derivative_side (F (i + 1)) hp (hc _ hi1)
      (lo (i + 1)) (hi (i + 1)) (hlole _ hi1 _ (hhimem _ hi1))
      (fun x hx => ⟨hlole _ hi1 x hx, hlehi _ hi1 x hx⟩)
    rw [hderiv i hin] at h
    exact h.elim
      (fun h => Or.inl (h _ (Polynomial.isRoot_of_mem_roots (hlomem _ hi0))))
      (fun h => Or.inr (h _ (Polynomial.isRoot_of_mem_roots (hhimem _ hi0))))
  rcases one_exception_global_side lo hi D (n - 1) hD hDmono hequal hside with h | h
  · refine ⟨lo, (fun i hin => Polynomial.isRoot_of_mem_roots (hlomem i hin)), Or.inr h, ?_⟩
    rw [chainCost_of_real_nonincreasing lo h]
    have h0 := hdisk 0 hn _ (hlomem 0 hn)
    have hend := hdisk (n - 1) (by omega) _ (hlomem (n - 1) (by omega))
    linarith
  · refine ⟨hi, (fun i hin => Polynomial.isRoot_of_mem_roots (hhimem i hin)), Or.inl h, ?_⟩
    rw [chainCost_of_real_nondecreasing hi h]
    have h0 := hdisk 0 hn _ (hhimem 0 hn)
    have hend := hdisk (n - 1) (by omega) _ (hhimem (n - 1) (by omega))
    linarith

end DerivativeChainPrivate



set_option autoImplicit false

namespace DerivativeChainPrivate

theorem row_root_norm_le_one {n : ℕ} (a : Fin n → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1)
    (m : ℕ) (hm0 : 0 < m) (hmn : m ≤ n) (z : ℂ) (hz : (row a m).eval z = 0) :
    ‖z‖ ≤ 1 := by
  have hprod : fromRoots a ≠ 0 := (Polynomial.monic_prod_X_sub_C a Finset.univ).ne_zero
  have hroots : (fromRoots a).roots = Finset.univ.val.map a := by
    unfold fromRoots
    rw [Polynomial.roots_prod _ _ hprod]
    simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  have hiter : ∀ k : ℕ, k < n → ∀ w : ℂ,
      ((Polynomial.derivative^[k]) (fromRoots a)).eval w = 0 → ‖w‖ ≤ 1 := by
    intro k
    induction k with
    | zero =>
      intro _ w hw
      have hm := (Polynomial.mem_roots hprod).mpr hw
      rw [hroots] at hm
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hm
      exact ha i
    | succ k ih =>
      intro hk w hw
      have hk0 : k < n := by omega
      have hdegree : ((Polynomial.derivative^[k]) (fromRoots a)).natDegree = n - k := by
        have h := row_natDegree a (m := n - k) (Nat.sub_le n k)
        simpa only [row, Nat.sub_sub_self (Nat.le_of_lt hk0)] using h
      have hpos : 0 < ((Polynomial.derivative^[k]) (fromRoots a)).degree := by
        rw [← Polynomial.natDegree_pos_iff_degree_pos, hdegree]
        omega
      rw [Function.iterate_succ_apply'] at hw
      exact derivative_root_norm_le hpos 1
        (fun x hx => ih hk0 x (Polynomial.isRoot_of_mem_roots hx)) hw
  exact hiter (n - m) (by omega) z hz

theorem almostRealOnePair_of_real_quadratic {n : ℕ} (a : Fin n → ℂ)
    (hn : 2 ≤ n) (ha : ∀ i, ‖a i‖ ≤ 1)
    (hr : RealCoefficients a) (hc : nonrealCount a ≤ 2)
    (hquad : ∃ x : ℝ, (row a 2).eval (x : ℂ) = 0) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z ≤ 2 := by
  obtain ⟨p, _, hrows⟩ := almost_real_row_count a hr
  let F (i : ℕ) := (Polynomial.derivative^[n - (i + 1)]) p
  have hmap (i : ℕ) (hin : i < n) :
      (F i).map Complex.ofRealHom = row a (i + 1) := (hrows (i + 1) (by omega)).1
  have hdegree (i : ℕ) (hin : i < n) : (F i).natDegree = i + 1 :=
    (hrows (i + 1) (by omega)).2.1
  have hcount (i : ℕ) (hin : i < n) :
      i + 1 - nonrealCount a ≤ (F i).roots.card := (hrows (i + 1) (by omega)).2.2
  have hderiv (i : ℕ) (hin : i < n - 1) : (F (i + 1)).derivative = F i := by
    dsimp only [F]
    have heq : n - (i + 1) = n - (i + 1 + 1) + 1 := by omega
    rw [heq, Function.iterate_succ_apply']
  have hdefect (i : ℕ) (hin : i < n) :
      (F i).natDegree - (F i).roots.card ≤ 2 := by
    have h := hcount i hin
    rw [hdegree i hin]
    omega
  have hreal (i : ℕ) (hin : i < n) : (F i).roots ≠ 0 := by
    by_cases hi0 : i = 0
    · subst i
      have hs := Polynomial.Splits.of_natDegree_eq_one (hdegree 0 (by omega))
      have hcard := hs.natDegree_eq_card_roots
      rw [hdegree 0 (by omega)] at hcard
      intro hz
      simp [hz] at hcard
    by_cases hi1 : i = 1
    · subst i
      obtain ⟨x, hx⟩ := hquad
      rw [← hmap 1 (by omega)] at hx
      have hxroot : (F 1).IsRoot x := by
        apply Polynomial.IsRoot.of_map (f := Complex.ofRealHom) _ Complex.ofReal_injective
        exact hx
      have hm : x ∈ (F 1).roots :=
        ((Polynomial.mem_roots (by
          intro hzero
          have hd := hdegree 1 (by omega)
          simp [hzero] at hd)).mpr hxroot)
      intro hz
      simpa only [hz, Multiset.notMem_zero] using hm
    · have h := hcount i hin
      intro hz
      simp only [hz, Multiset.card_zero] at h
      omega
  have hdisk (i : ℕ) (hin : i < n) (x : ℝ) (hx : x ∈ (F i).roots) :
      -1 ≤ x ∧ x ≤ 1 := by
    have heval : (row a (i + 1)).eval (x : ℂ) = 0 := by
      rw [← hmap i hin]
      exact (Polynomial.isRoot_of_mem_roots hx).map (f := Complex.ofRealHom)
    have hnorm := row_root_norm_le_one a ha (i + 1) (by omega) (by omega) (x : ℂ) heval
    have habs : |x| ≤ 1 := by simpa using hnorm
    exact abs_le.mp habs
  obtain ⟨x, hx, _, hcost⟩ := real_tower_monotone_chain (by omega) F hdegree hderiv hdefect hreal hdisk
  refine ⟨fun i => (x i.val : ℂ), ?_, hcost⟩
  intro i
  rw [← hmap i.val i.isLt]
  exact (show (F i.val).IsRoot (x i.val) from hx i.val i.isLt).map (f := Complex.ofRealHom)

end DerivativeChainPrivate



set_option autoImplicit false

namespace DerivativeChainPrivate



theorem root_esymm_one {R : Type*} [CommRing R] (s : Multiset R) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]

theorem root_esymm_cons {R : Type*} [CommRing R] (a : R) (s : Multiset R) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons]
  rw [← Multiset.sum_map_mul_left]

theorem root_sum_sq {R : Type*} [CommRing R] (s : Multiset R) :
    (s.map (fun z => z ^ 2)).sum = s.sum ^ 2 - 2 * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, root_esymm_cons, root_esymm_one]
    rw [ih]
    ring

theorem root_sum_cube {R : Type*} [CommRing R] (s : Multiset R) :
    (s.map (fun z => z ^ 3)).sum = s.sum ^ 3 - 3 * s.sum * s.esymm 2 + 3 * s.esymm 3 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, root_esymm_cons, root_esymm_one]
    rw [ih]
    ring

theorem centered_monic_coeff_two_three (p : Polynomial ℂ) (hp : p.Monic)
    (hn : 3 ≤ p.natDegree) (hsum : p.roots.sum = 0) :
    p.coeff (p.natDegree - 2) = -(p.roots.map (fun z => z ^ 2)).sum / 2 ∧
      p.coeff (p.natDegree - 3) = -(p.roots.map (fun z => z ^ 3)).sum / 3 := by
  have hv2 := Polynomial.coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits p)
    (k := p.natDegree - 2) (Nat.sub_le _ _)
  have hv3 := Polynomial.coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits p)
    (k := p.natDegree - 3) (Nat.sub_le _ _)
  rw [hp.leadingCoeff, one_mul, show p.natDegree - (p.natDegree - 2) = 2 by omega] at hv2
  rw [hp.leadingCoeff, one_mul, show p.natDegree - (p.natDegree - 3) = 3 by omega] at hv3
  constructor
  · rw [hv2, root_sum_sq, hsum]
    ring
  · rw [hv3, root_sum_cube, hsum]
    ring

theorem complex_moment_identities (s : Multiset ℂ) :
    ((s.map (fun z => z ^ 2)).sum).re =
        (s.map (fun z => z.re ^ 2)).sum - (s.map (fun z => z.im ^ 2)).sum ∧
      (s.map (fun z => ‖z‖ ^ 2)).sum =
        (s.map (fun z => z.re ^ 2)).sum + (s.map (fun z => z.im ^ 2)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    have hz := Complex.sq_norm_sub_sq_re z
    simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_re,
      pow_two, Complex.mul_re] at *
    constructor <;> nlinarith [ih.1, ih.2]

theorem imag_sq_sum_le_nonreal_card (s : Multiset ℂ)
    (h : ∀ z ∈ s, |z.im| ≤ 1) :
    (s.map (fun z => z.im ^ 2)).sum ≤
      ((s.filter (fun z => z.im ≠ 0)).card : ℝ) := by
  classical
  revert h
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    intro h
    have htail := ih (fun w hw => h w (Multiset.mem_cons_of_mem hw))
    have hz := abs_le.mp (h z (Multiset.mem_cons_self _ _))
    by_cases hi : z.im = 0
    · simpa [Multiset.filter_cons, hi] using htail
    · simp only [Multiset.map_cons, Multiset.sum_cons,
        Multiset.filter_cons_of_pos (p := fun w : ℂ => w.im ≠ 0) (a := z) s hi,
        Multiset.card_cons, Nat.cast_add, Nat.cast_one]
      nlinarith

theorem cube_sum_norm_le_twice_energy (s : Multiset ℂ) (h : ∀ z ∈ s, ‖z‖ ≤ 2) :
    ‖(s.map (fun z => z ^ 3)).sum‖ ≤ 2 * (s.map (fun z => ‖z‖ ^ 2)).sum := by
  revert h
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    intro h
    have htail := ih (fun w hw => h w (Multiset.mem_cons_of_mem hw))
    have hz := h z (Multiset.mem_cons_self _ _)
    have hcube : ‖z ^ 3‖ ≤ 2 * ‖z‖ ^ 2 := by
      rw [norm_pow]
      nlinarith [mul_nonneg (show 0 ≤ 2 - ‖z‖ by linarith) (sq_nonneg ‖z‖)]
    simp only [Multiset.map_cons, Multiset.sum_cons]
    calc
      ‖z ^ 3 + (s.map (fun z => z ^ 3)).sum‖ ≤
          ‖z ^ 3‖ + ‖(s.map (fun z => z ^ 3)).sum‖ := norm_add_le _ _
      _ ≤ 2 * ‖z‖ ^ 2 + 2 * (s.map (fun z => ‖z‖ ^ 2)).sum := add_le_add hcube htail
      _ = 2 * (‖z‖ ^ 2 + (s.map (fun z => ‖z‖ ^ 2)).sum) := by ring

theorem one_pair_moment_budget (s : Multiset ℂ)
    (hc : (s.filter (fun z => z.im ≠ 0)).card ≤ 2)
    (him : ∀ z ∈ s, |z.im| ≤ 1) (hnorm : ∀ z ∈ s, ‖z‖ ≤ 2)
    (hsquare : ((s.map (fun z => z ^ 2)).sum).re ≤ 0) :
    -2 ≤ ((s.map (fun z => z ^ 2)).sum).re ∧
      (s.map (fun z => ‖z‖ ^ 2)).sum ≤ 4 ∧ ‖(s.map (fun z => z ^ 3)).sum‖ ≤ 8 := by
  have hI := imag_sq_sum_le_nonreal_card s him
  have hcard : ((s.filter (fun z => z.im ≠ 0)).card : ℝ) ≤ 2 := by exact_mod_cast hc
  have hR : 0 ≤ (s.map (fun z => z.re ^ 2)).sum := by
    apply Multiset.sum_nonneg
    intro x hx
    obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hx
    exact sq_nonneg z.re
  obtain ⟨hre, henergy⟩ := complex_moment_identities s
  have hE : (s.map (fun z => ‖z‖ ^ 2)).sum ≤ 4 := by linarith
  refine ⟨by linarith, hE, ?_⟩
  have hcube := cube_sum_norm_le_twice_energy s hnorm
  linarith

theorem centered_monic_roots_sum_zero (p : Polynomial ℂ) (hp : p.Monic)
    (hn : 0 < p.natDegree) (hcenter : p.coeff (p.natDegree - 1) = 0) :
    p.roots.sum = 0 := by
  have hv := Polynomial.coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits p)
    (k := p.natDegree - 1) (Nat.sub_le _ _)
  rw [hcenter, hp.leadingCoeff, one_mul,
    show p.natDegree - (p.natDegree - 1) = 1 by omega, root_esymm_one] at hv
  simpa using hv.symm

end DerivativeChainPrivate



set_option autoImplicit false

namespace DerivativeChainPrivate

theorem real_tower_short_suffix {n : ℕ} (hn : 0 < n) (F : ℕ → Polynomial ℝ)
    (hderiv : ∀ i < n - 1, (F (i + 1)).derivative = F i)
    (hcount : ∀ i < n - 1, (F (i + 1)).roots.card = (F i).roots.card + 1)
    (hreal : ∀ i < n, (F i).roots ≠ 0)
    (L R : ℝ) (hwidth : R - L ≤ 2)
    (hdisk : ∀ i < n, ∀ x ∈ (F i).roots, L ≤ x ∧ x ≤ R)
    (a : ℝ) (ha : a ∈ (F 0).roots) :
    ∃ x : ℕ → ℝ, x 0 = a ∧ (∀ i < n, (F i).eval (x i) = 0) ∧
      chainCost (fun i : Fin n => (x i.val : ℂ)) ≤ 1 := by
  classical
  let lo (i : ℕ) := if i = 0 then a else if h : i < n then
    (F i).roots.toFinset.min' (Multiset.toFinset_nonempty.mpr (hreal i h)) else a
  let hi (i : ℕ) := if i = 0 then a else if h : i < n then
    (F i).roots.toFinset.max' (Multiset.toFinset_nonempty.mpr (hreal i h)) else a
  have hLo0 : lo 0 = a := by simp [lo]
  have hHi0 : hi 0 = a := by simp [hi]
  have hlomem (i : ℕ) (hin : i < n) : lo i ∈ (F i).roots := by
    by_cases hi0 : i = 0
    · subst i; simpa only [hLo0] using ha
    · simpa only [lo, if_neg hi0, dif_pos hin, Multiset.mem_toFinset] using
        Finset.min'_mem (F i).roots.toFinset (Multiset.toFinset_nonempty.mpr (hreal i hin))
  have hhimem (i : ℕ) (hin : i < n) : hi i ∈ (F i).roots := by
    by_cases hi0 : i = 0
    · subst i; simpa only [hHi0] using ha
    · simpa only [hi, if_neg hi0, dif_pos hin, Multiset.mem_toFinset] using
        Finset.max'_mem (F i).roots.toFinset (Multiset.toFinset_nonempty.mpr (hreal i hin))
  have hinterval (i : ℕ) (hin : i < n - 1) :
      ∀ x ∈ (F i).roots,
        (F (i + 1)).roots.toFinset.min' (Multiset.toFinset_nonempty.mpr (hreal _ (by omega))) ≤ x ∧
        x ≤ (F (i + 1)).roots.toFinset.max' (Multiset.toFinset_nonempty.mpr (hreal _ (by omega))) := by
    let s := (F (i + 1)).roots.toFinset
    have hs : s.Nonempty := Multiset.toFinset_nonempty.mpr (hreal _ (by omega))
    have h := real_derivative_roots_interval_of_count_eq (F (i + 1)) (s.min' hs) (s.max' hs)
      (fun x hx => ⟨Finset.min'_le _ x (Multiset.mem_toFinset.mpr hx),
        Finset.le_max' _ x (Multiset.mem_toFinset.mpr hx)⟩)
      (by simpa only [hderiv i hin] using hcount i hin)
    simpa only [hderiv i hin] using h
  have hLo (i : ℕ) (hin : i < n - 1) : lo (i + 1) ≤ lo i := by
    have h := (hinterval i hin (lo i) (hlomem _ (by omega))).1
    simpa only [lo, if_neg (by omega : i + 1 ≠ 0), dif_pos (by omega : i + 1 < n)] using h
  have hHi (i : ℕ) (hin : i < n - 1) : hi i ≤ hi (i + 1) := by
    have h := (hinterval i hin (hi i) (hhimem _ (by omega))).2
    simpa only [hi, if_neg (by omega : i + 1 ≠ 0), dif_pos (by omega : i + 1 < n)] using h
  have hLoCost := chainCost_of_real_nonincreasing lo hLo
  have hHiCost := chainCost_of_real_nondecreasing hi hHi
  rw [hLo0] at hLoCost
  rw [hHi0] at hHiCost
  have hLoEnd := hdisk (n - 1) (by omega) _ (hlomem _ (by omega))
  have hHiEnd := hdisk (n - 1) (by omega) _ (hhimem _ (by omega))
  by_cases h : a - lo (n - 1) ≤ 1
  · exact ⟨lo, hLo0, (fun i hin => Polynomial.isRoot_of_mem_roots (hlomem _ hin)),
      hLoCost.le.trans h⟩
  · refine ⟨hi, hHi0, (fun i hin => Polynomial.isRoot_of_mem_roots (hhimem _ hin)), ?_⟩
    rw [hHiCost]
    linarith

end DerivativeChainPrivate



set_option autoImplicit false

namespace DerivativeChainPrivate

theorem real_iterate_natDegree (p : Polynomial ℝ) (k : ℕ) :
    ((Polynomial.derivative^[k]) p).natDegree = p.natDegree - k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Polynomial.natDegree_derivative, ih]
    omega

theorem iterate_derivative_real_translate (p : Polynomial ℝ) (u : ℝ) (k : ℕ) :
    (Polynomial.derivative^[k]) (p.comp (Polynomial.X + Polynomial.C u)) =
      ((Polynomial.derivative^[k]) p).comp (Polynomial.X + Polynomial.C u) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply', ih, Polynomial.derivative_comp,
      Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C,
      add_zero, one_mul]

theorem centered_quadratic_row (p : Polynomial ℝ) (hp : p.Monic) (n : ℕ)
    (hd : p.natDegree = n) (hn : 2 ≤ n) (hcenter : p.coeff (n - 1) = 0) :
    (Polynomial.derivative^[n - 2]) p =
      Polynomial.C ((n - 2).factorial : ℝ) *
        (Polynomial.C (n.choose 2 : ℝ) * Polynomial.X ^ 2 + Polynomial.C (p.coeff (n - 2))) := by
  have htop : p.coeff n = 1 := by rw [← hd, Polynomial.coeff_natDegree, hp.leadingCoeff]
  have hdeg : ((Polynomial.derivative^[n - 2]) p).natDegree ≤ 2 := by
    rw [real_iterate_natDegree, hd]
    omega
  ext k
  by_cases hk : k ≤ 2
  · interval_cases k
    · simp [Polynomial.coeff_iterate_derivative, Nat.descFactorial_self, nsmul_eq_mul, mul_comm]
    · simp [Polynomial.coeff_iterate_derivative, show 1 + (n - 2) = n - 1 by omega, hcenter]
    · simp [Polynomial.coeff_iterate_derivative, show 2 + (n - 2) = n by omega, htop,
        Nat.descFactorial_eq_factorial_mul_choose, Nat.choose_symm hn, nsmul_eq_mul, mul_comm]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    symm
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hmodel : (Polynomial.C ((n - 2).factorial : ℝ) *
        (Polynomial.C (n.choose 2 : ℝ) * Polynomial.X ^ 2 + Polynomial.C (p.coeff (n - 2)))).natDegree ≤ 2 := by
      compute_degree!
    omega

theorem centered_cubic_row (p : Polynomial ℝ) (hp : p.Monic) (n : ℕ)
    (hd : p.natDegree = n) (hn : 3 ≤ n) (hcenter : p.coeff (n - 1) = 0) :
    (Polynomial.derivative^[n - 3]) p =
      Polynomial.C ((n - 3).factorial : ℝ) *
        (Polynomial.C (n.choose 3 : ℝ) * Polynomial.X ^ 3 +
          Polynomial.C (((n - 2 : ℕ) : ℝ) * p.coeff (n - 2)) * Polynomial.X +
          Polynomial.C (p.coeff (n - 3))) := by
  have htop : p.coeff n = 1 := by rw [← hd, Polynomial.coeff_natDegree, hp.leadingCoeff]
  have hdeg : ((Polynomial.derivative^[n - 3]) p).natDegree ≤ 3 := by
    rw [real_iterate_natDegree, hd]
    omega
  have hchoose : (n - 2).choose (n - 3) = n - 2 := by
    rw [Nat.choose_symm_of_eq_add (by omega : n - 2 = (n - 3) + 1), Nat.choose_one_right]
  ext k
  by_cases hk : k ≤ 3
  · interval_cases k
    · simp [Polynomial.coeff_iterate_derivative, Nat.descFactorial_self, nsmul_eq_mul, mul_comm]
    · simp [Polynomial.coeff_iterate_derivative, show 1 + (n - 3) = n - 2 by omega,
        Nat.descFactorial_eq_factorial_mul_choose, hchoose, nsmul_eq_mul]
      ring
    · simp [Polynomial.coeff_iterate_derivative, show 2 + (n - 3) = n - 1 by omega, hcenter]
    · simp [Polynomial.coeff_iterate_derivative, show 3 + (n - 3) = n by omega, htop,
        Nat.descFactorial_eq_factorial_mul_choose, Nat.choose_symm hn, nsmul_eq_mul, mul_comm]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    symm
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hmodel : (Polynomial.C ((n - 3).factorial : ℝ) *
        (Polynomial.C (n.choose 3 : ℝ) * Polynomial.X ^ 3 +
          Polynomial.C (((n - 2 : ℕ) : ℝ) * p.coeff (n - 2)) * Polynomial.X +
          Polynomial.C (p.coeff (n - 3)))).natDegree ≤ 3 := by
      compute_degree!
    omega

end DerivativeChainPrivate



set_option autoImplicit false

namespace DerivativeChainPrivate

theorem cubic_coordinate_abs_le (A T C x : ℝ) (hA : 20 ≤ A) (hT : 0 ≤ T)
    (hC : |C| ≤ (8 : ℝ) / 3) (heq : A * x ^ 3 + T * x + C = 0) : |x| ≤ 3 / 5 := by
  have hmain : A * |x| ^ 3 ≤ |C| := by
    by_cases hx : 0 ≤ x
    · have hx3 : 0 ≤ x ^ 3 := by positivity
      have hprod := mul_nonneg (show 0 ≤ A by linarith) hx3
      have hlin := mul_nonneg hT hx
      have hsign : C ≤ 0 := by linarith
      rw [abs_of_nonneg hx, abs_of_nonpos hsign]
      linarith
    · have hx0 : x ≤ 0 := le_of_not_ge hx
      have hx3 : x ^ 3 ≤ 0 := by nlinarith only
        [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) hx0]
      have hprod := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ A by linarith) hx3
      have hlin := mul_nonpos_of_nonneg_of_nonpos hT hx0
      have hsign : 0 ≤ C := by linarith
      rw [abs_of_nonpos hx0, abs_of_nonneg hsign]
      nlinarith only [heq, hlin]
  have hsmall : |x| ^ 3 ≤ (2 : ℝ) / 15 := by
    have hprod := mul_le_mul_of_nonneg_right hA (show 0 ≤ |x| ^ 3 by positivity)
    linarith
  by_contra hx
  have hlarge : (3 : ℝ) / 5 < |x| := lt_of_not_ge hx
  have hfactor := mul_pos (sub_pos.mpr hlarge)
    (show 0 < |x| ^ 2 + (3 / 5) * |x| + (3 / 5) ^ 2 by positivity)
  nlinarith

theorem short_prefix_of_coordinates (x b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 3 / 10)
    (hx : |x| ≤ 3 / 5) :
    ‖(b : ℂ) * Complex.I‖ + ‖(x : ℂ) - (b : ℂ) * Complex.I‖ ≤ 1 := by
  have hfirst : ‖(b : ℂ) * Complex.I‖ = b := by simp [norm_mul, abs_of_nonneg hb0]
  have hsq : ‖(x : ℂ) - (b : ℂ) * Complex.I‖ ^ 2 = x ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hx0 := abs_le.mp hx
  have hx2 : x ^ 2 ≤ (9 : ℝ) / 25 := by nlinarith
  have hnonneg : 0 ≤ 1 - b := by linarith
  have hsqbound : ‖(x : ℂ) - (b : ℂ) * Complex.I‖ ^ 2 ≤ (1 - b) ^ 2 := by nlinarith
  have hsecond := (sq_le_sq₀ (norm_nonneg ((x : ℂ) - (b : ℂ) * Complex.I)) hnonneg).mp hsqbound
  rw [hfirst]
  linarith

end DerivativeChainPrivate



set_option autoImplicit false

namespace DerivativeChainPrivate

theorem centered_one_pair_cubic_prefix (p : Polynomial ℝ) (hp : p.Monic) (n : ℕ)
    (hd : p.natDegree = n) (hn : 6 ≤ n) (hcenter : p.coeff (n - 1) = 0)
    (hc : p.natDegree - p.roots.card ≤ 2)
    (him : ∀ z ∈ (p.map Complex.ofRealHom).roots, |z.im| ≤ 1)
    (hnorm : ∀ z ∈ (p.map Complex.ofRealHom).roots, ‖z‖ ≤ 2)
    (hno : ∀ x : ℝ, ((Polynomial.derivative^[n - 2]) p).eval x ≠ 0) :
    ∃ b : ℝ, 0 ≤ b ∧
      (((Polynomial.derivative^[n - 2]) p).map Complex.ofRealHom).eval
        ((b : ℂ) * Complex.I) = 0 ∧
      ∀ x : ℝ, ((Polynomial.derivative^[n - 3]) p).eval x = 0 →
        ‖(b : ℂ) * Complex.I‖ + ‖(x : ℂ) - (b : ℂ) * Complex.I‖ ≤ 1 := by
  let A : ℝ := (n.choose 2 : ℝ)
  let B : ℝ := p.coeff (n - 2)
  have hA_nat := Nat.choose_le_choose 2 hn
  norm_num [Nat.choose] at hA_nat
  have hA : 15 ≤ A := by
    dsimp only [A]
    exact_mod_cast hA_nat
  have hApos : 0 < A := by linarith
  have hBpos : 0 < B := by
    by_contra hB
    let x := Real.sqrt (-B / A)
    have hrad : 0 ≤ -B / A := div_nonneg (by linarith) hApos.le
    have hsq : x ^ 2 * A = -B :=
      (eq_div_iff (ne_of_gt hApos)).mp (Real.sq_sqrt hrad)
    apply hno x
    rw [centered_quadratic_row p hp n hd (by omega) hcenter]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_X]
    change ((n - 2).factorial : ℝ) * (A * x ^ 2 + B) = 0
    rw [show A * x ^ 2 + B = 0 by nlinarith, mul_zero]
  let Q := p.map Complex.ofRealHom
  have hQdegree : Q.natDegree = n := by simp only [Q, Polynomial.natDegree_map, hd]
  have hQcenter : Q.coeff (Q.natDegree - 1) = 0 := by
    rw [hQdegree]
    simp only [Q, Polynomial.coeff_map, hcenter, map_zero]
  have hsum := centered_monic_roots_sum_zero Q (hp.map Complex.ofRealHom)
    (by rw [hQdegree]; omega) hQcenter
  have hv := centered_monic_coeff_two_three Q (hp.map Complex.ofRealHom)
    (by rw [hQdegree]; omega) hsum
  have h2 : ((Q.roots.map (fun z => z ^ 2)).sum).re = -2 * B := by
    have h := congrArg Complex.re hv.1
    norm_num [Q, Polynomial.natDegree_map, hd, Polynomial.coeff_map, Complex.div_re] at h
    linarith
  have h3 : |p.coeff (n - 3)| = ‖(Q.roots.map (fun z => z ^ 3)).sum‖ / 3 := by
    have h := congrArg (fun z : ℂ => ‖z‖) hv.2
    simpa [Q, Polynomial.natDegree_map, hd, Polynomial.coeff_map, norm_div] using h
  have hnc : (Q.roots.filter (fun z => z.im ≠ 0)).card ≤ 2 := by
    rw [nonreal_roots_of_real_polynomial]
    exact hc
  obtain ⟨hlower, _, hcube⟩ := one_pair_moment_budget Q.roots hnc him hnorm
    (by rw [h2]; linarith)
  have hBupper : B ≤ 1 := by linarith
  have hCupper : |p.coeff (n - 3)| ≤ (8 : ℝ) / 3 := by linarith
  let b := Real.sqrt (B / A)
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hbrel : A * b ^ 2 = B := by
    have h := (eq_div_iff (ne_of_gt hApos)).mp
      (Real.sq_sqrt (show 0 ≤ B / A by positivity))
    simpa only [b, mul_comm] using h
  have hb : b ≤ 3 / 10 := by
    have hprod := mul_le_mul_of_nonneg_right hA (sq_nonneg b)
    nlinarith
  refine ⟨b, hb0, ?_, ?_⟩
  · rw [centered_quadratic_row p hp n hd (by omega) hcenter]
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    change (((n - 2).factorial : ℝ) : ℂ) *
      ((A : ℂ) * ((b : ℂ) * Complex.I) ^ 2 + (B : ℂ)) = 0
    have hzero : (A : ℂ) * ((b : ℂ) * Complex.I) ^ 2 + (B : ℂ) = 0 := by
      calc
        _ = ((B - A * b ^ 2 : ℝ) : ℂ) := by
          push_cast
          rw [mul_pow, Complex.I_sq]
          ring
        _ = 0 := by rw [show B - A * b ^ 2 = 0 by linarith]; rfl
    rw [hzero, mul_zero]
  · intro x hx
    have hpoly : (n.choose 3 : ℝ) * x ^ 3 + (((n - 2 : ℕ) : ℝ) * B) * x +
        p.coeff (n - 3) = 0 := by
      rw [centered_cubic_row p hp n hd (by omega) hcenter] at hx
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X] at hx
      exact (mul_eq_zero.mp hx).resolve_left
        (by exact_mod_cast Nat.factorial_ne_zero (n - 3))
    have hA3_nat := Nat.choose_le_choose 3 hn
    norm_num [Nat.choose] at hA3_nat
    have hA3 : (20 : ℝ) ≤ (n.choose 3 : ℝ) := by exact_mod_cast hA3_nat
    have hxbound := cubic_coordinate_abs_le (n.choose 3 : ℝ)
      (((n - 2 : ℕ) : ℝ) * B) (p.coeff (n - 3)) x hA3 (by positivity) hCupper hpoly
    exact short_prefix_of_coordinates x b hb0 hb hxbound

end DerivativeChainPrivate



set_option autoImplicit false

namespace DerivativeChainPrivate

theorem real_row_count_of_nonreal_quadratic (p : Polynomial ℝ) (n : ℕ)
    (hd : p.natDegree = n) (hc : p.natDegree - p.roots.card ≤ 2)
    (hno : ∀ x : ℝ, ((Polynomial.derivative^[n - 2]) p).eval x ≠ 0)
    (m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) :
    ((Polynomial.derivative^[n - m]) p).roots.card = m - 2 := by
  have hzero : ((Polynomial.derivative^[n - 2]) p).roots = 0 := by
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    intro x hx
    exact hno x (Polynomial.isRoot_of_mem_roots hx)
  let R := (Polynomial.derivative^[n - m]) p
  have hdegree : R.natDegree = m := by
    rw [real_iterate_natDegree, hd]
    omega
  have hdegree2 : ((Polynomial.derivative^[n - 2]) p).natDegree = 2 := by
    rw [real_iterate_natDegree, hd]
    omega
  have hcomp : (Polynomial.derivative^[m - 2]) R = (Polynomial.derivative^[n - 2]) p := by
    dsimp only [R]
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  have hlower := real_root_defect_iterate R (m - 2)
  rw [hcomp, hzero, Multiset.card_zero, hdegree2, Nat.sub_zero, hdegree] at hlower
  have hupper := (real_root_defect_iterate p (n - m)).trans hc
  change R.natDegree - R.roots.card ≤ 2 at hupper
  rw [hdegree] at hupper
  have hcard := Polynomial.card_roots' R
  change R.roots.card = m - 2
  omega

theorem centered_one_pair_complete (p : Polynomial ℝ) (hp : p.Monic) (n : ℕ)
    (hd : p.natDegree = n) (hn : 6 ≤ n) (hcenter : p.coeff (n - 1) = 0)
    (hc : p.natDegree - p.roots.card ≤ 2) (u : ℝ)
    (hdisk : ∀ m : ℕ, 0 < m → m ≤ n → ∀ z : ℂ,
      (((Polynomial.derivative^[n - m]) p).map Complex.ofRealHom).eval z = 0 →
        ‖z + (u : ℂ)‖ ≤ 1)
    (hno : ∀ x : ℝ, ((Polynomial.derivative^[n - 2]) p).eval x ≠ 0) :
    ∃ z : Fin n → ℂ,
      (∀ i : Fin n, (((Polynomial.derivative^[n - (i.val + 1)]) p).map
        Complex.ofRealHom).eval (z i) = 0) ∧ chainCost z ≤ 2 := by
  have hrow1 : (((Polynomial.derivative^[n - 1]) p).map Complex.ofRealHom).eval 0 = 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map, Polynomial.coeff_iterate_derivative]
    simp [hcenter]
  have hu : ‖(u : ℂ)‖ ≤ 1 := by
    simpa using hdisk 1 (by omega) (by omega) 0 hrow1
  have htop (z : ℂ) (hz : z ∈ (p.map Complex.ofRealHom).roots) : ‖z + (u : ℂ)‖ ≤ 1 := by
    have heval := (Polynomial.mem_roots
      ((Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr hp.ne_zero)).mp hz
    exact hdisk n (by omega) le_rfl z (by simpa using heval)
  have him (z : ℂ) (hz : z ∈ (p.map Complex.ofRealHom).roots) : |z.im| ≤ 1 := by
    have h := (Complex.abs_im_le_norm (z + (u : ℂ))).trans (htop z hz)
    simpa using h
  have hnorm (z : ℂ) (hz : z ∈ (p.map Complex.ofRealHom).roots) : ‖z‖ ≤ 2 := by
    calc
      ‖z‖ = ‖(z + (u : ℂ)) - (u : ℂ)‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖z + (u : ℂ)‖ + ‖(u : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith [htop z hz]
  obtain ⟨b, _, hbroot, hbudget⟩ := centered_one_pair_cubic_prefix p hp n hd hn hcenter hc him hnorm hno
  let F (i : ℕ) := (Polynomial.derivative^[n - (i + 3)]) p
  have hcard (i : ℕ) (hin : i < n - 2) : (F i).roots.card = i + 1 := by
    have h := real_row_count_of_nonreal_quadratic p n hd hc hno (i + 3) (by omega) (by omega)
    change (F i).roots.card = i + 3 - 2 at h
    omega
  have hreal (i : ℕ) (hin : i < n - 2) : (F i).roots ≠ 0 := by
    intro hz
    have h := hcard i hin
    rw [hz, Multiset.card_zero] at h
    omega
  have hderiv (i : ℕ) (hin : i < n - 2 - 1) : (F (i + 1)).derivative = F i := by
    dsimp only [F]
    have heq : n - (i + 3) = n - (i + 1 + 3) + 1 := by omega
    rw [heq, Function.iterate_succ_apply']
  have hcount (i : ℕ) (hin : i < n - 2 - 1) : (F (i + 1)).roots.card = (F i).roots.card + 1 := by
    rw [hcard (i + 1) (by omega), hcard i (by omega)]
  have hbounds (i : ℕ) (hin : i < n - 2) (x : ℝ) (hx : x ∈ (F i).roots) :
      -1 - u ≤ x ∧ x ≤ 1 - u := by
    have heval : ((F i).map Complex.ofRealHom).eval (x : ℂ) = 0 :=
      (Polynomial.isRoot_of_mem_roots hx).map (f := Complex.ofRealHom)
    have hb := hdisk (i + 3) (by omega) (by omega) (x : ℂ) heval
    have habs : |x + u| ≤ 1 := by
      simpa only [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs] using hb
    have h := abs_le.mp habs
    constructor <;> linarith
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero (hreal 0 (by omega))
  obtain ⟨x, hx0, hxroots, hxcost⟩ := real_tower_short_suffix (by omega) F hderiv hcount hreal
    (-1 - u) (1 - u) (by linarith) hbounds a ha
  have haeval : ((Polynomial.derivative^[n - 3]) p).eval a = 0 :=
    Polynomial.isRoot_of_mem_roots ha
  have hprefix := hbudget a haeval
  let w : ℂ := (b : ℂ) * Complex.I
  let z (i : ℕ) := if i = 0 then 0 else if i = 1 then w else (x (i - 2) : ℂ)
  refine ⟨fun i => z i.val, ?_, ?_⟩
  · intro i
    by_cases hi0 : i.val = 0
    · simpa [z, hi0] using hrow1
    by_cases hi1 : i.val = 1
    · simpa [z, hi1, w] using hbroot
    · have heq : i.val - 2 + 3 = i.val + 1 := by omega
      have hroot : (F (i.val - 2)).IsRoot (x (i.val - 2)) := hxroots _ (by omega)
      have h : ((F (i.val - 2)).map Complex.ofRealHom).eval (x (i.val - 2) : ℂ) = 0 :=
        hroot.map (f := Complex.ofRealHom)
      simpa only [F, heq, z, if_neg hi0, if_neg hi1] using h
  · have hcost : chainCost (fun i : Fin n => z i.val) =
        ‖w‖ + ‖(a : ℂ) - w‖ + chainCost (fun i : Fin (n - 2) => (x i.val : ℂ)) := by
      simpa only [z, sub_zero, hx0] using
        chainCost_prepend_two n (by omega) 0 w (fun j => (x j : ℂ))
    rw [hcost]
    linarith

end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution {n : ℕ} (a : Fin n → ℂ)
    (hn : 1 ≤ n) (ha : ∀ i, ‖a i‖ ≤ 1)
    (hr : RealCoefficients a) (hc : nonrealCount a ≤ 2) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z ≤ 2 := by
  by_cases hn5 : n ≤ 5
  · obtain ⟨z, hz, hcost⟩ := exists_chain_cost_le_sqrt (by omega) a ha
    refine ⟨z, hz, hcost.trans ?_⟩
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h4 : ((n - 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (show n - 1 ≤ 4 by omega)
    nlinarith
  by_cases hquad : ∃ x : ℝ, (row a 2).eval (x : ℂ) = 0
  · exact almostRealOnePair_of_real_quadratic a (by omega) ha hr hc hquad
  obtain ⟨p, hp, hrows⟩ := almost_real_row_count a hr
  have hpdegree : p.natDegree = n := by
    simpa only [Nat.sub_self, Function.iterate_zero_apply] using (hrows n le_rfl).2.1
  have hpmonic : p.Monic := by
    apply (Polynomial.monic_map_iff (f := Complex.ofRealHom)).mp
    rw [hp]
    exact Polynomial.monic_prod_X_sub_C a Finset.univ
  have hpcount : p.natDegree - p.roots.card ≤ 2 := by
    rw [root_slot_nonreal_count a p hp]
    exact hc
  let P1 := (Polynomial.derivative^[n - 1]) p
  have hP1degree : P1.natDegree = 1 := by
    rw [real_iterate_natDegree, hpdegree]
    omega
  have hsplit := Polynomial.Splits.of_natDegree_eq_one hP1degree
  obtain ⟨u, humem⟩ := Multiset.exists_mem_of_ne_zero
    (hsplit.roots_ne_zero (by rw [hP1degree]; decide))
  have hu : P1.eval u = 0 := Polynomial.isRoot_of_mem_roots humem
  let q := p.comp (Polynomial.X + Polynomial.C u)
  have hqdegree : q.natDegree = n := by
    simp only [q, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one, hpdegree]
  have hqmonic : q.Monic := hpmonic.comp_X_add_C u
  have hqcard : q.roots.card = p.roots.card := by
    have h := congrArg Multiset.card (p.map_roots_comp_C_mul_X_add_C 1 u isUnit_one)
    simpa [q] using h
  have hqcount : q.natDegree - q.roots.card ≤ 2 := by
    rw [hqdegree, hqcard]
    simpa only [hpdegree] using hpcount
  have hqcenter : q.coeff (n - 1) = 0 := by
    have hrow : ((Polynomial.derivative^[n - 1]) q).eval 0 = 0 := by
      rw [iterate_derivative_real_translate]
      simpa only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C, zero_add] using hu
    have hfactor : ((n - 1).factorial : ℝ) * q.coeff (n - 1) = 0 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative] at hrow
      simpa [Nat.descFactorial_self, nsmul_eq_mul, mul_comm] using hrow
    exact (mul_eq_zero.mp hfactor).resolve_left
      (by exact_mod_cast Nat.factorial_ne_zero (n - 1))
  have htranslate (m : ℕ) (hm : m ≤ n) (z : ℂ) :
      (((Polynomial.derivative^[n - m]) q).map Complex.ofRealHom).eval z =
        (row a m).eval (z + (u : ℂ)) := by
    rw [iterate_derivative_real_translate, Polynomial.map_comp, (hrows m hm).1]
    simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    rfl
  have hdisk (m : ℕ) (hm0 : 0 < m) (hm : m ≤ n) (z : ℂ)
      (hz : (((Polynomial.derivative^[n - m]) q).map Complex.ofRealHom).eval z = 0) :
      ‖z + (u : ℂ)‖ ≤ 1 := by
    rw [htranslate m hm z] at hz
    exact row_root_norm_le_one a ha m hm0 hm (z + (u : ℂ)) hz
  have hno (x : ℝ) : ((Polynomial.derivative^[n - 2]) q).eval x ≠ 0 := by
    intro hx
    apply hquad
    refine ⟨x + u, ?_⟩
    have h : (((Polynomial.derivative^[n - 2]) q).map Complex.ofRealHom).eval (x : ℂ) = 0 :=
      (show ((Polynomial.derivative^[n - 2]) q).IsRoot x from hx).map (f := Complex.ofRealHom)
    rw [htranslate 2 (by omega) (x : ℂ)] at h
    simpa only [Complex.ofReal_add] using h
  obtain ⟨z, hz, hcost⟩ := centered_one_pair_complete q hqmonic n hqdegree
    (by omega) hqcenter hqcount u hdisk hno
  refine ⟨fun i => z i + (u : ℂ), ?_, ?_⟩
  · intro i
    rw [← htranslate (i.val + 1) (by omega) (z i)]
    exact hz i
  · rw [chainCost_translate]
    exact hcost
