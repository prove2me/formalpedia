-- Prove2me | solution 1 for BraidsLinksMCG.configForget_lift_path_homotopy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-22T14:30:48.993725+00:00
-- url     : https://prove2.me/submissions/7b57f4b8-e0cd-4972-942e-cc88d49a04b1

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

open BraidsLinksMCG unitInterval
open scoped BigOperators

noncomputable section

private def weight (r : ℝ) (a z : ℂ) : ℝ := max (r - dist z a) 0 / r

private def move (n : ℕ) (r : ℝ) (a b : Fin n → ℂ) (z : ℂ) : ℂ :=
  z + ∑ i, weight r (a i) z • (b i - a i)

private lemma weight_self {r : ℝ} (hr : 0 < r) (a : ℂ) : weight r a a = 1 := by
  simp [weight, max_eq_left hr.le, ne_of_gt hr]

private lemma weight_far {r : ℝ} (a z : ℂ) (h : r ≤ dist z a) : weight r a z = 0 := by
  simp [weight, max_eq_right (sub_nonpos.mpr h)]

private lemma move_self (n : ℕ) (r : ℝ) (a : Fin n → ℂ) (z : ℂ) : move n r a a z = z := by
  simp [move]

private lemma move_point (n : ℕ) {r : ℝ} (hr : 0 < r) (a b : Fin n → ℂ)
    (ha : ∀ i j, i ≠ j → r ≤ dist (a i) (a j)) (i : Fin n) :
    move n r a b (a i) = b i := by
  classical
  rw [move, Finset.sum_eq_single i]
  · rw [weight_self hr, one_smul]
    abel
  · intro j _ hji
    rw [weight_far (a j) (a i) (ha i j (Ne.symm hji)), zero_smul]
  · simp

private lemma weight_dist {r : ℝ} (hr : 0 < r) (a x y : ℂ) :
    |weight r a x - weight r a y| ≤ dist x y / r := by
  have h := abs_max_sub_max_le_abs (r - dist x a) (r - dist y a) 0
  have he : (r - dist x a) - (r - dist y a) = -(dist x a - dist y a) := by ring
  rw [he, abs_neg] at h
  calc
    |weight r a x - weight r a y| =
        |max (r - dist x a) 0 - max (r - dist y a) 0| / r := by
      simp only [weight, ← sub_div, abs_div, abs_of_pos hr]
    _ ≤ |dist x a - dist y a| / r := div_le_div_of_nonneg_right h hr.le
    _ ≤ dist x y / r := div_le_div_of_nonneg_right (abs_dist_sub_le x y a) hr.le

private lemma move_injective (n : ℕ) {r : ℝ} (hr : 0 < r) (a b : Fin n → ℂ)
    (hab : ∀ i, dist (b i) (a i) ≤ r / (2 * ((n : ℝ) + 1))) :
    Function.Injective (move n r a b) := by
  intro x y hxy
  let S : ℂ → ℂ := fun z => ∑ i, weight r (a i) z • (b i - a i)
  have hden : 0 < 2 * ((n : ℝ) + 1) := by positivity
  have hterm (i : Fin n) :
      ‖weight r (a i) x • (b i - a i) - weight r (a i) y • (b i - a i)‖ ≤
        dist x y / (2 * ((n : ℝ) + 1)) := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    calc
      |weight r (a i) x - weight r (a i) y| * ‖b i - a i‖ ≤
          (dist x y / r) * (r / (2 * ((n : ℝ) + 1))) :=
        mul_le_mul (weight_dist hr (a i) x y) (by simpa [dist_eq_norm] using hab i)
          (norm_nonneg _) (div_nonneg dist_nonneg hr.le)
      _ = dist x y / (2 * ((n : ℝ) + 1)) := by field_simp [ne_of_gt hr]
  have hS : ‖S x - S y‖ ≤ dist x y / 2 := by
    calc
      ‖S x - S y‖ = ‖∑ i, (weight r (a i) x • (b i - a i) -
          weight r (a i) y • (b i - a i))‖ := by
        dsimp only [S]
        rw [← Finset.sum_sub_distrib]
      _ ≤ ∑ i : Fin n, ‖weight r (a i) x • (b i - a i) -
          weight r (a i) y • (b i - a i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, dist x y / (2 * ((n : ℝ) + 1)) :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = (n : ℝ) * (dist x y / (2 * ((n : ℝ) + 1))) := by simp
      _ ≤ ((n : ℝ) + 1) * (dist x y / (2 * ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith) (div_nonneg dist_nonneg hden.le)
      _ = dist x y / 2 := by
        have hn : (n : ℝ) + 1 ≠ 0 := by positivity
        field_simp
  have he : x - y = S y - S x := by
    change x + S x = y + S y at hxy
    linear_combination hxy
  have hdist : dist x y = ‖S x - S y‖ := by rw [dist_eq_norm, he, norm_sub_rev]
  have : dist x y = 0 := by rw [← hdist] at hS; linarith [dist_nonneg (x := x) (y := y)]
  exact dist_eq_zero.mp this

private lemma continuous_move {X : Type*} [TopologicalSpace X] (n : ℕ) (r : ℝ)
    (a b : X → Fin n → ℂ) (z : X → ℂ)
    (ha : Continuous a) (hb : Continuous b) (hz : Continuous z) :
    Continuous (fun x => move n r (a x) (b x) (z x)) := by
  unfold move weight
  fun_prop

private lemma uniform_separation {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] (n : ℕ) (f : X → OrderedConfig n) (hf : Continuous f) :
    ∃ r : ℝ, 0 < r ∧ ∀ x i j, i ≠ j → r ≤ dist ((f x).1 i) ((f x).1 j) := by
  classical
  let D : X → ℝ := fun x => ∑ i : Fin n, ∑ j : Fin n,
    if i = j then 0 else (dist ((f x).1 i) ((f x).1 j))⁻¹
  have hc (i : Fin n) : Continuous (fun x => (f x).1 i) := by
    simpa only [Function.comp_def] using
      (continuous_apply i).comp (continuous_subtype_val.comp hf)
  have hD : Continuous D := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    by_cases h : i = j
    · simp only [h, ite_true]
      exact continuous_const
    · simp only [h, ite_false]
      exact ((hc i).dist (hc j)).inv₀ (fun x =>
        ne_of_gt (dist_pos.mpr (fun he => h ((f x).2 he))))
  have hnon (x : X) : 0 ≤ D x := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs <;> positivity
  obtain ⟨x₀, _, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hD.continuousOn
  refine ⟨(D x₀ + 1)⁻¹, inv_pos.mpr (by linarith [hnon x₀]), ?_⟩
  intro x i j hij
  have hd : 0 < dist ((f x).1 i) ((f x).1 j) :=
    dist_pos.mpr (fun he => hij ((f x).2 he))
  have hsingle : (dist ((f x).1 i) ((f x).1 j))⁻¹ ≤ D x := by
    calc
      _ = (if i = j then 0 else (dist ((f x).1 i) ((f x).1 j))⁻¹) := by simp [hij]
      _ ≤ ∑ k : Fin n, if i = k then 0 else (dist ((f x).1 i) ((f x).1 k))⁻¹ := by
        apply Finset.single_le_sum (fun k _ => ?_) (Finset.mem_univ j)
        split_ifs <;> positivity
      _ ≤ D x := by
        apply Finset.single_le_sum (fun k _ => ?_) (Finset.mem_univ i)
        apply Finset.sum_nonneg
        intro l _
        split_ifs <;> positivity
  have hb : (dist ((f x).1 i) ((f x).1 j))⁻¹ ≤ D x₀ + 1 :=
    le_trans hsingle (le_trans (hmax (Set.mem_univ x)) (by linarith))
  exact (inv_le_comm₀ (by linarith [hnon x₀]) hd).mpr hb

private def clockStep (d : ℝ) (hd : 0 ≤ d) (k : ℕ) (s : I) : I :=
  ⟨min (s : ℝ) ((k : ℝ) * d),
    ⟨le_min s.2.1 (mul_nonneg (Nat.cast_nonneg k) hd), (min_le_left _ _).trans s.2.2⟩⟩

private lemma clockStep_cont (d : ℝ) (hd : 0 ≤ d) (k : ℕ) :
    Continuous (clockStep d hd k) := by unfold clockStep; fun_prop

private lemma clockStep_zero (d : ℝ) (hd : 0 ≤ d) (s : I) : clockStep d hd 0 s = 0 := by
  apply Subtype.ext
  simp [clockStep, min_eq_right s.2.1]

private lemma clockStep_at_zero (d : ℝ) (hd : 0 ≤ d) (k : ℕ) : clockStep d hd k 0 = 0 := by
  apply Subtype.ext
  simp [clockStep, min_eq_left (mul_nonneg (Nat.cast_nonneg k) hd)]

private lemma clockStep_dist (d : ℝ) (hd : 0 ≤ d) (k : ℕ) (s : I) :
    dist (clockStep d hd (k+1) s) (clockStep d hd k s) ≤ d := by
  change |min (s : ℝ) (((k + 1 : ℕ) : ℝ) * d) - min (s : ℝ) ((k : ℝ) * d)| ≤ d
  rw [Nat.cast_add, Nat.cast_one]
  rw [abs_le]
  constructor <;> (simp only [min_def]; split_ifs <;> nlinarith)

private lemma lift_last_coordinate (n : ℕ)
    (γ : Path (baseOrdered (n + 1)) (baseOrdered (n + 1)))
    (η : Path (baseOrdered n) (baseOrdered n))
    (H : ((γ.map (configForget n).continuous).cast
      (configForget_base n).symm (configForget_base n).symm).Homotopy η) :
    ∃ z : C(I × I, ℂ),
      (∀ u i, z u ≠ (H u).1 i) ∧
      (∀ t, z (0,t) = (γ t).1 (Fin.last n)) ∧
      (∀ s, z (s,0) = ((n : ℕ) + 1 : ℂ)) ∧
      (∀ s, z (s,1) = ((n : ℕ) + 1 : ℂ)) := by
  classical
  obtain ⟨r, hr, hsep⟩ := uniform_separation n H H.continuous
  have hc : Continuous (fun u : I × I => (H u).1) := continuous_subtype_val.comp H.continuous
  have heps : 0 < r / (2 * ((n : ℝ) + 1)) := by positivity
  obtain ⟨ε, hε, hUC⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hc) _ heps
  let d : ℝ := ε / 2
  have hd : 0 < d := half_pos hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / d)
  have hNd : 1 ≤ (N : ℝ) * d := by
    have := (div_lt_iff₀ hd).mp hN
    linarith
  let A : ℕ → I × I → Fin n → ℂ := fun k u => (H (clockStep d hd.le k u.1, u.2)).1
  have hA (k : ℕ) : Continuous (A k) := by
    exact continuous_subtype_val.comp (H.continuous.comp
      (((clockStep_cont d hd.le k).comp continuous_fst).prodMk continuous_snd))
  have hclose (k : ℕ) (u : I × I) (i : Fin n) :
      dist (A (k+1) u i) (A k u i) ≤ r / (2 * ((n : ℝ) + 1)) := by
    have htime : dist (clockStep d hd.le (k+1) u.1, u.2)
        (clockStep d hd.le k u.1, u.2) < ε := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact (clockStep_dist d hd.le k u.1).trans_lt (by dsimp [d]; linarith)
    exact (dist_le_pi_dist _ _ i).trans (le_of_lt (hUC htime))
  let Z : ℕ → I × I → ℂ := fun k => Nat.rec
    (fun u : I × I => (γ u.2).1 (Fin.last n))
    (fun k prev u => move n r (A k u) (A (k+1) u) (prev u)) k
  have hZ0 (u : I × I) : Z 0 u = (γ u.2).1 (Fin.last n) := rfl
  have hZsucc (k : ℕ) (u : I × I) :
      Z (k+1) u = move n r (A k u) (A (k+1) u) (Z k u) := rfl
  have hZcont (k : ℕ) : Continuous (Z k) := by
    induction k with
    | zero =>
      change Continuous (fun u : I × I => (γ u.2).1 (Fin.last n))
      simpa only [Function.comp_def] using (continuous_apply (Fin.last n)).comp
        (continuous_subtype_val.comp (γ.continuous.comp continuous_snd))
    | succ k ih => exact continuous_move n r (A k) (A (k+1)) (Z k) (hA k) (hA (k+1)) ih
  have havoid (k : ℕ) (u : I × I) : ∀ i, Z k u ≠ A k u i := by
    induction k with
    | zero =>
      intro i hi
      have ha : A 0 u i = (γ u.2).1 i.castSucc := by
        simp only [A, clockStep_zero]
        rw [H.apply_zero]
        rfl
      rw [hZ0, ha] at hi
      have he := (γ u.2).2 hi
      have := congrArg Fin.val he
      simp only [Fin.val_last, Fin.val_castSucc] at this
      exact (Nat.ne_of_gt i.isLt) this
    | succ k ih =>
      intro i hi
      have hm := move_point n hr (A k u) (A (k+1) u)
        (hsep (clockStep d hd.le k u.1, u.2)) i
      exact ih i ((move_injective n hr (A k u) (A (k+1) u) (hclose k u))
        ((hZsucc k u).symm.trans (hi.trans hm.symm)))
  have hinit (k : ℕ) (t : I) : Z k (0,t) = (γ t).1 (Fin.last n) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [hZsucc]
      have he : A (k+1) (0,t) = A k (0,t) := by simp only [A, clockStep_at_zero]
      rw [he, move_self, ih]
  have hfixed (k : ℕ) (s t : I) (ht : t = 0 ∨ t = 1) :
      Z k (s,t) = ((n : ℕ) + 1 : ℂ) := by
    induction k with
    | zero =>
      rcases ht with rfl | rfl
      · change (γ 0).1 (Fin.last n) = ((n : ℕ) + 1 : ℂ)
        rw [γ.source]
        rfl
      · change (γ 1).1 (Fin.last n) = ((n : ℕ) + 1 : ℂ)
        rw [γ.target]
        rfl
    | succ k ih =>
      have he : A (k+1) (s,t) = A k (s,t) := by
        rcases ht with rfl | rfl <;> simp [A]
      rw [hZsucc, he, move_self, ih]
  have hclock (s : I) : clockStep d hd.le N s = s := by
    apply Subtype.ext
    exact min_eq_left (s.2.2.trans hNd)
  refine ⟨⟨Z N, hZcont N⟩, ?_, hinit N, ?_, ?_⟩
  · intro u i
    change Z N u ≠ (H u).1 i
    simpa only [A, hclock, Prod.mk.eta] using havoid N u i
  · intro s; exact hfixed N s 0 (Or.inl rfl)
  · intro s; exact hfixed N s 1 (Or.inr rfl)

/-- Lift a based homotopy by finitely many small injective moves of the plane. -/
theorem solution (n : ℕ)
    (γ : Path (baseOrdered (n + 1)) (baseOrdered (n + 1)))
    (η : Path (baseOrdered n) (baseOrdered n))
    (H : ((γ.map (configForget n).continuous).cast
      (configForget_base n).symm (configForget_base n).symm).Homotopy η) :
    ∃ δ : Path (baseOrdered (n + 1)) (baseOrdered (n + 1)),
      ∃ K : γ.Homotopy δ,
        ∀ s t, configForget n (K (s, t)) = H (s, t) := by
  classical
  obtain ⟨z, hz, hz0, hzs, hzt⟩ := lift_last_coordinate n γ η H
  let F : C(I × I, OrderedConfig (n+1)) :=
    { toFun := fun u => ⟨Fin.snoc (α := fun _ => ℂ) (H u).1 (z u), by
        intro i j hij
        induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last => rfl
          | cast b =>
            simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
            exact False.elim (hz u b hij)
        | cast a =>
          induction j using Fin.lastCases with
          | last =>
            simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
            exact False.elim (hz u a hij.symm)
          | cast b =>
            simp only [Fin.snoc_castSucc] at hij
            exact congrArg Fin.castSucc ((H u).2 hij)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply continuous_pi
        intro i
        induction i using Fin.lastCases with
        | last => simpa only [Fin.snoc_last] using z.continuous
        | cast a =>
          simpa only [Fin.snoc_castSucc, Function.comp_def] using
            (continuous_apply a).comp (continuous_subtype_val.comp H.continuous) }
  have hF0 (t : I) : F (0,t) = γ t := by
    apply Subtype.ext
    funext i
    induction i using Fin.lastCases with
    | last => simpa only [F, ContinuousMap.coe_mk, Fin.snoc_last] using hz0 t
    | cast a =>
      simp only [F, ContinuousMap.coe_mk, Fin.snoc_castSucc]
      rw [H.apply_zero]
      rfl
  have hFs (s : I) : F (s,0) = baseOrdered (n+1) := by
    apply Subtype.ext
    funext i
    induction i using Fin.lastCases with
    | last => simpa [F, baseOrdered] using hzs s
    | cast a =>
      simp only [F, ContinuousMap.coe_mk, Fin.snoc_castSucc]
      rw [Path.Homotopy.source]
      rfl
  have hFt (s : I) : F (s,1) = baseOrdered (n+1) := by
    apply Subtype.ext
    funext i
    induction i using Fin.lastCases with
    | last => simpa [F, baseOrdered] using hzt s
    | cast a =>
      simp only [F, ContinuousMap.coe_mk, Fin.snoc_castSucc]
      rw [Path.Homotopy.target]
      rfl
  let δ : Path (baseOrdered (n+1)) (baseOrdered (n+1)) :=
    { toFun := fun t => F (1,t)
      continuous_toFun := F.continuous.comp (continuous_const.prodMk continuous_id)
      source' := hFs 1
      target' := hFt 1 }
  let K : γ.Homotopy δ :=
    { toContinuousMap := F
      map_zero_left := hF0
      map_one_left := fun _ => rfl
      prop' := by
        intro s t ht
        rcases ht with ht | ht
        · have : t = 0 := ht
          subst t
          simpa using hFs s
        · have : t = 1 := ht
          subst t
          simpa using hFt s }
  refine ⟨δ, K, ?_⟩
  intro s t
  apply Subtype.ext
  funext i
  exact Fin.snoc_castSucc (α := fun _ => ℂ) _ _ i
