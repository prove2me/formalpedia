-- Prove2me | solution 1 for BraidsLinksMCG.fadellNeuwirth_incl_injective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T00:02:14.326723+00:00
-- url     : https://prove2.me/submissions/f23013f2-30dd-4f17-aa1c-caef06babe60

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

open BraidsLinksMCG unitInterval
open scoped BigOperators

noncomputable section

private lemma configIncl_apply_castSucc (n : ℕ) (z : PuncturedPlane n) (j : Fin n) :
    (configIncl n z).1 j.castSucc = ((j : ℕ) + 1 : ℂ) := by
  simp [configIncl, Fin.snoc_castSucc]

private lemma configIncl_apply_last (n : ℕ) (z : PuncturedPlane n) :
    (configIncl n z).1 (Fin.last n) = z.1 := by
  simp [configIncl, Fin.snoc_last]

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

private lemma transport (m : ℕ) (H : C(I × I, OrderedConfig m))
    (h0 : ∀ t, H (0,t) = baseOrdered m)
    (hs : ∀ s, H (s,0) = baseOrdered m)
    (ht : ∀ s, H (s,1) = baseOrdered m) :
    ∃ R : ℝ, 0 < R ∧ ∃ T : I × ℂ → ℂ, Continuous T ∧
      (∀ t, Function.Injective (fun z => T (t,z))) ∧
      (∀ t i, T (t,(baseOrdered m).1 i) = (H (1,t)).1 i) ∧
      (∀ z, T (0,z) = z) ∧ (∀ z, T (1,z) = z) ∧
      (∀ t z, R ≤ ‖z‖ → T (t,z) = z) := by
  classical
  obtain ⟨r, hr, hsep⟩ := uniform_separation m H H.continuous
  have hc : Continuous (fun u : I × I => (H u).1) := continuous_subtype_val.comp H.continuous
  obtain ⟨u₀, _, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    hc.norm.continuousOn
  let B := ‖(H u₀).1‖
  let R := B + r + 1
  have hB : 0 ≤ B := norm_nonneg _
  have hbound (u : I × I) (i : Fin m) : ‖(H u).1 i‖ ≤ B :=
    (norm_le_pi_norm _ i).trans (hmax (Set.mem_univ u))
  have heps : 0 < r / (2 * ((m : ℝ) + 1)) := by positivity
  obtain ⟨ε, hε, hUC⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hc) _ heps
  let d : ℝ := ε / 2
  have hd : 0 < d := half_pos hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / d)
  have hNd : 1 ≤ (N : ℝ) * d := by
    have := (div_lt_iff₀ hd).mp hN
    linarith
  have hclock : clockStep d hd.le N 1 = 1 := by
    apply Subtype.ext
    exact min_eq_left hNd
  let A : ℕ → I → Fin m → ℂ := fun k t => (H (clockStep d hd.le k 1, t)).1
  have hA (k : ℕ) : Continuous (A k) := by
    exact continuous_subtype_val.comp (H.continuous.comp (continuous_const.prodMk continuous_id))
  have hclose (k : ℕ) (t : I) (i : Fin m) :
      dist (A (k+1) t i) (A k t i) ≤ r / (2 * ((m : ℝ) + 1)) := by
    have htime : dist (clockStep d hd.le (k+1) 1, t)
        (clockStep d hd.le k 1, t) < ε := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact (clockStep_dist d hd.le k 1).trans_lt (by dsimp [d]; linarith)
    exact (dist_le_pi_dist _ _ i).trans (le_of_lt (hUC htime))
  let Z : ℕ → I × ℂ → ℂ := fun k => Nat.rec (fun u : I × ℂ => u.2)
    (fun k prev u => move m r (A k u.1) (A (k+1) u.1) (prev u)) k
  have hZsucc (k : ℕ) (u : I × ℂ) :
      Z (k+1) u = move m r (A k u.1) (A (k+1) u.1) (Z k u) := rfl
  have hZcont (k : ℕ) : Continuous (Z k) := by
    induction k with
    | zero => exact continuous_snd
    | succ k ih =>
      exact continuous_move (X := I × ℂ) m r (A k ∘ Prod.fst)
        (A (k + 1) ∘ Prod.fst) (Z k)
        ((hA k).comp continuous_fst) ((hA (k + 1)).comp continuous_fst) ih
  have hinj (k : ℕ) (t : I) : Function.Injective (fun z => Z k (t,z)) := by
    induction k with
    | zero => exact Function.injective_id
    | succ k ih => exact (move_injective m hr (A k t) (A (k+1) t) (hclose k t)).comp ih
  have htrack (k : ℕ) (t : I) (i : Fin m) : Z k (t,(baseOrdered m).1 i) = A k t i := by
    induction k with
    | zero => simp [Z, A, clockStep_zero, h0]
    | succ k ih =>
      rw [hZsucc, ih]
      exact move_point m hr _ _ (hsep (clockStep d hd.le k 1,t)) i
  have hedge (k : ℕ) (t : I) (he : t = 0 ∨ t = 1) (z : ℂ) : Z k (t,z) = z := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hsame : A (k+1) t = A k t := by
        rcases he with rfl | rfl <;> simp [A, hs, ht]
      rw [hZsucc, hsame, move_self, ih]
  have hfar (k : ℕ) (t : I) (z : ℂ) (hz : R ≤ ‖z‖) : Z k (t,z) = z := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [hZsucc, ih]
      have hw (i : Fin m) : weight r (A k t i) z = 0 := by
        apply weight_far
        have hb := hbound (clockStep d hd.le k 1,t) i
        have hn := norm_le_norm_add_norm_sub' z (A k t i)
        dsimp only [R] at hz
        rw [dist_eq_norm]
        change ‖A k t i‖ ≤ B at hb
        linarith
      simp [move, hw]
  refine ⟨R, by dsimp [R]; linarith, Z N, hZcont N, hinj N, ?_,
    hedge N 0 (Or.inl rfl), hedge N 1 (Or.inr rfl), hfar N⟩
  intro t i
  simpa only [A, hclock] using htrack N t i

private lemma square_null {X : Type*} [TopologicalSpace X] {x y : X}
    (γ : Path x x) (q : Path x y) (F : C(I × I, X))
    (h0 : ∀ t, F (0,t) = γ t) (h1 : ∀ t, F (1,t) = y)
    (hs : ∀ s, F (s,0) = q s) (ht : ∀ s, F (s,1) = q s) :
    Path.Homotopic.Quotient.mk γ = Path.Homotopic.Quotient.refl x := by
  let p₁ : Path ((0,0) : I × I) (1,1) :=
    .prod (.trans (.refl _) .id) (.trans .id (.refl _))
  let p₂ : Path ((0,0) : I × I) (1,1) :=
    .prod (.trans .id (.refl _)) (.trans (.refl _) .id)
  let K : p₁.Homotopy p₂ :=
    Path.Homotopic.prodHomotopy (.trans (.reflTrans _) (.symm <| .transRefl _))
      (.trans (.transRefl _) (.symm <| .reflTrans _))
  have he0 : x = F (0,0) := (h0 0).trans γ.source |>.symm
  have he1 : y = F (1,1) := (h1 1).symm
  have ha : ((p₁.map F.continuous).cast he0 he1) = γ.trans q := by
    ext t
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, p₁, Path.prod_coe]
    simp only [Path.trans_apply]
    split_ifs <;> simp_all only [Path.refl_apply, Path.id_apply]
  have hb : ((p₂.map F.continuous).cast he0 he1) = q.trans (Path.refl y) := by
    ext t
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, p₂, Path.prod_coe]
    simp only [Path.trans_apply]
    split_ifs <;> simp_all only [Path.refl_apply, Path.id_apply]
  have he : Path.Homotopic.Quotient.mk (γ.trans q) =
      Path.Homotopic.Quotient.mk (q.trans (Path.refl y)) := by
    exact Path.Homotopic.Quotient.eq.mpr ⟨((K.map F).pathCast he0 he1).cast ha hb⟩
  have he' := congrArg (fun p => Path.Homotopic.Quotient.trans p
    (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk q))) he
  simpa only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_refl,
    Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_symm] using he'

/-- Fibre-inclusion injectivity from compactly supported ambient transport. -/
theorem solution (n : ℕ) :
    Function.Injective (FundamentalGroup.mapOfEq (configIncl n) (configIncl_base n)) := by
  classical
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective a
  have hm : Path.Homotopic.Quotient.mk
      ((γ.map (configIncl n).continuous).cast
        (configIncl_base n).symm (configIncl_base n).symm) =
      Path.Homotopic.Quotient.mk (Path.refl (baseOrdered (n+1))) := by
    simpa only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.mk_cast,
      Path.Homotopic.Quotient.mk_map, Path.Homotopic.Quotient.mk_refl,
      FundamentalGroup.one_def] using ha
  obtain ⟨K⟩ := Path.Homotopic.Quotient.exact hm
  let H := K.symm
  obtain ⟨R, hR, T, hTcont, hinj, htrack, hs, ht, hfar⟩ := transport (n+1) H.toContinuousMap
    (by intro t; simpa [H] using K.symm.apply_zero t)
    (by intro s; exact H.source s) (by intro s; exact H.target s)
  let L : ℝ := max R ((n : ℝ) + 1) + 1
  have hL : (n : ℝ) + 1 ≤ L := by dsimp [L]; linarith [le_max_right R ((n : ℝ)+1)]
  have hLR : R ≤ L := by dsimp [L]; linarith [le_max_left R ((n : ℝ)+1)]
  let qval : I → ℂ := fun s => ((n : ℕ) + 1 : ℂ) + (s : ℝ) * (L - ((n : ℝ)+1))
  have hq (s : I) (j : Fin n) : qval s ≠ ((j : ℕ) + 1 : ℂ) := by
    intro he
    have hre : (n : ℝ) + 1 + (s : ℝ) * (L - ((n : ℝ)+1)) = (j : ℝ) + 1 := by
      have h := congrArg Complex.re he
      simpa [qval] using h
    have hj : (j : ℝ) < n := by exact_mod_cast j.isLt
    have hnon : 0 ≤ (s : ℝ) * (L - ((n : ℝ)+1)) := mul_nonneg s.2.1 (sub_nonneg.mpr hL)
    linarith
  let q : Path (basePunctured n) (⟨(L : ℂ), by
      intro j he
      have hre := congrArg Complex.re he
      have hj : (j : ℝ) < n := by exact_mod_cast j.isLt
      simp only [Complex.ofReal_re, Complex.add_re, Complex.natCast_re, Complex.one_re] at hre
      linarith⟩ : PuncturedPlane n) :=
    { toFun := fun s => ⟨qval s, hq s⟩
      continuous_toFun := by apply Continuous.subtype_mk; dsimp [qval]; fun_prop
      source' := by apply Subtype.ext; simp [qval, basePunctured]
      target' := by apply Subtype.ext; simp [qval, push_cast] }
  have hH (t : I) : H (1,t) = (configIncl n) (γ t) := by
    rw [H.apply_one]
    rfl
  have hfix (t : I) (j : Fin n) : T (t, ((j : ℕ)+1 : ℂ)) = ((j : ℕ)+1 : ℂ) := by
    have hh := htrack t j.castSucc
    change T (t, ((j : ℕ)+1 : ℂ)) = (H (1,t)).1 j.castSucc at hh
    have hcoord : (H (1,t)).1 j.castSucc = ((j : ℕ)+1 : ℂ) := by
      rw [hH t]
      exact configIncl_apply_castSucc n (γ t) j
    exact hh.trans hcoord
  have hlast (t : I) : T (t, ((n : ℕ)+1 : ℂ)) = (γ t).1 := by
    have hh := htrack t (Fin.last n)
    change T (t, ((n : ℕ)+1 : ℂ)) = (H (1,t)).1 (Fin.last n) at hh
    have hcoord : (H (1,t)).1 (Fin.last n) = (γ t).1 := by
      rw [hH t]
      exact configIncl_apply_last n (γ t)
    exact hh.trans hcoord
  let F : C(I × I, PuncturedPlane n) :=
    { toFun := fun u => ⟨T (u.2, qval u.1), by
        intro j hj
        have he := hinj u.2 (hj.trans (hfix u.2 j).symm)
        exact hq u.1 j he⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply hTcont.comp
        apply Continuous.prodMk continuous_snd
        dsimp [qval]
        fun_prop }
  have hzero (t : I) : F (0,t) = γ t := by
    apply Subtype.ext
    simpa [F, qval] using hlast t
  have hone (t : I) : F (1,t) = q 1 := by
    apply Subtype.ext
    have hnorm : R ≤ ‖(L : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ L)]
      exact hLR
    have hv : qval 1 = (L : ℂ) := by dsimp [qval]; simp [push_cast]
    change T (t,qval 1) = qval 1
    rw [hv]
    exact hfar t _ hnorm
  have hside0 (s : I) : F (s,0) = q s := by apply Subtype.ext; exact hs _
  have hside1 (s : I) : F (s,1) = q s := by apply Subtype.ext; exact ht _
  have he := square_null γ q F hzero (by intro t; exact (hone t).trans q.target) hside0 hside1
  exact he
